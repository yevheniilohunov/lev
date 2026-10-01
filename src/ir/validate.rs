use std::collections::{HashMap, HashSet};

use crate::{
    compiler::error::CompilerError,
    semantic::symbols::{FunctionId, LocalId, StructId},
};

use super::ir::*;

pub fn validate(program: &IrProgram) -> Result<(), Vec<CompilerError>> {
    validate_with_options(program, false)
}

pub fn validate_ssa(program: &IrProgram) -> Result<(), Vec<CompilerError>> {
    validate_with_options(program, true)
}

fn validate_with_options(program: &IrProgram, require_ssa: bool) -> Result<(), Vec<CompilerError>> {
    let mut validator = Validator::new(program);

    validator.validate_program(require_ssa);

    if validator.errors.is_empty() {
        Ok(())
    } else {
        Err(validator.errors)
    }
}

struct Validator<'a> {
    program: &'a IrProgram,
    errors: Vec<CompilerError>,
}

#[derive(Debug, Clone)]
struct ValueDefinition {
    block: BlockId,
    ty: IrType,
}

impl<'a> Validator<'a> {
    fn new(program: &'a IrProgram) -> Self {
        Self {
            program,
            errors: Vec::new(),
        }
    }

    fn validate_program(&mut self, require_ssa: bool) {
        self.validate_function_ids();

        for function in &self.program.functions {
            self.validate_function(function, require_ssa);
        }
    }

    fn is_assignable(&self, actual: &IrType, expected: &IrType) -> bool {
        if actual == expected {
            return true;
        }

        let (IrType::Struct(actual_id), IrType::Struct(expected_id)) = (actual, expected) else {
            return false;
        };

        let mut current = Some(*actual_id);

        while let Some(struct_id) = current {
            if struct_id == *expected_id {
                return true;
            }

            current = self
                .program
                .structs
                .iter()
                .find(|structure| structure.id == struct_id)
                .and_then(|structure| structure.base);
        }

        false
    }

    fn validate_ssa_form(&mut self, function: &IrFunction) {
        for block in &function.blocks {
            let mut saw_non_phi = false;

            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::Phi { .. } => {
                        if saw_non_phi {
                            self.error(format!(
                            "function '{}': phi in block {} appears after a non-phi instruction",
                            function.name,
                            block.id.0
                        ));
                        }
                    }

                    IrInstruction::LoadLocal { .. } => {
                        self.error(format!(
                            "function '{}': LoadLocal remains after SSA construction in block {}",
                            function.name, block.id.0
                        ));
                        saw_non_phi = true;
                    }

                    IrInstruction::StoreLocal { .. } => {
                        self.error(format!(
                            "function '{}': StoreLocal remains after SSA construction in block {}",
                            function.name, block.id.0
                        ));
                        saw_non_phi = true;
                    }

                    _ => {
                        saw_non_phi = true;
                    }
                }
            }
        }
    }

    fn validate_phi_node(
        &mut self,
        function: &IrFunction,
        block: &BasicBlock,
        local: LocalId,
        destination: ValueId,
        sources: &[(BlockId, ValueId)],
        definitions: &HashMap<ValueId, ValueDefinition>,
    ) {
        let Some(local_ty) = self.local_type(function, local) else {
            return;
        };

        let Some(destination_def) = definitions.get(&destination) else {
            return;
        };

        if destination_def.ty != local_ty {
            self.error(format!(
                "function '{}': phi destination %{} has type {:?}, but local {} has type {:?}",
                function.name, destination.0, destination_def.ty, local.0, local_ty
            ));
        }

        for (_, value) in sources {
            let Some(value_def) = definitions.get(value) else {
                continue;
            };

            if value_def.ty != local_ty {
                self.error(format!(
                "function '{}': phi in block {} for local {} receives value %{} of type {:?}, expected {:?}",
                function.name,
                block.id.0,
                local.0,
                value.0,
                value_def.ty,
                local_ty
            ));
            }
        }
    }

    fn pe(
        &self,
        function: &IrFunction,
        instruction: &IrInstruction,
        definitions: &HashMap<ValueId, ValueDefinition>,
    ) -> Option<IrType> {
        match instruction {
            IrInstruction::Parameter { local, .. } | IrInstruction::LoadLocal { local, .. } => {
                self.local_type(function, *local)
            }

            IrInstruction::ConstInt { .. } => Some(IrType::Int),
            IrInstruction::ConstString { .. } => Some(IrType::String),
            IrInstruction::ConstBool { .. } => Some(IrType::Bool),

            IrInstruction::Copy { source, .. } => definitions .get(source) .map(|definition| definition.ty.clone()),

            IrInstruction::AllocStruct { struct_id, .. }
            | IrInstruction::StructCopy { struct_id, .. } => Some(IrType::Struct(*struct_id)),

            IrInstruction::LoadField {
                receiver, field, ..
            } => {
                let IrType::Struct(struct_id) = self.value_type(*receiver, definitions)? else {
                    return None;
                };

                self.struct_field_type(struct_id, *field)
            }

            IrInstruction::Binary {
                op, left, right, ..
            } => {
                let left_ty = self.value_type(*left, definitions)?;
                let right_ty = self.value_type(*right, definitions)?;

                match op {
                    IrBinaryOp::Add
                    | IrBinaryOp::Subtract
                    | IrBinaryOp::Multiply
                    | IrBinaryOp::Divide => {
                        if left_ty == IrType::Int && right_ty == IrType::Int {
                            Some(IrType::Int)
                        } else {
                            None
                        }
                    }

                    IrBinaryOp::Equal => {
                        if left_ty == right_ty {
                            Some(IrType::Bool)
                        } else {
                            None
                        }
                    }
                }
            }

            IrInstruction::Call {
                function: target, ..
            } => self
                .program
                .functions
                .iter()
                .find(|candidate| candidate.id == Some(*target))
                .map(|candidate| candidate.return_type.clone()),

            IrInstruction::Phi { sources, .. } => {
                let mut ty = None;

                for (_, value) in sources {
                    let source_ty = self.value_type(*value, definitions)?;

                    if let Some(existing) = &ty {
                        if *existing != source_ty {
                            return None;
                        }
                    } else {
                        ty = Some(source_ty);
                    }
                }

                ty
            }

            IrInstruction::StoreLocal { .. } | IrInstruction::StoreField { .. } => None,
            IrInstruction::StackAllocStruct { destination, struct_id } => todo!(),
        }
    }

    fn local_type(&self, function: &IrFunction, local: LocalId) -> Option<IrType> {
        function
            .parameters
            .iter()
            .chain(function.locals.iter())
            .find(|candidate| candidate.id == local)
            .map(|local| local.ty.clone())
    }

    fn value_type(
        &self,
        value: ValueId,
        definitions: &HashMap<ValueId, ValueDefinition>,
    ) -> Option<IrType> {
        definitions
            .get(&value)
            .map(|definition| definition.ty.clone())
    }

    fn struct_field_type(&self, struct_id: StructId, field: usize) -> Option<IrType> {
        self.program
            .structs
            .iter()
            .find(|structure| structure.id == struct_id)
            .and_then(|structure| structure.fields.get(field))
            .map(|field| field.ty.clone())
    }

    fn validate_instruction_uses(
        &mut self,
        function: &IrFunction,
        use_block: BlockId,
        instruction: &IrInstruction,
        definitions: &HashMap<ValueId, ValueDefinition>,
        dominance: &DominanceInfo,
        require_ssa: bool,
    ) {
        match instruction {
            IrInstruction::ConstInt { .. }
            | IrInstruction::ConstString { .. }
            | IrInstruction::ConstBool { .. }
            | IrInstruction::LoadLocal { .. }
            | IrInstruction::Parameter { .. }
            | IrInstruction::Copy { .. }
            | IrInstruction::AllocStruct { .. } => {}

            IrInstruction::StoreLocal { local, value } => {
                self.require_value(function, use_block, *value, definitions, dominance, require_ssa);

                if let Some(value_ty) = self.value_type(*value, definitions) {
                    if let Some(local_ty) = self.local_type(function, *local) {
                        self.require_type(
                            function,
                            format!("store to local {}", local.0),
                            &value_ty,
                            &local_ty,
                        );
                    }
                }
            }

            IrInstruction::Binary {
                op, left, right, ..
            } => {
                self.require_value(function, use_block, *left, definitions, dominance, require_ssa);
                self.require_value(function, use_block, *right, definitions, dominance, require_ssa);

                let left_ty = self.value_type(*left, definitions);
                let right_ty = self.value_type(*right, definitions);

                match op {
                    IrBinaryOp::Add
                    | IrBinaryOp::Subtract
                    | IrBinaryOp::Multiply
                    | IrBinaryOp::Divide => {
                        if let Some(ty) = left_ty {
                            self.require_type(function, "binary left operand", &ty, &IrType::Int);
                        }

                        if let Some(ty) = right_ty {
                            self.require_type(function, "binary right operand", &ty, &IrType::Int);
                        }
                    }

                    IrBinaryOp::Equal => {
                        if let (Some(left_ty), Some(right_ty)) = (left_ty, right_ty) {
                            if left_ty != right_ty {
                                self.error(format!(
                                "function '{}': equality operands have incompatible types: {:?} and {:?}",
                                function.name, left_ty, right_ty
                            ));
                            }
                        }
                    }
                }
            }

            IrInstruction::Call {
                function: target,
                arguments,
                destination,
            } => {
                for argument in arguments {
                    self.require_value(function, use_block, *argument, definitions, dominance, require_ssa);
                }

                let Some(target_function) = self
                    .program
                    .functions
                    .iter()
                    .find(|candidate| candidate.id == Some(*target))
                else {
                    return;
                };

                if arguments.len() != target_function.parameters.len() {
                    self.error(format!(
                        "function '{}': call to '{}' expects {} arguments but got {}",
                        function.name,
                        target_function.name,
                        target_function.parameters.len(),
                        arguments.len()
                    ));
                }

                for (index, (argument, parameter)) in arguments
                    .iter()
                    .zip(&target_function.parameters)
                    .enumerate()
                {
                    let Some(argument_ty) = self.value_type(*argument, definitions) else {
                        continue;
                    };

                    if !self.is_assignable(&argument_ty, &parameter.ty) {
                        self.error(format!(
                            "function '{}': argument {} to '{}' has type {:?}, expected {:?}",
                            function.name, index, target_function.name, argument_ty, parameter.ty
                        ));
                    }
                }

                if let Some(destination) = destination {
                    if target_function.return_type == IrType::Void {
                        self.error(format!(
                            "function '{}': call to void function '{}' has a destination",
                            function.name, target_function.name
                        ));
                    } else if let Some(destination_ty) = self.value_type(*destination, definitions)
                    {
                        if destination_ty != target_function.return_type {
                            self.error(format!(
                                "function '{}': call destination %{} has type {:?}, expected {:?}",
                                function.name,
                                destination.0,
                                destination_ty,
                                target_function.return_type
                            ));
                        }
                    }
                }
            }

            IrInstruction::Phi { sources, .. } => {
                self.validate_phi_sources(function, use_block, sources, definitions, dominance);

                let mut phi_type = None;

                for (_, value) in sources {
                    let Some(value_ty) = self.value_type(*value, definitions) else {
                        continue;
                    };

                    if let Some(existing) = &phi_type {
                        if existing != &value_ty {
                            self.error(format!(
                            "function '{}': phi in block {} has incompatible value types {:?} and {:?}",
                            function.name,
                            use_block.0,
                            existing,
                            value_ty
                        ));
                        }
                    } else {
                        phi_type = Some(value_ty);
                    }
                }
            }

            IrInstruction::LoadField {
                receiver,
                field,
                destination,
            } => {
                self.require_value(function, use_block, *receiver, definitions, dominance, require_ssa);

                let Some(receiver_ty) = self.value_type(*receiver, definitions) else {
                    return;
                };

                let IrType::Struct(struct_id) = receiver_ty else {
                    self.error(format!(
                        "function '{}': LoadField receiver %{} is not a struct",
                        function.name, receiver.0
                    ));
                    return;
                };

                let Some(field_ty) = self.struct_field_type(struct_id, *field) else {
                    self.error(format!(
                        "function '{}': LoadField references invalid field {} of struct {:?}",
                        function.name, field, struct_id
                    ));
                    return;
                };

                let Some(destination_ty) = self.value_type(*destination, definitions) else {
                    return;
                };

                if destination_ty != field_ty {
                    self.error(format!(
                        "function '{}': LoadField destination %{} has type {:?}, expected {:?}",
                        function.name, destination.0, destination_ty, field_ty
                    ));
                }
            }

            IrInstruction::StoreField {
                receiver,
                field,
                value,
            } => {
                self.require_value(function, use_block, *receiver, definitions, dominance, require_ssa);

                self.require_value(function, use_block, *value, definitions, dominance, require_ssa);

                let Some(receiver_ty) = self.value_type(*receiver, definitions) else {
                    return;
                };

                let IrType::Struct(struct_id) = receiver_ty else {
                    self.error(format!(
                        "function '{}': StoreField receiver %{} is not a struct",
                        function.name, receiver.0
                    ));
                    return;
                };

                let Some(field_ty) = self.struct_field_type(struct_id, *field) else {
                    self.error(format!(
                        "function '{}': StoreField references invalid field {} of struct {:?}",
                        function.name, field, struct_id
                    ));
                    return;
                };

                if let Some(value_ty) = self.value_type(*value, definitions) {
                    if !self.is_assignable(&value_ty, &field_ty) {
                        self.error(format!(
                            "function '{}': StoreField value has type {:?}, expected {:?}",
                            function.name, value_ty, field_ty
                        ));
                    }
                }
            }

            IrInstruction::StructCopy {
                source, struct_id, ..
            } => {
                self.require_value(function, use_block, *source, definitions, dominance, require_ssa);

                if let Some(source_ty) = self.value_type(*source, definitions) {
                    let expected = IrType::Struct(*struct_id);

                    if source_ty != expected {
                        self.error(format!(
                            "function '{}': StructCopy source has type {:?}, expected {:?}",
                            function.name, source_ty, expected
                        ));
                    }
                }
            }
            IrInstruction::StackAllocStruct { destination, struct_id } => todo!(),
        }
    }

    fn validate_function_ids(&mut self) {
        let mut ids = HashSet::new();

        for function in &self.program.functions {
            if !ids.insert(function.id) {
                self.error(format!("duplicate function id #{}", function.id.unwrap().0));
            }
        }
    }

    fn validate_function(&mut self, function: &IrFunction, require_ssa: bool) {
        self.validate_entry(function);
        self.validate_blocks(function);
        self.validate_locals(function);
        self.validate_calls(function);

        if require_ssa {
            self.validate_ssa_form(function);
        }

        if function.entry.0 < function.blocks.len() {
    let dominance = DominanceInfo::compute(function);

    self.validate_values(function, &dominance, require_ssa);

    if require_ssa {
        self.validate_dominance(function, &dominance);
    }
}
    }

    fn validate_entry(&mut self, function: &IrFunction) {
        if function.entry.0 >= function.blocks.len() {
            self.error(format!(
                "function '{}': invalid entry block {}",
                function.name, function.entry.0
            ));
        }
    }

    fn validate_blocks(&mut self, function: &IrFunction) {
        let mut ids = HashSet::new();

        for (index, block) in function.blocks.iter().enumerate() {
            if block.id.0 != index {
                self.error(format!(
                    "function '{}': block id {} does not match position {}",
                    function.name, block.id.0, index
                ));
            }

            if !ids.insert(block.id) {
                self.error(format!(
                    "function '{}': duplicate block id {}",
                    function.name, block.id.0
                ));
            }

            self.validate_terminator_targets(function, block);
        }
    }

    fn validate_terminator_targets(&mut self, function: &IrFunction, block: &BasicBlock) {
        match &block.terminator {
            Terminator::Jump(target) => {
                self.validate_block_target(function, block.id, *target);
            }

            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                self.validate_block_target(function, block.id, *then_block);

                self.validate_block_target(function, block.id, *else_block);
            }

            Terminator::Return { .. } | Terminator::Unreachable => {}
        }
    }

    fn validate_block_target(&mut self, function: &IrFunction, source: BlockId, target: BlockId) {
        if target.0 >= function.blocks.len() {
            self.error(format!(
                "function '{}': block {} references invalid block {}",
                function.name, source.0, target.0
            ));
        }
    }

    fn validate_locals(&mut self, function: &IrFunction) {
        let mut locals = HashSet::new();

        for local in &function.parameters {
            if !locals.insert(local.id) {
                self.error(format!(
                    "function '{}': duplicate local id {}",
                    function.name, local.id.0
                ));
            }
        }

        for local in &function.locals {
            if !locals.insert(local.id) {
                self.error(format!(
                    "function '{}': duplicate local id {}",
                    function.name, local.id.0
                ));
            }
        }

        for block in &function.blocks {
            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::LoadLocal { local, .. }
                    | IrInstruction::StoreLocal { local, .. }
                    | IrInstruction::Parameter { local, .. }
                    | IrInstruction::Phi { local, .. } => match !locals.contains(local) {
                        true => {
                            self.error(format!(
                                "function '{}': unknown local {}",
                                function.name, local.0
                            ));
                        }
                        false => (),
                    },

                    _ => {}
                }
            }
        }
    }

    fn validate_calls(&mut self, function: &IrFunction) {
        let functions: HashSet<FunctionId> = self
            .program
            .functions
            .iter()
            .map_while(|function| function.id)
            .collect();

        for block in &function.blocks {
            for instruction in &block.instructions {
                if let IrInstruction::Call {
                    function: target, ..
                } = instruction
                    && !functions.contains(target)
                {
                    self.error(format!(
                        "function '{}': call references unknown function #{}",
                        function.name, target.0
                    ));
                }
            }
        }
    }

    fn validate_returns(
        &mut self,
        function: &IrFunction,
        definitions: &HashMap<ValueId, ValueDefinition>,
    ) {
        for block in &function.blocks {
            let Terminator::Return { value } = &block.terminator else {
                continue;
            };

            match (&function.return_type, value) {
                (IrType::Void, Some(_)) => {
                    self.error(format!(
                        "function '{}': void function returns a value",
                        function.name
                    ));
                }

                (IrType::Void, None) => {}

                (_, None) => {
                    self.error(format!(
                        "function '{}': non-void function has empty return",
                        function.name
                    ));
                }

                (expected, Some(value)) => {
                    let Some(actual) = definitions.get(value).map(|definition| &definition.ty)
                    else {
                        continue;
                    };

                    if actual != expected {
                        self.error(format!(
                            "function '{}': return value has type {:?}, expected {:?}",
                            function.name, actual, expected
                        ));
                    }
                }
            }
        }
    }

    fn validate_values(&mut self, function: &IrFunction, dominance: &DominanceInfo, require_ssa: bool) {
        let mut definitions = HashMap::<ValueId, ValueDefinition>::new();

        // First discover every SSA value definition.
        //
        // Some instructions (notably Phi, Call, LoadField, and Binary)
        // may need definitions that are encountered later in the block
        // traversal. Repeat until no new definitions can be inferred.
        loop {
            let mut changed = false;

            for block in &function.blocks {
                if !dominance.reachable.contains(&block.id) {
                    continue;
                }

                for instruction in &block.instructions {
                    let Some(destination) = instruction_destination(instruction) else {
                        continue;
                    };

                    if definitions.contains_key(&destination) {
                        continue;
                    }

                    let Some(ty) = self.pe(function, instruction, &definitions) else {
                        continue;
                    };

                    definitions.insert(
                        destination,
                        ValueDefinition {
                            block: block.id,
                            ty,
                        },
                    );

                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        if require_ssa {
            // Check for duplicate SSA value definitions separately.
        //
        // This must not be folded into the inference loop because a
        // definition may legitimately be skipped during an early inference
        // pass and become inferable on a later pass.
        let mut seen = HashSet::<ValueId>::new();

        for block in &function.blocks {
            if !dominance.reachable.contains(&block.id) {
                continue;
            }

            for instruction in &block.instructions {
                let Some(destination) = instruction_destination(instruction) else {
                    continue;
                };

                if !seen.insert(destination) {
                    self.error(format!(
                        "function '{}': value %{} is defined more than once",
                        function.name, destination.0
                    ));
                }
            }
        }
        }

       
        // Now that all inferable definitions are known, validate every use.
        for block in &function.blocks {
            if !dominance.reachable.contains(&block.id) {
                continue;
            }

            for instruction in &block.instructions {
                self.validate_instruction_uses(
                    function,
                    block.id,
                    instruction,
                    &definitions,
                    dominance,
                    require_ssa
                );
            }

            self.validate_terminator_values(
                function,
                block.id,
                &block.terminator,
                &definitions,
                dominance,
                require_ssa
            );
        }

        for block in &function.blocks {
            if !dominance.reachable.contains(&block.id) {
                continue;
            }

            for instruction in &block.instructions {
                let IrInstruction::Phi {
                    destination,
                    local,
                    sources,
                } = instruction
                else {
                    continue;
                };

                self.validate_phi_node(
                    function,
                    block,
                    *local,
                    *destination,
                    sources,
                    &definitions,
                );
            }
        }

        for block in &function.blocks {
            if block.id != function.entry {
                for instruction in &block.instructions {
                    if let IrInstruction::Parameter { local, .. } = instruction {
                        self.error(format!(
                    "function '{}': parameter local {} is defined outside the entry block {}",
                    function.name,
                    local.0,
                    function.entry.0
                ));
                    }
                }
            }
        }

        self.validate_returns(function, &definitions);
    }

    fn validate_phi_sources(
        &mut self,
        function: &IrFunction,
        phi_block: BlockId,
        sources: &[(BlockId, ValueId)],
        definitions: &HashMap<ValueId, ValueDefinition>,
        dominance: &DominanceInfo,
    ) {
        if sources.is_empty() {
            self.error(format!(
                "function '{}': phi in block {} has no incoming values",
                function.name, phi_block.0
            ));
            return;
        }

        let predecessors = function.predecessors(phi_block);

        let mut incoming_blocks = HashSet::new();

        for (predecessor, value) in sources {
            if !predecessors.contains(predecessor) {
                self.error(
                    format!(
                        "function '{}': phi in block {} has incoming edge from non-predecessor block {}",
                        function.name,
                        phi_block.0,
                        predecessor.0
                    )
                );
            }

            if !incoming_blocks.insert(*predecessor) {
                self.error(format!(
                    "function '{}': phi in block {} has duplicate incoming block {}",
                    function.name, phi_block.0, predecessor.0
                ));
            }

            let Some(definition) = definitions.get(value) else {
                self.error(format!(
        "function '{}': phi in block {} uses value %{} from predecessor {} but that value is never defined",
        function.name,
        phi_block.0,
        value.0,
        predecessor.0
    ));
                continue;
            };

            if !dominance.dominates(definition.block, *predecessor) {
                self.error(format!(
        "function '{}': value %{} is defined in block {} but does not dominate predecessor block {} for phi in block {}",
        function.name,
        value.0,
        definition.block.0,
        predecessor.0,
        phi_block.0
    ));
            }
        }

        for predecessor in predecessors {
            if !incoming_blocks.contains(&predecessor) {
                self.error(
                    format!(
                        "function '{}': phi in block {} is missing incoming value from predecessor block {}",
                        function.name,
                        phi_block.0,
                        predecessor.0
                    )
                );
            }
        }
    }

    fn validate_terminator_values(
        &mut self,
        function: &IrFunction,
        use_block: BlockId,
        terminator: &Terminator,
        definitions: &HashMap<ValueId, ValueDefinition>,
        dominance: &DominanceInfo,
        require_ssa: bool
    ) {
        match terminator {
            Terminator::Jump(_) => {}

            Terminator::Branch { condition, .. } => {
                self.require_value(function, use_block, *condition, definitions, dominance, require_ssa);
            }

            Terminator::Return { value } => {
                if let Some(value) = value {
                    self.require_value(function, use_block, *value, definitions, dominance, require_ssa);
                }
            }

            Terminator::Unreachable => {}
        }
    }

    fn require_value(
        &mut self,
        function: &IrFunction,
        use_block: BlockId,
        value: ValueId,
        definitions: &HashMap<ValueId, ValueDefinition>,
        dominance: &DominanceInfo,
        require_ssa: bool,
    ) {
        let Some(definition) = definitions.get(&value) else {
            self.error(format!(
                "function '{}': value %{} is used but never defined",
                function.name, value.0
            ));
            return;
        };

        if require_ssa && !dominance.dominates(definition.block, use_block) {
            self.error(format!(
        "function '{}': value %{} is defined in block {} but used in block {} where the definition does not dominate the use",
        function.name,
        value.0,
        definition.block.0,
        use_block.0
    ));
        }
    }

    fn require_type(
        &mut self,
        function: &IrFunction,
        context: impl Into<String>,
        actual: &IrType,
        expected: &IrType,
    ) {
        if actual != expected {
            self.error(format!(
                "function '{}': {} has type {:?}, expected {:?}",
                function.name,
                context.into(),
                actual,
                expected
            ));
        }
    }

    fn validate_dominance(&mut self, function: &IrFunction, dominance: &DominanceInfo) {
        for block in &function.blocks {
            if !dominance.reachable.contains(&block.id) {
                continue;
            }

            let dominators = dominance
                .dominators
                .get(&block.id)
                .cloned()
                .unwrap_or_default();

            if !dominators.contains(&block.id) {
                self.error(format!(
                    "function '{}': block {} does not dominate itself",
                    function.name, block.id.0
                ));
            }

            if block.id == function.entry
                && (dominators.len() != 1 || !dominators.contains(&function.entry))
            {
                self.error(format!(
                    "function '{}': entry block has invalid dominator set",
                    function.name
                ));
            }
        }
    }

    fn error(&mut self, message: impl Into<String>) {
        self.errors.push(CompilerError::internal(message));
    }
}

fn instruction_destination(instruction: &IrInstruction) -> Option<ValueId> {
    match instruction {
        IrInstruction::ConstInt { destination, .. }
        | IrInstruction::ConstString { destination, .. }
        | IrInstruction::ConstBool { destination, .. }
        | IrInstruction::LoadLocal { destination, .. }
        | IrInstruction::Parameter { destination, .. }
        | IrInstruction::Phi { destination, .. }
        | IrInstruction::StructCopy { destination, .. }
        | IrInstruction::Copy { destination, .. }

        | IrInstruction::Binary { destination, .. } => Some(*destination),

        IrInstruction::StoreLocal { .. } => None,

        IrInstruction::Call { destination, .. } => *destination,
        IrInstruction::LoadField { destination, .. } => Some(*destination),
        IrInstruction::AllocStruct { destination, .. } => Some(*destination),
        IrInstruction::StoreField { .. } => None,
        IrInstruction::StackAllocStruct { destination, .. } => Some(*destination),
    }
}

#[derive(Debug, Clone)]
pub struct DominanceInfo {
    pub reachable: HashSet<BlockId>,

    /// All blocks that dominate each block.
    pub dominators: HashMap<BlockId, HashSet<BlockId>>,

    /// Immediate dominator for every reachable block.
    ///
    /// The entry block has `None`.
    pub immediate_dominator: HashMap<BlockId, Option<BlockId>>,

    /// Dominance frontier of each reachable block.
    pub dominance_frontier: HashMap<BlockId, HashSet<BlockId>>,
}

impl DominanceInfo {
    pub fn compute(function: &IrFunction) -> Self {
        let reachable = function.reachable_blocks();

        let dominators = compute_dominator_sets(function, &reachable);

        let immediate_dominator = compute_immediate_dominators(function, &dominators, &reachable);

        let dominance_frontier =
            compute_dominance_frontier(function, &immediate_dominator, &reachable);

        Self {
            reachable,
            dominators,
            immediate_dominator,
            dominance_frontier,
        }
    }

    pub fn dominates(&self, dominator: BlockId, block: BlockId) -> bool {
        self.dominators
            .get(&block)
            .map(|set| set.contains(&dominator))
            .unwrap_or(false)
    }

    pub fn immediate_dominator(&self, block: BlockId) -> Option<BlockId> {
        self.immediate_dominator.get(&block).copied().flatten()
    }

    pub fn dominance_frontier(&self, block: BlockId) -> Option<&HashSet<BlockId>> {
        self.dominance_frontier.get(&block)
    }
}

fn compute_dominator_sets(
    function: &IrFunction,
    reachable: &HashSet<BlockId>,
) -> HashMap<BlockId, HashSet<BlockId>> {
    let mut dominators = HashMap::new();

    for block in &function.blocks {
        if !reachable.contains(&block.id) {
            continue;
        }

        if block.id == function.entry {
            let mut set = HashSet::new();
            set.insert(function.entry);
            dominators.insert(block.id, set);
        } else {
            dominators.insert(block.id, reachable.iter().copied().collect());
        }
    }

    let mut changed = true;

    while changed {
        changed = false;

        for block in &function.blocks {
            if block.id == function.entry || !reachable.contains(&block.id) {
                continue;
            }

            let predecessors: Vec<BlockId> = function
                .predecessors(block.id)
                .into_iter()
                .filter(|pred| reachable.contains(pred))
                .collect();

            if predecessors.is_empty() {
                continue;
            }

            let mut new_set = reachable.iter().copied().collect::<HashSet<_>>();

            for predecessor in predecessors {
                if let Some(pred_doms) = dominators.get(&predecessor) {
                    new_set = new_set.intersection(pred_doms).copied().collect();
                }
            }

            new_set.insert(block.id);

            if dominators.get(&block.id) != Some(&new_set) {
                dominators.insert(block.id, new_set);
                changed = true;
            }
        }
    }

    dominators
}

fn compute_immediate_dominators(
    function: &IrFunction,
    dominators: &HashMap<BlockId, HashSet<BlockId>>,
    reachable: &HashSet<BlockId>,
) -> HashMap<BlockId, Option<BlockId>> {
    let mut result = HashMap::new();

    result.insert(function.entry, None);

    for block in &function.blocks {
        if block.id == function.entry || !reachable.contains(&block.id) {
            continue;
        }

        let Some(block_dominators) = dominators.get(&block.id) else {
            continue;
        };

        let mut strict_dominators: Vec<BlockId> = block_dominators
            .iter()
            .copied()
            .filter(|candidate| *candidate != block.id)
            .collect();

        strict_dominators
            .sort_by_key(|candidate| dominators.get(candidate).map(|set| set.len()).unwrap_or(0));

        let immediate = strict_dominators.pop();

        result.insert(block.id, immediate);
    }

    result
}

fn compute_dominance_frontier(
    function: &IrFunction,
    immediate_dominator: &HashMap<BlockId, Option<BlockId>>,
    reachable: &HashSet<BlockId>,
) -> HashMap<BlockId, HashSet<BlockId>> {
    let mut frontier = HashMap::new();

    for block in &function.blocks {
        if reachable.contains(&block.id) {
            frontier.insert(block.id, HashSet::new());
        }
    }

    for block in &function.blocks {
        if !reachable.contains(&block.id) {
            continue;
        }

        let predecessors: Vec<BlockId> = function
            .predecessors(block.id)
            .into_iter()
            .filter(|pred| reachable.contains(pred))
            .collect();

        if predecessors.len() < 2 {
            continue;
        }

        let stop = immediate_dominator.get(&block.id).copied().flatten();

        for predecessor in predecessors {
            let mut runner = predecessor;

            loop {
                if Some(runner) == stop {
                    break;
                }

                frontier.entry(runner).or_default().insert(block.id);

                let Some(next) = immediate_dominator.get(&runner).copied().flatten() else {
                    break;
                };

                runner = next;
            }
        }
    }

    frontier
}

#[cfg(test)]
mod tests {
    use super::*;

    fn local(id: usize, name: &str, ty: IrType) -> IrLocal {
        IrLocal {
            id: LocalId(id),
            name: name.to_string(),
            ty,
        }
    }

    fn block(id: usize, instructions: Vec<IrInstruction>, terminator: Terminator) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            instructions,
            terminator,
        }
    }

    fn function(
        id: usize,
        name: &str,
        parameters: Vec<IrLocal>,
        locals: Vec<IrLocal>,
        return_type: IrType,
        blocks: Vec<BasicBlock>,
    ) -> IrFunction {
        IrFunction {
            id: Some(FunctionId(id)),
            name: name.to_string(),
            owner: None,
            parameters,
            locals,
            return_type,
            entry: BlockId(0),
            blocks,
        }
    }

    fn program(functions: Vec<IrFunction>) -> IrProgram {
        IrProgram {
            structs: Vec::new(),
            functions,
        }
    }

    fn assert_error(result: Result<(), Vec<CompilerError>>, expected: &str) {
        let errors = result.expect_err("expected validation to fail");

        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "expected an error containing {:?}, got:\n{:#?}",
            expected,
            errors
        );
    }

    fn assert_valid(result: Result<(), Vec<CompilerError>>) {
        if let Err(errors) = result {
            panic!("expected valid IR, got:\n{:#?}", errors);
        }
    }

    // ---------------------------------------------------------------------
    // Basic program/function structure
    // ---------------------------------------------------------------------

    #[test]
    fn accepts_empty_program() {
        assert_valid(validate(&program(Vec::new())));
    }

    #[test]
    fn accepts_minimal_void_function() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(0, Vec::new(), Terminator::Return { value: None })],
        );

        assert_valid(validate(&program(vec![function])));
    }

    #[test]
    fn rejects_invalid_entry_block() {
        let mut function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(0, Vec::new(), Terminator::Return { value: None })],
        );

        function.entry = BlockId(10);

        assert_error(validate(&program(vec![function])), "invalid entry block 10");
    }

    #[test]
    fn rejects_duplicate_function_ids() {
        let first = function(
            0,
            "first",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(0, Vec::new(), Terminator::Return { value: None })],
        );

        let second = function(
            0,
            "second",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(0, Vec::new(), Terminator::Return { value: None })],
        );

        assert_error(
            validate(&program(vec![first, second])),
            "duplicate function id #0",
        );
    }

    #[test]
    fn rejects_block_id_that_does_not_match_position() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![
                block(0, Vec::new(), Terminator::Jump(BlockId(2))),
                block(2, Vec::new(), Terminator::Return { value: None }),
            ],
        );

        assert_error(
            validate(&program(vec![function])),
            "block id 2 does not match position 1",
        );
    }

    #[test]
    fn rejects_duplicate_block_ids() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![
                block(0, Vec::new(), Terminator::Return { value: None }),
                block(0, Vec::new(), Terminator::Return { value: None }),
            ],
        );

        assert_error(validate(&program(vec![function])), "duplicate block id 0");
    }

    #[test]
    fn rejects_invalid_jump_target() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(0, Vec::new(), Terminator::Jump(BlockId(99)))],
        );

        assert_error(
            validate(&program(vec![function])),
            "block 0 references invalid block 99",
        );
    }

    #[test]
    fn rejects_invalid_branch_targets() {
        let function = function(
            0,
            "test",
            vec![local(0, "condition", IrType::Bool)],
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![IrInstruction::Parameter {
                    destination: ValueId(0),
                    local: LocalId(0),
                }],
                Terminator::Branch {
                    condition: ValueId(0),
                    then_block: BlockId(1),
                    else_block: BlockId(99),
                },
            )],
        );

        assert_error(
            validate(&program(vec![function])),
            "block 0 references invalid block 99",
        );
    }

    // ---------------------------------------------------------------------
    // Locals
    // ---------------------------------------------------------------------

    #[test]
    fn rejects_duplicate_parameter_and_local_id() {
        let function = function(
            0,
            "test",
            vec![local(0, "x", IrType::Int)],
            vec![local(0, "y", IrType::Int)],
            IrType::Void,
            vec![block(0, Vec::new(), Terminator::Return { value: None })],
        );

        assert_error(validate(&program(vec![function])), "duplicate local id 0");
    }

    #[test]
    fn rejects_unknown_local() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![IrInstruction::LoadLocal {
                    destination: ValueId(0),
                    local: LocalId(42),
                }],
                Terminator::Return { value: None },
            )],
        );

        assert_error(validate(&program(vec![function])), "unknown local 42");
    }

    // ---------------------------------------------------------------------
    // Calls
    // ---------------------------------------------------------------------

    #[test]
    fn rejects_unknown_call_target() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![IrInstruction::Call {
                    destination: None,
                    function: FunctionId(99),
                    arguments: Vec::new(),
                }],
                Terminator::Return { value: None },
            )],
        );

        assert_error(
            validate(&program(vec![function])),
            "call references unknown function #99",
        );
    }

    #[test]
    fn rejects_wrong_call_argument_count() {
        let callee = function(
            0,
            "callee",
            vec![local(0, "x", IrType::Int), local(1, "y", IrType::Bool)],
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![
                    IrInstruction::Parameter {
                        destination: ValueId(0),
                        local: LocalId(0),
                    },
                    IrInstruction::Parameter {
                        destination: ValueId(1),
                        local: LocalId(1),
                    },
                ],
                Terminator::Return { value: None },
            )],
        );

        let caller = function(
            1,
            "caller",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 1,
                    },
                    IrInstruction::Call {
                        destination: None,
                        function: FunctionId(0),
                        arguments: vec![ValueId(0)],
                    },
                ],
                Terminator::Return { value: None },
            )],
        );

        assert_error(
            validate(&program(vec![callee, caller])),
            "call to 'callee' expects 2 arguments but got 1",
        );
    }

    #[test]
    fn rejects_wrong_call_argument_type() {
        let callee = function(
            0,
            "callee",
            vec![local(0, "x", IrType::Int)],
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![IrInstruction::Parameter {
                    destination: ValueId(0),
                    local: LocalId(0),
                }],
                Terminator::Return { value: None },
            )],
        );

        let caller = function(
            1,
            "caller",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstBool {
                        destination: ValueId(0),
                        value: true,
                    },
                    IrInstruction::Call {
                        destination: None,
                        function: FunctionId(0),
                        arguments: vec![ValueId(0)],
                    },
                ],
                Terminator::Return { value: None },
            )],
        );

        assert_error(
            validate(&program(vec![callee, caller])),
            "argument 0 to 'callee' has type Bool, expected Int",
        );
    }

    #[test]
    fn accepts_inheritance_assignability_for_call_arguments() {
        let base = IrStruct {
            id: StructId(0),
            name: "Base".to_string(),
            base: None,
            fields: Vec::new(),
        };

        let derived = IrStruct {
            id: StructId(1),
            name: "Derived".to_string(),
            base: Some(StructId(0)),
            fields: Vec::new(),
        };

        let callee = function(
            0,
            "accept_base",
            vec![local(0, "value", IrType::Struct(StructId(0)))],
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![IrInstruction::Parameter {
                    destination: ValueId(0),
                    local: LocalId(0),
                }],
                Terminator::Return { value: None },
            )],
        );

        let caller = function(
            1,
            "caller",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![
                    IrInstruction::AllocStruct {
                        destination: ValueId(0),
                        struct_id: StructId(1),
                    },
                    IrInstruction::Call {
                        destination: None,
                        function: FunctionId(0),
                        arguments: vec![ValueId(0)],
                    },
                ],
                Terminator::Return { value: None },
            )],
        );

        let mut program = program(vec![callee, caller]);
        program.structs = vec![base, derived];

        assert_valid(validate(&program));
    }

    #[test]
    fn rejects_destination_for_void_call() {
        let callee = function(
            0,
            "callee",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(0, Vec::new(), Terminator::Return { value: None })],
        );

        let caller = function(
            1,
            "caller",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![IrInstruction::Call {
                    destination: Some(ValueId(0)),
                    function: FunctionId(0),
                    arguments: Vec::new(),
                }],
                Terminator::Return { value: None },
            )],
        );

        assert_error(
            validate(&program(vec![callee, caller])),
            "call to void function 'callee' has a destination",
        );
    }

    // ---------------------------------------------------------------------
    // Returns
    // ---------------------------------------------------------------------

    #[test]
    fn rejects_value_return_from_void_function() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![IrInstruction::ConstInt {
                    destination: ValueId(0),
                    value: 42,
                }],
                Terminator::Return {
                    value: Some(ValueId(0)),
                },
            )],
        );

        assert_error(
            validate(&program(vec![function])),
            "void function returns a value",
        );
    }

    #[test]
    fn rejects_empty_return_from_non_void_function() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(0, Vec::new(), Terminator::Return { value: None })],
        );

        assert_error(
            validate(&program(vec![function])),
            "non-void function has empty return",
        );
    }

    #[test]
    fn rejects_wrong_return_type() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(
                0,
                vec![IrInstruction::ConstBool {
                    destination: ValueId(0),
                    value: true,
                }],
                Terminator::Return {
                    value: Some(ValueId(0)),
                },
            )],
        );

        assert_error(
            validate(&program(vec![function])),
            "return value has type Bool, expected Int",
        );
    }

    // ---------------------------------------------------------------------
    // Values / definitions / dominance
    // ---------------------------------------------------------------------

    #[test]
    fn rejects_undefined_value_use() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(
                0,
                Vec::new(),
                Terminator::Return {
                    value: Some(ValueId(99)),
                },
            )],
        );

        assert_error(
            validate(&program(vec![function])),
            "value %99 is used but never defined",
        );
    }

    #[test]
    fn rejects_duplicate_value_definition() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 1,
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 2,
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(0)),
                },
            )],
        );

        assert_error(
            validate_ssa(&program(vec![function])),
            "value %0 is defined more than once",
        );
    }

    #[test]
    fn rejects_value_used_before_dominating_block() {
        let function = function(
            0,
            "test",
            vec![local(0, "condition", IrType::Bool)],
            Vec::new(),
            IrType::Int,
            vec![
                block(
                    0,
                    vec![IrInstruction::Parameter {
                        destination: ValueId(0),
                        local: LocalId(0),
                    }],
                    Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                ),
                block(
                    1,
                    vec![IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 42,
                    }],
                    Terminator::Jump(BlockId(3)),
                ),
                block(2, Vec::new(), Terminator::Jump(BlockId(3))),
                block(
                    3,
                    Vec::new(),
                    Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                ),
            ],
        );

        assert_error(
            validate_ssa(&program(vec![function])),
            "does not dominate the use",
        );
    }

    // ---------------------------------------------------------------------
    // Binary instructions
    // ---------------------------------------------------------------------

    #[test]
    fn accepts_integer_arithmetic() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 1,
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 2,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Add,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(2)),
                },
            )],
        );

        assert_valid(validate(&program(vec![function])));
    }

    #[test]
    fn rejects_non_integer_arithmetic() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstBool {
                        destination: ValueId(0),
                        value: true,
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 2,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Add,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(2)),
                },
            )],
        );

        assert_error(
            validate(&program(vec![function])),
            "binary left operand has type Bool, expected Int",
        );
    }

    #[test]
    fn rejects_equality_with_incompatible_types() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Bool,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 1,
                    },
                    IrInstruction::ConstBool {
                        destination: ValueId(1),
                        value: true,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Equal,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(2)),
                },
            )],
        );

        assert_error(
            validate(&program(vec![function])),
            "equality operands have incompatible types",
        );
    }

    // ---------------------------------------------------------------------
    // Struct fields
    // ---------------------------------------------------------------------

    #[test]
    fn accepts_valid_field_load_and_store() {
        let structure = IrStruct {
            id: StructId(0),
            name: "Point".to_string(),
            base: None,
            fields: vec![IrField {
                name: "x".to_string(),
                ty: IrType::Int,
            }],
        };

        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::AllocStruct {
                        destination: ValueId(0),
                        struct_id: StructId(0),
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 10,
                    },
                    IrInstruction::StoreField {
                        receiver: ValueId(0),
                        field: 0,
                        value: ValueId(1),
                    },
                    IrInstruction::LoadField {
                        destination: ValueId(2),
                        receiver: ValueId(0),
                        field: 0,
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(2)),
                },
            )],
        );

        let mut program = program(vec![function]);
        program.structs.push(structure);

        assert_valid(validate(&program));
    }

    #[test]
    fn rejects_load_field_from_non_struct() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 1,
                    },
                    IrInstruction::LoadField {
                        destination: ValueId(1),
                        receiver: ValueId(0),
                        field: 0,
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(1)),
                },
            )],
        );

        assert_error(
            validate(&program(vec![function])),
            "LoadField receiver %0 is not a struct",
        );
    }

    #[test]
    fn rejects_invalid_load_field_index() {
        let structure = IrStruct {
            id: StructId(0),
            name: "Point".to_string(),
            base: None,
            fields: vec![],
        };

        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::AllocStruct {
                        destination: ValueId(0),
                        struct_id: StructId(0),
                    },
                    IrInstruction::LoadField {
                        destination: ValueId(1),
                        receiver: ValueId(0),
                        field: 5,
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(1)),
                },
            )],
        );

        let mut program = program(vec![function]);
        program.structs.push(structure);

        assert_error(validate(&program), "LoadField references invalid field 5");
    }

    #[test]
    fn rejects_store_field_type_mismatch() {
        let structure = IrStruct {
            id: StructId(0),
            name: "Point".to_string(),
            base: None,
            fields: vec![IrField {
                name: "x".to_string(),
                ty: IrType::Int,
            }],
        };

        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![block(
                0,
                vec![
                    IrInstruction::AllocStruct {
                        destination: ValueId(0),
                        struct_id: StructId(0),
                    },
                    IrInstruction::ConstBool {
                        destination: ValueId(1),
                        value: true,
                    },
                    IrInstruction::StoreField {
                        receiver: ValueId(0),
                        field: 0,
                        value: ValueId(1),
                    },
                ],
                Terminator::Return { value: None },
            )],
        );

        let mut program = program(vec![function]);
        program.structs.push(structure);

        assert_error(
            validate(&program),
            "StoreField value has type Bool, expected Int",
        );
    }

    // ---------------------------------------------------------------------
    // StructCopy
    // ---------------------------------------------------------------------

    #[test]
    fn rejects_struct_copy_type_mismatch() {
        let first = IrStruct {
            id: StructId(0),
            name: "A".to_string(),
            base: None,
            fields: Vec::new(),
        };

        let second = IrStruct {
            id: StructId(1),
            name: "B".to_string(),
            base: None,
            fields: Vec::new(),
        };

        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Struct(StructId(1)),
            vec![block(
                0,
                vec![
                    IrInstruction::AllocStruct {
                        destination: ValueId(0),
                        struct_id: StructId(0),
                    },
                    IrInstruction::StructCopy {
                        destination: ValueId(1),
                        source: ValueId(0),
                        struct_id: StructId(1),
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(1)),
                },
            )],
        );

        let mut program = program(vec![function]);
        program.structs = vec![first, second];

        assert_error(
            validate(&program),
            "StructCopy source has type Struct(StructId(0)), expected Struct(StructId(1))",
        );
    }

    // ---------------------------------------------------------------------
    // SSA form
    // ---------------------------------------------------------------------

    #[test]
    fn validate_ssa_accepts_phi_before_normal_instructions() {
        let function = function(
            0,
            "test",
            vec![local(0, "condition", IrType::Bool)],
            vec![local(1, "x", IrType::Int)],
            IrType::Int,
            vec![
                block(
                    0,
                    vec![
                        IrInstruction::Parameter {
                            destination: ValueId(0),
                            local: LocalId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 10,
                        },
                    ],
                    Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                ),
                block(
                    1,
                    vec![IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 20,
                    }],
                    Terminator::Jump(BlockId(3)),
                ),
                block(
                    2,
                    vec![IrInstruction::ConstInt {
                        destination: ValueId(3),
                        value: 30,
                    }],
                    Terminator::Jump(BlockId(3)),
                ),
                block(
                    3,
                    vec![IrInstruction::Phi {
                        destination: ValueId(4),
                        local: LocalId(1),
                        sources: vec![(BlockId(1), ValueId(2)), (BlockId(2), ValueId(3))],
                    }],
                    Terminator::Return {
                        value: Some(ValueId(4)),
                    },
                ),
            ],
        );

        assert_valid(validate_ssa(&program(vec![function])));
    }

    #[test]
    fn validate_ssa_rejects_phi_after_non_phi() {
        let function = function(
            0,
            "test",
            Vec::new(),
            vec![local(0, "x", IrType::Int)],
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 1,
                    },
                    IrInstruction::Phi {
                        destination: ValueId(1),
                        local: LocalId(0),
                        sources: vec![(BlockId(0), ValueId(0))],
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(1)),
                },
            )],
        );

        assert_error(
            validate_ssa(&program(vec![function])),
            "phi in block 0 appears after a non-phi instruction",
        );
    }

    #[test]
    fn validate_ssa_rejects_load_local() {
        let function = function(
            0,
            "test",
            Vec::new(),
            vec![local(0, "x", IrType::Int)],
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 1,
                    },
                    IrInstruction::LoadLocal {
                        destination: ValueId(1),
                        local: LocalId(0),
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(0)),
                },
            )],
        );

        assert_error(
            validate_ssa(&program(vec![function])),
            "LoadLocal remains after SSA construction",
        );
    }

    #[test]
    fn validate_ssa_rejects_store_local() {
        let function = function(
            0,
            "test",
            Vec::new(),
            vec![local(0, "x", IrType::Int)],
            IrType::Void,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 1,
                    },
                    IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(0),
                    },
                ],
                Terminator::Return { value: None },
            )],
        );

        assert_error(
            validate_ssa(&program(vec![function])),
            "StoreLocal remains after SSA construction",
        );
    }

    #[test]
    fn validate_ssa_rejects_parameter_outside_entry() {
        let function = function(
            0,
            "test",
            vec![local(0, "x", IrType::Int)],
            Vec::new(),
            IrType::Void,
            vec![
                block(0, Vec::new(), Terminator::Jump(BlockId(1))),
                block(
                    1,
                    vec![IrInstruction::Parameter {
                        destination: ValueId(0),
                        local: LocalId(0),
                    }],
                    Terminator::Return { value: None },
                ),
            ],
        );

        assert_error(
            validate_ssa(&program(vec![function])),
            "parameter local 0 is defined outside the entry block 0",
        );
    }

    // ---------------------------------------------------------------------
    // Phi validation
    // ---------------------------------------------------------------------

    fn branching_function_with_phi(sources: Vec<(BlockId, ValueId)>) -> IrFunction {
        function(
            0,
            "test",
            vec![local(0, "condition", IrType::Bool)],
            vec![local(1, "x", IrType::Int)],
            IrType::Int,
            vec![
                block(
                    0,
                    vec![
                        IrInstruction::Parameter {
                            destination: ValueId(0),
                            local: LocalId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 0,
                        },
                    ],
                    Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                ),
                block(
                    1,
                    vec![IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 1,
                    }],
                    Terminator::Jump(BlockId(3)),
                ),
                block(
                    2,
                    vec![IrInstruction::ConstInt {
                        destination: ValueId(3),
                        value: 2,
                    }],
                    Terminator::Jump(BlockId(3)),
                ),
                block(
                    3,
                    vec![IrInstruction::Phi {
                        destination: ValueId(4),
                        local: LocalId(1),
                        sources,
                    }],
                    Terminator::Return {
                        value: Some(ValueId(4)),
                    },
                ),
            ],
        )
    }

    #[test]
    fn validate_ssa_accepts_complete_phi() {
        let function =
            branching_function_with_phi(vec![(BlockId(1), ValueId(2)), (BlockId(2), ValueId(3))]);

        assert_valid(validate_ssa(&program(vec![function])));
    }

    #[test]
    fn validate_ssa_rejects_empty_phi() {
        let function = branching_function_with_phi(Vec::new());

        assert_error(
            validate_ssa(&program(vec![function])),
            "phi in block 3 has no incoming values",
        );
    }

    #[test]
    fn validate_ssa_rejects_phi_from_non_predecessor() {
        let function =
            branching_function_with_phi(vec![(BlockId(1), ValueId(2)), (BlockId(99), ValueId(3))]);

        assert_error(
            validate_ssa(&program(vec![function])),
            "incoming edge from non-predecessor block 99",
        );
    }

    #[test]
    fn validate_ssa_rejects_duplicate_phi_predecessor() {
        let function =
            branching_function_with_phi(vec![(BlockId(1), ValueId(2)), (BlockId(1), ValueId(2))]);

        assert_error(
            validate_ssa(&program(vec![function])),
            "duplicate incoming block 1",
        );
    }

    #[test]
    fn validate_ssa_rejects_missing_phi_predecessor() {
        let function = branching_function_with_phi(vec![(BlockId(1), ValueId(2))]);

        assert_error(
            validate_ssa(&program(vec![function])),
            "missing incoming value from predecessor block 2",
        );
    }

    #[test]
    fn validate_ssa_rejects_undefined_phi_value() {
        let function =
            branching_function_with_phi(vec![(BlockId(1), ValueId(99)), (BlockId(2), ValueId(3))]);

        assert_error(
            validate_ssa(&program(vec![function])),
            "phi in block 3 uses value %99 from predecessor 1 but that value is never defined",
        );
    }

    #[test]
    fn validate_ssa_rejects_phi_value_that_does_not_dominate_predecessor() {
        let function =
            branching_function_with_phi(vec![(BlockId(1), ValueId(3)), (BlockId(2), ValueId(2))]);

        assert_error(
            validate_ssa(&program(vec![function])),
            "does not dominate predecessor block",
        );
    }

    #[test]
    fn validate_ssa_rejects_phi_type_mismatch() {
        let mut function =
            branching_function_with_phi(vec![(BlockId(1), ValueId(2)), (BlockId(2), ValueId(3))]);

        function.blocks[2].instructions[0] = IrInstruction::ConstBool {
            destination: ValueId(3),
            value: true,
        };

        assert_error(
            validate_ssa(&program(vec![function])),
            "phi in block 3 has incompatible value types",
        );
    }

    #[test]
    fn validate_ssa_rejects_phi_destination_type_mismatch() {
        let mut function =
            branching_function_with_phi(vec![(BlockId(1), ValueId(2)), (BlockId(2), ValueId(3))]);

        function.locals[0].ty = IrType::Bool;

        assert_error(
            validate_ssa(&program(vec![function])),
            "phi destination %4 has type Int, but local 1 has type Bool",
        );
    }

    // ---------------------------------------------------------------------
    // Dominance
    // ---------------------------------------------------------------------

    #[test]
    fn computes_linear_dominators() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![
                block(0, Vec::new(), Terminator::Jump(BlockId(1))),
                block(1, Vec::new(), Terminator::Jump(BlockId(2))),
                block(2, Vec::new(), Terminator::Return { value: None }),
            ],
        );

        let dominance = DominanceInfo::compute(&function);

        assert_eq!(dominance.immediate_dominator(BlockId(0)), None);
        assert_eq!(dominance.immediate_dominator(BlockId(1)), Some(BlockId(0)));
        assert_eq!(dominance.immediate_dominator(BlockId(2)), Some(BlockId(1)));

        assert!(dominance.dominates(BlockId(0), BlockId(2)));
        assert!(dominance.dominates(BlockId(1), BlockId(2)));
        assert!(dominance.dominates(BlockId(2), BlockId(2)));
    }

    #[test]
    fn computes_branch_join_dominance() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![
                block(
                    0,
                    Vec::new(),
                    Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                ),
                block(1, Vec::new(), Terminator::Jump(BlockId(3))),
                block(2, Vec::new(), Terminator::Jump(BlockId(3))),
                block(3, Vec::new(), Terminator::Return { value: None }),
            ],
        );

        let dominance = DominanceInfo::compute(&function);

        assert!(dominance.dominates(BlockId(0), BlockId(1)));
        assert!(dominance.dominates(BlockId(0), BlockId(2)));
        assert!(dominance.dominates(BlockId(0), BlockId(3)));

        assert!(!dominance.dominates(BlockId(1), BlockId(3)));
        assert!(!dominance.dominates(BlockId(2), BlockId(3)));

        assert_eq!(dominance.immediate_dominator(BlockId(3)), Some(BlockId(0)));
    }

    #[test]
    fn computes_loop_dominance_frontier() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![
                block(0, Vec::new(), Terminator::Jump(BlockId(1))),
                block(
                    1,
                    Vec::new(),
                    Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(2),
                        else_block: BlockId(3),
                    },
                ),
                block(2, Vec::new(), Terminator::Jump(BlockId(1))),
                block(3, Vec::new(), Terminator::Return { value: None }),
            ],
        );

        let dominance = DominanceInfo::compute(&function);

        assert_eq!(dominance.immediate_dominator(BlockId(1)), Some(BlockId(0)));
        assert_eq!(dominance.immediate_dominator(BlockId(2)), Some(BlockId(1)));
        assert_eq!(dominance.immediate_dominator(BlockId(3)), Some(BlockId(1)));

        assert!(
            dominance
                .dominance_frontier(BlockId(2))
                .is_some_and(|frontier| frontier.contains(&BlockId(1)))
        );
    }

    #[test]
    fn ignores_unreachable_blocks_in_dominance() {
        let function = function(
            0,
            "test",
            Vec::new(),
            Vec::new(),
            IrType::Void,
            vec![
                block(0, Vec::new(), Terminator::Return { value: None }),
                block(1, Vec::new(), Terminator::Return { value: None }),
            ],
        );

        let dominance = DominanceInfo::compute(&function);

        assert!(dominance.reachable.contains(&BlockId(0)));
        assert!(!dominance.reachable.contains(&BlockId(1)));

        assert!(!dominance.dominates(BlockId(0), BlockId(1)));
    }

    // ---------------------------------------------------------------------
    // SSA vs non-SSA validation
    // ---------------------------------------------------------------------

    #[test]
    fn regular_validation_allows_load_and_store_local() {
        let function = function(
            0,
            "test",
            Vec::new(),
            vec![local(0, "x", IrType::Int)],
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 42,
                    },
                    IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(0),
                    },
                    IrInstruction::LoadLocal {
                        destination: ValueId(1),
                        local: LocalId(0),
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(1)),
                },
            )],
        );

        assert_valid(validate(&program(vec![function])));
    }

    #[test]
    fn ssa_validation_rejects_load_and_store_local() {
        let function = function(
            0,
            "test",
            Vec::new(),
            vec![local(0, "x", IrType::Int)],
            IrType::Int,
            vec![block(
                0,
                vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 42,
                    },
                    IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(0),
                    },
                    IrInstruction::LoadLocal {
                        destination: ValueId(1),
                        local: LocalId(0),
                    },
                ],
                Terminator::Return {
                    value: Some(ValueId(1)),
                },
            )],
        );

        let result = validate_ssa(&program(vec![function]));
        let errors = result.expect_err("expected SSA validation to fail");

        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("StoreLocal remains")),
            "missing StoreLocal diagnostic: {errors:#?}"
        );

        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("LoadLocal remains")),
            "missing LoadLocal diagnostic: {errors:#?}"
        );
    }
}

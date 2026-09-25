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
            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::LoadLocal { .. } => {
                        self.error(format!(
                            "function '{}': LoadLocal remains after SSA construction in block {}",
                            function.name, block.id.0
                        ));
                    }

                    IrInstruction::StoreLocal { .. } => {
                        self.error(format!(
                            "function '{}': StoreLocal remains after SSA construction in block {}",
                            function.name, block.id.0
                        ));
                    }

                    _ => {}
                }
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
    ) {
        match instruction {
            IrInstruction::ConstInt { .. }
            | IrInstruction::ConstString { .. }
            | IrInstruction::ConstBool { .. }
            | IrInstruction::LoadLocal { .. }
            | IrInstruction::Parameter { .. }
            | IrInstruction::AllocStruct { .. } => {}

            IrInstruction::StoreLocal { local, value } => {
                self.require_value(function, use_block, *value, definitions, dominance);

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
                self.require_value(function, use_block, *left, definitions, dominance);
                self.require_value(function, use_block, *right, definitions, dominance);

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
                    self.require_value(function, use_block, *argument, definitions, dominance);
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
                self.require_value(function, use_block, *receiver, definitions, dominance);

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
                self.require_value(function, use_block, *receiver, definitions, dominance);

                self.require_value(function, use_block, *value, definitions, dominance);

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
                self.require_value(function, use_block, *source, definitions, dominance);

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
            self.validate_values(function, &dominance);
            self.validate_dominance(function, &dominance);
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

    fn validate_values(&mut self, function: &IrFunction, dominance: &DominanceInfo) {
        let mut definitions = HashMap::<ValueId, ValueDefinition>::new();

        for block in &function.blocks {
            if !dominance.reachable.contains(&block.id) {
                continue;
            }

            for instruction in &block.instructions {
                if let Some(destination) = instruction_destination(instruction) {
                    let Some(ty) = self.pe(function, instruction, &definitions) else {
                        continue;
                    };

                    if definitions
                        .insert(
                            destination,
                            ValueDefinition {
                                block: block.id,
                                ty,
                            },
                        )
                        .is_some()
                    {
                        self.error(format!(
                            "function '{}': value %{} is defined more than once",
                            function.name, destination.0
                        ));
                    }
                }
            }
        }

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
                );
            }

            self.validate_terminator_values(
                function,
                block.id,
                &block.terminator,
                &definitions,
                dominance,
            );
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
    ) {
        match terminator {
            Terminator::Jump(_) => {}

            Terminator::Branch { condition, .. } => {
                self.require_value(function, use_block, *condition, definitions, dominance);
            }

            Terminator::Return { value } => {
                if let Some(value) = value {
                    self.require_value(function, use_block, *value, definitions, dominance);
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
    ) {
        let Some(definition) = definitions.get(&value) else {
            self.error(format!(
                "function '{}': value %{} is used but never defined",
                function.name, value.0
            ));
            return;
        };

        if !dominance.dominates(definition.block, use_block) {
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
        | IrInstruction::Binary { destination, .. } => Some(*destination),

        IrInstruction::StoreLocal { .. } => None,

        IrInstruction::Call { destination, .. } => *destination,
        IrInstruction::LoadField { destination, .. } => Some(*destination),
        IrInstruction::AllocStruct { destination, .. } => Some(*destination),
        IrInstruction::StoreField { .. } => None,
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

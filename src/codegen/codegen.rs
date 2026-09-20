use std::collections::{ BTreeMap, HashMap, HashSet };
use std::fmt::Write;

use crate::compiler::error::CompilerError;

use crate::ir::ir::{
    BasicBlock,
    BlockId,
    IrBinaryOp,
    IrFunction,
    IrInstruction,
    IrProgram,
    Terminator,
    ValueId,
};
use crate::semantic::symbols::FunctionId;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodegenTarget {
    X86_64,
    X86_64MacOS,
}

pub fn generate(program: &IrProgram, target: CodegenTarget) -> Result<String, Vec<CompilerError>> {
    let mut output = String::new();

    writeln!(output, ".intel_syntax noprefix").map_err(|error|
        vec![CompilerError::internal(error.to_string())]
    )?;
    writeln!(output, ".text").map_err(|error| vec![CompilerError::internal(error.to_string())])?;

    let string_labels = collect_string_literals(program);

    let function_names: HashMap<_, _> = program.functions
        .iter()
        .map(|function| { (function.id, FunctionCodegen::function_symbol_name(program, function)) })
        .collect();

    emit_string_section(&mut output, &string_labels, target)?;

    for function in &program.functions {
        generate_function(&mut output, program, function, &function_names, &string_labels, target)?;
    }

    Ok(output)
}

fn collect_string_literals(program: &IrProgram) -> BTreeMap<String, String> {
    let mut labels = BTreeMap::new();

    for function in &program.functions {
        for block in &function.blocks {
            for instruction in &block.instructions {
                let IrInstruction::ConstString { value, .. } = instruction else {
                    continue;
                };

                if !labels.contains_key(value) {
                    let label = format!(".L_string_{}", labels.len());
                    labels.insert(value.clone(), label);
                }
            }
        }
    }

    labels
}

fn emit_string_section(
    output: &mut String,
    string_labels: &BTreeMap<String, String>,
    target: CodegenTarget
) -> Result<(), Vec<CompilerError>> {
    if string_labels.is_empty() {
        return Ok(());
    }

    match target {
        CodegenTarget::X86_64 => {
            writeln!(output, ".section .rodata").map_err(|error|
                vec![CompilerError::internal(error.to_string())]
            )?;
        }

        CodegenTarget::X86_64MacOS => {
            writeln!(output, ".section __TEXT,__cstring").map_err(|error|
                vec![CompilerError::internal(error.to_string())]
            )?;
        }
    }

    for (value, label) in string_labels {
        writeln!(output, "{}:", label).map_err(|error|
            vec![CompilerError::internal(error.to_string())]
        )?;

        writeln!(output, "    .asciz \"{}\"", escape_assembly_string(value)).map_err(|error|
            vec![CompilerError::internal(error.to_string())]
        )?;
    }

    Ok(())
}

fn escape_assembly_string(value: &str) -> String {
    let mut result = String::new();

    for character in value.chars() {
        match character {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            character if character.is_ascii_graphic() || character == ' ' => {
                result.push(character);
            }
            character => {
                for byte in character.to_string().as_bytes() {
                    result.push_str(&format!("\\{:03o}", byte));
                }
            }
        }
    }

    result
}

struct FunctionCodegen<'a> {
    output: &'a mut String,
    program: &'a IrProgram,
    function: &'a IrFunction,
    value_slots: HashMap<ValueId, i32>,
    edge_copies: HashMap<BlockId, Vec<(ValueId, ValueId)>>,
    struct_storage: HashMap<ValueId, i32>,
    function_names: &'a HashMap<FunctionId, String>,
    next_stack_offset: i32,
    target: CodegenTarget,
    phi_temp_offset: i32,
    string_labels: &'a BTreeMap<String, String>,
}

impl<'a> FunctionCodegen<'a> {
    fn new(
        output: &'a mut String,
        program: &'a IrProgram,
        function: &'a IrFunction,
        function_names: &'a HashMap<FunctionId, String>,
        string_labels: &'a BTreeMap<String, String>,
        target: CodegenTarget
    ) -> Self {
        Self {
            output,
            program,
            function,
            value_slots: HashMap::new(),
            edge_copies: HashMap::new(),
            struct_storage: HashMap::new(),
            function_names,
            next_stack_offset: 8,
            phi_temp_offset: 0,
            target,
            string_labels,
        }
    }

    fn block_label(&self, block: BlockId) -> String {
        let function_name = Self::function_symbol_name(self.program, self.function);
        let symbol = self.symbol_name(&function_name);
        format!(".L{}_{}", symbol, block.0)
    }

    fn allocate_struct_storage(&mut self) {
        for block in &self.function.blocks {
            for instruction in &block.instructions {
                let (destination, struct_id) = match instruction {
                    IrInstruction::AllocStruct { destination, struct_id } =>
                        (*destination, *struct_id),

                    IrInstruction::StructCopy { destination, struct_id, .. } =>
                        (*destination, *struct_id),

                    _ => {
                        continue;
                    }
                };

                let Some(structure) = self.program.structs
                    .iter()
                    .find(|structure| structure.id == struct_id) else {
                    continue;
                };

                let size = (structure.fields.len() as i32) * 8;

                self.struct_storage.insert(destination, self.next_stack_offset);

                self.next_stack_offset += size;
            }
        }
    }

    fn function_symbol_name(program: &IrProgram, function: &IrFunction) -> String {
        match function.owner {
            Some(owner) => {
                let struct_name = program.structs
                    .iter()
                    .find(|structure| structure.id == owner)
                    .map(|structure| structure.name.as_str())
                    .unwrap_or("unknown");

                format!("{}_{}", struct_name, function.name)
            }

            None => function.name.clone(),
        }
    }

    fn symbol_name(&self, name: &str) -> String {
        match self.target {
            CodegenTarget::X86_64 => name.to_string(),
            CodegenTarget::X86_64MacOS => format!("_{}", name),
        }
    }

    fn generate(mut self) -> Result<(), Vec<CompilerError>> {
        self.collect_phi_copies();
        self.allocate_value_slots();
        self.allocate_struct_storage();

        // Reserve one additional stack slot for cycle-breaking phi copies.
        self.phi_temp_offset = self.next_stack_offset;
        self.next_stack_offset += 8;

        let function_name = Self::function_symbol_name(self.program, self.function);
        let symbol = self.symbol_name(&function_name);

        writeln!(self.output, ".globl {}", symbol).map_err(|error|
            vec![CompilerError::internal(error.to_string())]
        )?;

        writeln!(self.output, "{}:", symbol).map_err(|error|
            vec![CompilerError::internal(error.to_string())]
        )?;

        self.emit_prologue()?;

        for block in &self.function.blocks {
            self.emit_block(block)?;
        }

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Phi elimination
    // ---------------------------------------------------------------------

    fn collect_phi_copies(&mut self) {
        for block in &self.function.blocks {
            for instruction in &block.instructions {
                let IrInstruction::Phi { destination, sources, .. } = instruction else {
                    continue;
                };

                for &(predecessor, source_value) in sources {
                    self.edge_copies
                        .entry(predecessor)
                        .or_default()
                        .push((source_value, *destination));
                }
            }
        }
    }

    fn emit_edge_copies(&mut self, predecessor: BlockId) -> Result<(), Vec<CompilerError>> {
        let Some(copies) = self.edge_copies.get(&predecessor).cloned() else {
            return Ok(());
        };

        self.emit_parallel_copies(&copies)
    }

    /// Emit a set of copies that conceptually happen simultaneously.
    ///
    /// Example:
    ///
    ///     a <- b
    ///     b <- a
    ///
    /// Cannot safely be emitted as:
    ///
    ///     mov a, b
    ///     mov b, a
    ///
    /// because the original value of `a` would be lost.
    ///
    /// We therefore use the temporary stack slot:
    ///
    ///     temp <- a
    ///     a <- b
    ///     b <- temp
    fn emit_parallel_copies(
        &mut self,
        copies: &[(ValueId, ValueId)]
    ) -> Result<(), Vec<CompilerError>> {
        let mut pending: Vec<(ValueId, ValueId)> = copies.to_vec();

        while !pending.is_empty() {
            let mut progress = false;

            // First emit copies whose destination is not used as a source
            // by another pending copy.
            let sources: HashSet<ValueId> = pending
                .iter()
                .map(|(source, _)| *source)
                .collect();

            let mut index = 0;

            while index < pending.len() {
                let (source, destination) = pending[index];

                if source == destination {
                    pending.remove(index);
                    progress = true;
                    continue;
                }

                if !sources.contains(&destination) {
                    self.emit_load(source, "rax")?;
                    self.emit_store(destination, "rax")?;

                    pending.remove(index);
                    progress = true;
                } else {
                    index += 1;
                }
            }

            if progress {
                continue;
            }

            // No safe copy was found, so there is a cycle.
            //
            // Break the cycle by saving one source value in the temporary
            // stack slot.
            let (source, destination) = pending[0];

            self.emit_load(source, "rax")?;

            writeln!(self.output, "    mov [rbp-{}], rax", self.phi_temp_offset).map_err(|e|
                vec![CompilerError::internal(e.to_string())]
            )?;

            // Replace the source of this copy with a special temporary
            // representation by removing it and carrying the destination
            // forward.
            pending.remove(0);

            let mut current_destination = destination;

            loop {
                let next_index = pending.iter().position(|(_, destination)| *destination == source);

                let Some(next_index) = next_index else {
                    break;
                };

                let (next_source, next_destination) = pending.remove(next_index);

                self.emit_load(next_source, "rax")?;
                self.emit_store(current_destination, "rax")?;

                current_destination = next_destination;

                if next_source == source {
                    break;
                }
            }

            // Restore the original value from the temporary slot.
            writeln!(self.output, "    mov rax, [rbp-{}]", self.phi_temp_offset).map_err(|e|
                vec![CompilerError::internal(e.to_string())]
            )?;

            self.emit_store(current_destination, "rax")?;
        }

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Stack allocation
    // ---------------------------------------------------------------------

    fn allocate_value_slots(&mut self) {
        for block in &self.function.blocks {
            for instruction in &block.instructions {
                if let Some(value) = instruction_destination(instruction) {
                    self.allocate_value(value);
                }
            }
        }
    }

    fn allocate_value(&mut self, value: ValueId) {
        if self.value_slots.contains_key(&value) {
            return;
        }

        self.value_slots.insert(value, self.next_stack_offset);
        self.next_stack_offset += 8;
    }

    fn stack_size(&self) -> i32 {
        let required = self.next_stack_offset - 8;

        if required <= 0 {
            return 0;
        }

        // Keep the stack 16-byte aligned.
        ((required + 15) / 16) * 16
    }

    fn emit_prologue(&mut self) -> Result<(), Vec<CompilerError>> {
        writeln!(self.output, "    push rbp").map_err(|error|
            vec![CompilerError::internal(error.to_string())]
        )?;

        writeln!(self.output, "    mov rbp, rsp").map_err(|error|
            vec![CompilerError::internal(error.to_string())]
        )?;

        let stack_size = self.stack_size();

        if stack_size > 0 {
            writeln!(self.output, "    sub rsp, {}", stack_size).map_err(|error|
                vec![CompilerError::internal(error.to_string())]
            )?;
        }

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Blocks
    // ---------------------------------------------------------------------

    fn emit_block(&mut self, block: &BasicBlock) -> Result<(), Vec<CompilerError>> {
        writeln!(self.output, "{}:", self.block_label(block.id)).map_err(|error|
            vec![CompilerError::internal(error.to_string())]
        )?;

        for instruction in &block.instructions {
            // Phi instructions have already been converted into edge copies.
            if matches!(instruction, IrInstruction::Phi { .. }) {
                continue;
            }

            self.emit_instruction(instruction)?;
        }

        // Phi copies belong to the predecessor edge, so they must happen
        // after ordinary instructions in this block but before its
        // terminator transfers control.
        self.emit_edge_copies(block.id)?;

        self.emit_terminator(&block.terminator)?;

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Instructions
    // ---------------------------------------------------------------------

    fn argument_register(index: usize) -> Option<&'static str> {
        match index {
            0 => Some("rdi"),
            1 => Some("rsi"),
            2 => Some("rdx"),
            3 => Some("rcx"),
            4 => Some("r8"),
            5 => Some("r9"),
            _ => None,
        }
    }

    fn emit_instruction(&mut self, instruction: &IrInstruction) -> Result<(), Vec<CompilerError>> {
        match instruction {
            IrInstruction::Parameter { destination, local } => {
                let symbol = self.symbol_name(&self.function.name);
                let parameter_index = self.function.parameters
                    .iter()
                    .position(|parameter| parameter.id == *local)
                    .ok_or_else(|| {
                        vec![
                            CompilerError::internal(
                                format!(
                                    "could not find parameter local {:?} in function '{}'",
                                    local,
                                    symbol
                                )
                            )
                        ]
                    })?;

                let register = Self::argument_register(parameter_index).ok_or_else(|| {
                    vec![
                        CompilerError::internal(
                            format!("more than six integer parameters are not supported yet")
                        )
                    ]
                })?;

                writeln!(self.output, "    mov rax, {}", register).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                self.emit_store(*destination, "rax")?;
            }

            IrInstruction::ConstInt { destination, value } => {
                self.emit_load_immediate("rax", *value)?;
                self.emit_store(*destination, "rax")?;
            }

            IrInstruction::ConstString { destination, value } => {
                let label = self.string_labels
                    .get(value)
                    .ok_or_else(|| {
                        vec![
                            CompilerError::internal(
                                format!("no assembly label found for string literal {:?}", value)
                            )
                        ]
                    })?;

                writeln!(self.output, "    lea rax, [rip + {}]", label).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                self.emit_store(*destination, "rax")?;
            }

            IrInstruction::ConstBool { destination, value } => {
                let value = if *value { 1 } else { 0 };

                writeln!(self.output, "    mov rax, {}", value).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                self.emit_store(*destination, "rax")?;
            }

            IrInstruction::LoadLocal { destination, local: _ } => {
                return Err(
                    vec![
                        CompilerError::internal(
                            format!(
                                "LoadLocal should have been removed by SSA construction: {:?}",
                                destination
                            )
                        )
                    ]
                );
            }

            IrInstruction::StoreLocal { local, value } => {
                return Err(
                    vec![
                        CompilerError::internal(
                            format!(
                                "StoreLocal should have been removed by SSA construction: local {:?}, value {:?}",
                                local,
                                value
                            )
                        )
                    ]
                );
            }

            IrInstruction::Binary { destination, op, left, right } => {
                self.emit_load(*left, "rax")?;
                self.emit_load(*right, "rcx")?;

                match op {
                    IrBinaryOp::Add => {
                        writeln!(self.output, "    add rax, rcx").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;
                    }

                    IrBinaryOp::Subtract => {
                        writeln!(self.output, "    sub rax, rcx").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;
                    }

                    IrBinaryOp::Multiply => {
                        writeln!(self.output, "    imul rax, rcx").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;
                    }

                    IrBinaryOp::Divide => {
                        writeln!(self.output, "    cqo").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;

                        writeln!(self.output, "    idiv rcx").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;
                    }

                    IrBinaryOp::Equal => {
                        writeln!(self.output, "    cmp rax, rcx").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;

                        writeln!(self.output, "    sete al").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;

                        writeln!(self.output, "    movzx rax, al").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;
                    }
                }

                self.emit_store(*destination, "rax")?;
            }

            IrInstruction::Call { destination, function, arguments } => {
                if arguments.len() > 6 {
                    return Err(
                        vec![
                            CompilerError::internal(
                                format!(
                                    "function call has {} arguments, but only 6 integer arguments are currently supported",
                                    arguments.len()
                                )
                            )
                        ]
                    );
                }

                let function_name = self.function_names
                    .get(function)
                    .ok_or_else(|| {
                        vec![CompilerError::internal(format!("unknown function id {:?}", function))]
                    })?;

                for (index, argument) in arguments.iter().enumerate() {
                    let register = Self::argument_register(index).ok_or_else(|| {
                        vec![
                            CompilerError::internal(
                                format!("no argument register available for argument {}", index)
                            )
                        ]
                    })?;

                    self.emit_load_value(*argument, register)?;
                }

                let symbol = self.symbol_name(function_name);

                writeln!(self.output, "    call {}", symbol).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                if let Some(destination) = destination {
                    self.emit_store_value(*destination, "rax")?;
                }
            }

            IrInstruction::Phi { .. } => {
                // Phi nodes are handled by emit_edge_copies().
            }

            IrInstruction::LoadField { destination, receiver, field } => {
                let offset = (*field as i32) * 8;

                self.emit_load(*receiver, "rax")?;

                if offset == 0 {
                    writeln!(self.output, "    mov rax, [rax]").map_err(|e|
                        vec![CompilerError::internal(e.to_string())]
                    )?;
                } else {
                    writeln!(self.output, "    mov rax, [rax+{}]", offset).map_err(|e|
                        vec![CompilerError::internal(e.to_string())]
                    )?;
                }

                self.emit_store(*destination, "rax")?;
            }
            IrInstruction::AllocStruct { destination, struct_id } => {
                let offset = self.struct_storage
                    .get(destination)
                    .ok_or_else(|| {
                        vec![
                            CompilerError::internal(
                                format!(
                                    "no stack storage allocated for struct value {:?}",
                                    destination
                                )
                            )
                        ]
                    })?;

                let _structure = self.program.structs
                    .iter()
                    .find(|structure| structure.id == *struct_id)
                    .ok_or_else(|| {
                        vec![CompilerError::internal(format!("unknown struct id {:?}", struct_id))]
                    })?;

                writeln!(self.output, "    lea rax, [rbp-{}]", offset).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                self.emit_store(*destination, "rax")?;
            }
            IrInstruction::StoreField { receiver, field, value } => {
                let offset = (*field as i32) * 8;

                self.emit_load(*receiver, "rax")?;
                self.emit_load(*value, "rcx")?;

                if offset == 0 {
                    writeln!(self.output, "    mov [rax], rcx").map_err(|e|
                        vec![CompilerError::internal(e.to_string())]
                    )?;
                } else {
                    writeln!(self.output, "    mov [rax+{}], rcx", offset).map_err(|e|
                        vec![CompilerError::internal(e.to_string())]
                    )?;
                }
            }
            IrInstruction::StructCopy { destination, source, struct_id } => {
                let destination_offset = self.struct_storage
                    .get(destination)
                    .copied()
                    .ok_or_else(|| {
                        vec![
                            CompilerError::internal(
                                format!(
                                    "no stack storage allocated for struct copy destination {:?}",
                                    destination
                                )
                            )
                        ]
                    })?;

                let structure = self.program.structs
                    .iter()
                    .find(|structure| structure.id == *struct_id)
                    .ok_or_else(|| {
                        vec![CompilerError::internal(format!("unknown struct id {:?}", struct_id))]
                    })?;

                self.emit_load(*source, "rax")?;

                writeln!(self.output, "    lea rdx, [rbp-{}]", destination_offset).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                for field_index in 0..structure.fields.len() {
                    let offset = (field_index as i32) * 8;

                    if offset == 0 {
                        writeln!(self.output, "    mov rcx, [rax]").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;

                        writeln!(self.output, "    mov [rdx], rcx").map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;
                    } else {
                        writeln!(self.output, "    mov rcx, [rax+{}]", offset).map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;

                        writeln!(self.output, "    mov [rdx+{}], rcx", offset).map_err(|e|
                            vec![CompilerError::internal(e.to_string())]
                        )?;
                    }
                }

                self.emit_store(*destination, "rdx")?;
            }
        }

        Ok(())
    }

    fn emit_load_value(
        &mut self,
        value: ValueId,
        register: &str
    ) -> Result<(), Vec<CompilerError>> {
        let offset = self.value_slots
            .get(&value)
            .ok_or_else(|| {
                vec![
                    CompilerError::internal(
                        format!("no stack slot allocated for SSA value {:?}", value)
                    )
                ]
            })?;

        writeln!(self.output, "    mov {}, [rbp-{}]", register, offset).map_err(|e|
            vec![CompilerError::internal(e.to_string())]
        )?;

        Ok(())
    }

    fn emit_store_value(
        &mut self,
        value: ValueId,
        register: &str
    ) -> Result<(), Vec<CompilerError>> {
        let offset = self.value_slots
            .get(&value)
            .ok_or_else(|| {
                vec![
                    CompilerError::internal(
                        format!("no stack slot allocated for SSA value {:?}", value)
                    )
                ]
            })?;

        writeln!(self.output, "    mov [rbp-{}], {}", offset, register).map_err(|e|
            vec![CompilerError::internal(e.to_string())]
        )?;

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Terminators
    // ---------------------------------------------------------------------

    fn emit_terminator(&mut self, terminator: &Terminator) -> Result<(), Vec<CompilerError>> {
        match terminator {
            Terminator::Jump(block) => {
                writeln!(self.output, "    jmp {}", self.block_label(*block)).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;
            }

            Terminator::Branch { condition, then_block, else_block } => {
                self.emit_load(*condition, "rax")?;

                writeln!(self.output, "    cmp rax, 0").map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                writeln!(self.output, "    jne {}", self.block_label(*then_block)).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                writeln!(self.output, "    jmp {}", self.block_label(*else_block)).map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;
            }

            Terminator::Return { value } => {
                if let Some(value) = value {
                    self.emit_load(*value, "rax")?;
                }

                writeln!(self.output, "    leave").map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;

                writeln!(self.output, "    ret").map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;
            }

            Terminator::Unreachable => {
                writeln!(self.output, "    ud2").map_err(|e|
                    vec![CompilerError::internal(e.to_string())]
                )?;
            }
        }

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Values
    // ---------------------------------------------------------------------

    fn emit_load(&mut self, value: ValueId, register: &str) -> Result<(), Vec<CompilerError>> {
        let offset = self.value_slots
            .get(&value)
            .ok_or_else(|| {
                vec![
                    CompilerError::internal(
                        format!("no stack slot allocated for SSA value {:?}", value)
                    )
                ]
            })?;

        writeln!(self.output, "    mov {}, [rbp-{}]", register, offset).map_err(|e|
            vec![CompilerError::internal(e.to_string())]
        )?;

        Ok(())
    }

    fn emit_store(&mut self, value: ValueId, register: &str) -> Result<(), Vec<CompilerError>> {
        let offset = self.value_slots
            .get(&value)
            .ok_or_else(|| {
                vec![
                    CompilerError::internal(
                        format!("no stack slot allocated for SSA value {:?}", value)
                    )
                ]
            })?;

        writeln!(self.output, "    mov [rbp-{}], {}", offset, register).map_err(|e|
            vec![CompilerError::internal(e.to_string())]
        )?;

        Ok(())
    }

    fn emit_load_immediate(
        &mut self,
        register: &str,
        value: i64
    ) -> Result<(), Vec<CompilerError>> {
        writeln!(self.output, "    mov {}, {}", register, value).map_err(|e|
            vec![CompilerError::internal(e.to_string())]
        )?;

        Ok(())
    }

    // fn block_label(&self, block: BlockId) -> String {
    //     let symbol = self.symbol_name(&self.function.name);

    //     format!(".L{}_{}", symbol, block.0)
    // }
}

// -------------------------------------------------------------------------
// Helpers
// -------------------------------------------------------------------------

fn instruction_destination(instruction: &IrInstruction) -> Option<ValueId> {
    match instruction {
        IrInstruction::Parameter { destination, .. } => { Some(*destination) }

        IrInstruction::ConstInt { destination, .. } => { Some(*destination) }

        IrInstruction::ConstString { destination, .. } => { Some(*destination) }

        IrInstruction::ConstBool { destination, .. } => { Some(*destination) }

        IrInstruction::LoadLocal { destination, .. } => { Some(*destination) }

        IrInstruction::StoreLocal { .. } => None,

        IrInstruction::Binary { destination, .. } => { Some(*destination) }

        IrInstruction::Call { destination, .. } => { *destination }

        IrInstruction::Phi { destination, .. } => { Some(*destination) }

        IrInstruction::LoadField { destination, .. } => { Some(*destination) }

        IrInstruction::AllocStruct { destination, .. } => { Some(*destination) }

        IrInstruction::StructCopy { destination, .. } => { Some(*destination) }

        IrInstruction::StoreField { .. } => None,
    }
}

fn generate_function(
    output: &mut String,
    program: &IrProgram,
    function: &IrFunction,
    function_names: &HashMap<FunctionId, String>,
    string_labels: &BTreeMap<String, String>,
    target: CodegenTarget
) -> Result<(), Vec<CompilerError>> {
    FunctionCodegen::new(
        output,
        program,
        function,
        function_names,
        string_labels,
        target
    ).generate()
}

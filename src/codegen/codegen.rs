use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write;

use crate::compiler::error::CompilerError;

use crate::ir::ir::{
    BasicBlock, BlockId, IrBinaryOp, IrFunction, IrInstruction, IrProgram, Terminator, ValueId,
};
use crate::semantic::symbols::FunctionId;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodegenTarget {
    X86_64,
    X86_64MacOS,
    Aarch64MacOS,
}

impl Default for CodegenTarget {
    fn default() -> Self {
        CodegenTarget::X86_64
    }
}

impl CodegenTarget {
    fn malloc_symbol(self) -> &'static str {
        match self {
            CodegenTarget::X86_64MacOS => "_malloc",
            CodegenTarget::X86_64 => "malloc",
            CodegenTarget::Aarch64MacOS => "_malloc",
        }
    }

    pub fn native() -> Self {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            return CodegenTarget::Aarch64MacOS;
        }

        #[cfg(all(target_os = "macos", target_arch = "x86_64"))]
        {
            return CodegenTarget::X86_64MacOS;
        }

        #[cfg(target_arch = "x86_64")]
        {
            return CodegenTarget::X86_64;
        }

        panic!("unsupported host architecture");
    }

    fn argument_register(self, index: usize) -> Option<&'static str> {
        match self {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => match index {
                0 => Some("rdi"),
                1 => Some("rsi"),
                2 => Some("rdx"),
                3 => Some("rcx"),
                4 => Some("r8"),
                5 => Some("r9"),
                _ => None,
            },

            CodegenTarget::Aarch64MacOS => match index {
                0 => Some("x0"),
                1 => Some("x1"),
                2 => Some("x2"),
                3 => Some("x3"),
                4 => Some("x4"),
                5 => Some("x5"),
                6 => Some("x6"),
                7 => Some("x7"),
                _ => None,
            },
        }
    }

    fn return_register(self) -> &'static str {
        match self {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => "rax",
            CodegenTarget::Aarch64MacOS => "x0",
        }
    }
}

pub fn generate(program: &IrProgram, target: CodegenTarget) -> Result<String, Vec<CompilerError>> {
    let mut output = String::new();

    match target {
        CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
            writeln!(output, ".intel_syntax noprefix")
                .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
        }

        CodegenTarget::Aarch64MacOS => {}
    }

    writeln!(output, ".text").map_err(|error| vec![CompilerError::internal(error.to_string())])?;

    let string_labels = collect_string_literals(program);

    let function_names: HashMap<_, _> = program
        .functions
        .iter()
        .map(|function| {
            (
                function.id,
                FunctionCodegen::function_symbol_name(program, function),
            )
        })
        .collect();

    emit_string_section(&mut output, &string_labels, target)?;

    for function in &program.functions {
        generate_function(
            &mut output,
            program,
            function,
            &function_names,
            &string_labels,
            target,
        )?;
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
    target: CodegenTarget,
) -> Result<(), Vec<CompilerError>> {
    if string_labels.is_empty() {
        return Ok(());
    }

    match target {
        CodegenTarget::X86_64 => {
            writeln!(output, ".section .rodata")
                .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
        }

        CodegenTarget::X86_64MacOS => {
            writeln!(output, ".section __TEXT,__cstring")
                .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
        }
        CodegenTarget::Aarch64MacOS => {
            writeln!(output, ".section __TEXT,__cstring")
                .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
        }
    }

    for (value, label) in string_labels {
        writeln!(output, "{}:", label)
            .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

        writeln!(output, "    .asciz \"{}\"", escape_assembly_string(value))
            .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
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
    edge_copies: HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>>,
    struct_storage: HashMap<ValueId, i32>,
    function_names: &'a HashMap<Option<FunctionId>, String>,
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
        function_names: &'a HashMap<Option<FunctionId>, String>,
        string_labels: &'a BTreeMap<String, String>,
        target: CodegenTarget,
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
                    IrInstruction::StackAllocStruct {
                        destination,
                        struct_id,
                    } => (*destination, *struct_id),

                    IrInstruction::StructCopy {
                        destination,
                        struct_id,
                        ..
                    } => (*destination, *struct_id),

                    _ => {
                        continue;
                    }
                };

                let Some(structure) = self
                    .program
                    .structs
                    .iter()
                    .find(|structure| structure.id == struct_id)
                else {
                    continue;
                };

                let size = (structure.fields.len() as i32) * 8;

                self.struct_storage
                    .insert(destination, self.next_stack_offset);

                self.next_stack_offset += size;
            }
        }
    }

    fn function_symbol_name(program: &IrProgram, function: &IrFunction) -> String {
        match function.owner {
            Some(owner) => {
                let struct_name = program
                    .structs
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
            CodegenTarget::Aarch64MacOS => format!("_{}", name),
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

        writeln!(self.output, ".globl {}", symbol)
            .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

        writeln!(self.output, "{}:", symbol)
            .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

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
                let IrInstruction::Phi {
                    destination,
                    sources,
                    ..
                } = instruction
                else {
                    continue;
                };

                for &(predecessor, source_value) in sources {
                    self.edge_copies
                        .entry((predecessor, block.id))
                        .or_default()
                        .push((source_value, *destination));
                }
            }
        }
    }

    fn emit_edge_copies(
        &mut self,
        predecessor: BlockId,
        successor: BlockId,
    ) -> Result<(), Vec<CompilerError>> {
        let Some(copies) = self.edge_copies.get(&(predecessor, successor)).cloned() else {
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
        copies: &[(ValueId, ValueId)],
    ) -> Result<(), Vec<CompilerError>> {
        let mut pending = copies.to_vec();
        let temporary_register = match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => "rax",
            CodegenTarget::Aarch64MacOS => "x16",
        };

        while !pending.is_empty() {
            let sources: HashSet<ValueId> = pending.iter().map(|(source, _)| *source).collect();

            let mut progress = false;
            let mut index = 0;

            while index < pending.len() {
                let (source, destination) = pending[index];

                if source == destination {
                    pending.remove(index);
                    progress = true;
                    continue;
                }

                // Safe when the destination is not needed as a source
                // by any remaining copy.
                if !sources.contains(&destination) {
                    self.emit_load(source, temporary_register)?;
                    self.emit_store(destination, temporary_register)?;

                    pending.remove(index);
                    progress = true;
                } else {
                    index += 1;
                }
            }

            if progress {
                continue;
            }

            // We have a cycle.
            //
            // Example:
            //
            //     a <- b
            //     b <- a
            //
            // Save `a`, then perform:
            //
            //     a <- b
            //     b <- temp
            //
            // For longer cycles the same backwards traversal works.
            let (source, _) = pending[0];

            self.emit_load(source, temporary_register)?;
            self.emit_phi_temp_store(temporary_register)?;

            // Remove the copy whose source we saved.
            let first_index = pending
                .iter()
                .position(|(candidate_source, _)| *candidate_source == source)
                .expect("cycle source must exist");

            pending.remove(first_index);

            let mut current_destination = source;

            loop {
                let Some(index) = pending
                    .iter()
                    .position(|(_, destination)| *destination == current_destination)
                else {
                    break;
                };

                let (next_source, _) = pending.remove(index);

                self.emit_load(next_source, temporary_register)?;
                self.emit_store(current_destination, temporary_register)?;

                current_destination = next_source;
            }

            // Complete the cycle with the saved original value.
            self.emit_phi_temp_load(temporary_register)?;
            self.emit_store(current_destination, temporary_register)?;
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

        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                // `push rbp` leaves rsp 8 bytes off a 16-byte boundary.
                // Make the frame size 8 mod 16 so rsp is 16-byte aligned
                // before any outgoing call.
                ((required + 23) / 16) * 16 + 8
            }

            CodegenTarget::Aarch64MacOS => {
                // The ARM64 prologue already pushes x29/x30 in a 16-byte
                // aligned pair, so the local frame itself must be a
                // multiple of 16.
                ((required + 15) / 16) * 16
            }
        }
    }

    fn emit_prologue(&mut self) -> Result<(), Vec<CompilerError>> {
        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(self.output, "    push rbp")
                    .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

                writeln!(self.output, "    mov rbp, rsp")
                    .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

                let stack_size = self.stack_size();

                if stack_size > 0 {
                    writeln!(self.output, "    sub rsp, {}", stack_size)
                        .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
                }
            }

            CodegenTarget::Aarch64MacOS => {
                writeln!(self.output, "    stp x29, x30, [sp, #-16]!")
                    .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

                writeln!(self.output, "    mov x29, sp")
                    .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

                let stack_size = self.stack_size();

                if stack_size > 0 {
                    writeln!(self.output, "    sub sp, sp, #{}", stack_size)
                        .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
                }
            }
        }

        Ok(())
    }

    fn emit_epilogue(&mut self) -> Result<(), Vec<CompilerError>> {
        let stack_size = self.stack_size();

        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(self.output, "    leave")
                    .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

                writeln!(self.output, "    ret")
                    .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
            }

            CodegenTarget::Aarch64MacOS => {
                if stack_size > 0 {
                    writeln!(self.output, "    add sp, sp, #{}", stack_size)
                        .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
                }

                writeln!(self.output, "    ldp x29, x30, [sp], #16")
                    .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

                writeln!(self.output, "    ret")
                    .map_err(|error| vec![CompilerError::internal(error.to_string())])?;
            }
        }

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Blocks
    // ---------------------------------------------------------------------

    fn emit_block(&mut self, block: &BasicBlock) -> Result<(), Vec<CompilerError>> {
        writeln!(self.output, "{}:", self.block_label(block.id))
            .map_err(|error| vec![CompilerError::internal(error.to_string())])?;

        for instruction in &block.instructions {
            // Phi instructions have already been converted into edge copies.
            if matches!(instruction, IrInstruction::Phi { .. }) {
                continue;
            }

            self.emit_instruction(instruction)?;
        }

        self.emit_terminator(block.id, &block.terminator)?;

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Instructions
    // ---------------------------------------------------------------------

    fn emit_instruction(&mut self, instruction: &IrInstruction) -> Result<(), Vec<CompilerError>> {
        match instruction {
            IrInstruction::Parameter { destination, local } => {
                let symbol = self.symbol_name(&self.function.name);
                let parameter_index = self
                    .function
                    .parameters
                    .iter()
                    .position(|parameter| parameter.id == *local)
                    .ok_or_else(|| {
                        vec![CompilerError::internal(format!(
                            "could not find parameter local {:?} in function '{}'",
                            local, symbol
                        ))]
                    })?;

                let register = self
                    .target
                    .argument_register(parameter_index)
                    .ok_or_else(|| {
                        vec![CompilerError::internal(format!(
                            "more than six integer parameters are not supported yet"
                        ))]
                    })?;

                let temporary_register = match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => "rax",
                    CodegenTarget::Aarch64MacOS => "x16",
                };

                writeln!(self.output, "    mov {}, {}", temporary_register, register)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                self.emit_store(*destination, temporary_register)?;
            }

            IrInstruction::ConstInt { destination, value } => {
                let temporary_register = match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => "rax",
                    CodegenTarget::Aarch64MacOS => "x16",
                };

                self.emit_load_immediate(temporary_register, *value)?;
                self.emit_store(*destination, temporary_register)?;
            }

            IrInstruction::ConstString { destination, value } => {
                let label = self.string_labels.get(value).ok_or_else(|| {
                    vec![CompilerError::internal(format!(
                        "no assembly label found for string literal {:?}",
                        value
                    ))]
                })?;

                match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                        writeln!(self.output, "    lea rax, [rip + {}]", label)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                        self.emit_store(*destination, "rax")?;
                    }

                    CodegenTarget::Aarch64MacOS => {
                        writeln!(self.output, "    adrp x16, {}", label)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                        writeln!(self.output, "    add x16, x16, :lo12:{}", label)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                        self.emit_store(*destination, "x16")?;
                    }
                }
            }

            IrInstruction::ConstBool { destination, value } => {
                let value = if *value { 1 } else { 0 };

                let temporary_register = match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => "rax",
                    CodegenTarget::Aarch64MacOS => "x16",
                };

                self.emit_load_immediate(temporary_register, value)?;
                self.emit_store(*destination, temporary_register)?;
            }

            IrInstruction::LoadLocal {
                destination,
                local: _,
            } => {
                return Err(vec![CompilerError::internal(format!(
                    "LoadLocal should have been removed by SSA construction: {:?}",
                    destination
                ))]);
            }

            IrInstruction::StoreLocal { local, value } => {
                return Err(vec![CompilerError::internal(format!(
                    "StoreLocal should have been removed by SSA construction: local {:?}, value {:?}",
                    local, value
                ))]);
            }

            IrInstruction::Binary {
                destination,
                op,
                left,
                right,
            } => match self.target {
                CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                    self.emit_load(*left, "rax")?;
                    self.emit_load(*right, "rcx")?;

                    match op {
                        IrBinaryOp::Add => {
                            writeln!(self.output, "    add rax, rcx")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        IrBinaryOp::Subtract => {
                            writeln!(self.output, "    sub rax, rcx")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        IrBinaryOp::Multiply => {
                            writeln!(self.output, "    imul rax, rcx")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        IrBinaryOp::Divide => {
                            writeln!(self.output, "    cqo")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                            writeln!(self.output, "    idiv rcx")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        IrBinaryOp::Equal => {
                            writeln!(self.output, "    cmp rax, rcx")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                            writeln!(self.output, "    sete al")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                            writeln!(self.output, "    movzx rax, al")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }
                    }

                    self.emit_store(*destination, "rax")?;
                }

                CodegenTarget::Aarch64MacOS => {
                    self.emit_load(*left, "x16")?;
                    self.emit_load(*right, "x17")?;

                    match op {
                        IrBinaryOp::Add => {
                            writeln!(self.output, "    add x16, x16, x17")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        IrBinaryOp::Subtract => {
                            writeln!(self.output, "    sub x16, x16, x17")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        IrBinaryOp::Multiply => {
                            writeln!(self.output, "    mul x16, x16, x17")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        IrBinaryOp::Divide => {
                            writeln!(self.output, "    sdiv x16, x16, x17")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        IrBinaryOp::Equal => {
                            writeln!(self.output, "    cmp x16, x17")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                            writeln!(self.output, "    cset x16, eq")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }
                    }

                    self.emit_store(*destination, "x16")?;
                }
            },

            IrInstruction::Call {
                destination,
                function,
                arguments,
            } => {
                let max_arguments = match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => 6,
                    CodegenTarget::Aarch64MacOS => 8,
                };

                if arguments.len() > max_arguments {
                    return Err(vec![CompilerError::internal(format!(
                        "function call has {} arguments, but only {} integer arguments are currently supported",
                        arguments.len(),
                        max_arguments
                    ))]);
                }

                let function_name = self.function_names.get(&Some(*function)).ok_or_else(|| {
                    vec![CompilerError::internal(format!(
                        "unknown function id {:?}",
                        function
                    ))]
                })?;

                for (index, argument) in arguments.iter().enumerate() {
                    let register = self.target.argument_register(index).ok_or_else(|| {
                        vec![CompilerError::internal(format!(
                            "no argument register available for argument {}",
                            index
                        ))]
                    })?;

                    self.emit_load_value(*argument, register)?;
                }

                let symbol = self.symbol_name(function_name);

                match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                        writeln!(self.output, "    call {}", symbol)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                    }

                    CodegenTarget::Aarch64MacOS => {
                        writeln!(self.output, "    bl {}", symbol)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                    }
                }

                if let Some(destination) = destination {
                    let return_register = self.target.return_register();
                    self.emit_store_value(*destination, return_register)?;
                }
            }

            IrInstruction::Phi { .. } => {
                // Phi nodes are handled by emit_edge_copies().
            }

            IrInstruction::LoadField {
                destination,
                receiver,
                field,
            } => {
                let offset = (*field as i32) * 8;

                match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                        self.emit_load(*receiver, "rax")?;

                        if offset == 0 {
                            writeln!(self.output, "    mov rax, [rax]")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        } else {
                            writeln!(self.output, "    mov rax, [rax+{}]", offset)
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        self.emit_store(*destination, "rax")?;
                    }

                    CodegenTarget::Aarch64MacOS => {
                        self.emit_load(*receiver, "x16")?;

                        if offset == 0 {
                            writeln!(self.output, "    ldr x16, [x16]")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        } else {
                            writeln!(self.output, "    ldr x16, [x16, #{}]", offset)
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }

                        self.emit_store(*destination, "x16")?;
                    }
                }
            }

            IrInstruction::StoreField {
                receiver,
                field,
                value,
            } => {
                let offset = (*field as i32) * 8;

                match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                        self.emit_load(*receiver, "rax")?;
                        self.emit_load(*value, "rcx")?;

                        if offset == 0 {
                            writeln!(self.output, "    mov [rax], rcx")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        } else {
                            writeln!(self.output, "    mov [rax+{}], rcx", offset)
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }
                    }

                    CodegenTarget::Aarch64MacOS => {
                        self.emit_load(*receiver, "x16")?;
                        self.emit_load(*value, "x17")?;

                        if offset == 0 {
                            writeln!(self.output, "    str x17, [x16]")
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        } else {
                            writeln!(self.output, "    str x17, [x16, #{}]", offset)
                                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        }
                    }
                }
            }
            IrInstruction::StructCopy {
                destination,
                source,
                struct_id,
            } => {
                let destination_offset =
                    self.struct_storage
                        .get(destination)
                        .copied()
                        .ok_or_else(|| {
                            vec![CompilerError::internal(format!(
                                "no stack storage allocated for struct copy destination {:?}",
                                destination
                            ))]
                        })?;

                let structure = self
                    .program
                    .structs
                    .iter()
                    .find(|structure| structure.id == *struct_id)
                    .ok_or_else(|| {
                        vec![CompilerError::internal(format!(
                            "unknown struct id {:?}",
                            struct_id
                        ))]
                    })?;

                match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                        self.emit_load(*source, "rax")?;

                        writeln!(self.output, "    lea rdx, [rbp-{}]", destination_offset)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                        for field_index in 0..structure.fields.len() {
                            let offset = (field_index as i32) * 8;

                            if offset == 0 {
                                writeln!(self.output, "    mov rcx, [rax]")
                                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                                writeln!(self.output, "    mov [rdx], rcx")
                                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                            } else {
                                writeln!(self.output, "    mov rcx, [rax+{}]", offset)
                                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                                writeln!(self.output, "    mov [rdx+{}], rcx", offset)
                                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                            }
                        }

                        self.emit_store(*destination, "rdx")?;
                    }

                    CodegenTarget::Aarch64MacOS => {
                        self.emit_load(*source, "x16")?;

                        writeln!(self.output, "    sub x17, x29, #{}", destination_offset)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                        for field_index in 0..structure.fields.len() {
                            let offset = (field_index as i32) * 8;

                            if offset == 0 {
                                writeln!(self.output, "    ldr x15, [x16]")
                                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                                writeln!(self.output, "    str x15, [x17]")
                                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                            } else {
                                writeln!(self.output, "    ldr x15, [x16, #{}]", offset)
                                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                                writeln!(self.output, "    str x15, [x17, #{}]", offset)
                                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                            }
                        }

                        self.emit_store(*destination, "x17")?;
                    }
                }
            }
            IrInstruction::Copy {
                destination,
                source,
            } => {
                let temporary_register = match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => "rax",
                    CodegenTarget::Aarch64MacOS => "x16",
                };

                self.emit_load(*source, temporary_register)?;
                self.emit_store(*destination, temporary_register)?;
            }
            IrInstruction::StackAllocStruct {
                destination,
                struct_id,
            } => {
                let offset = self.struct_storage.get(destination).ok_or_else(|| {
                    vec![CompilerError::internal(format!(
                        "no stack storage allocated for stack struct value {:?}",
                        destination
                    ))]
                })?;

                let _structure = self
                    .program
                    .structs
                    .iter()
                    .find(|structure| structure.id == *struct_id)
                    .ok_or_else(|| {
                        vec![CompilerError::internal(format!(
                            "unknown struct id {:?}",
                            struct_id
                        ))]
                    })?;

                match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                        writeln!(self.output, "    lea rax, [rbp-{}]", offset)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                        self.emit_store(*destination, "rax")?;
                    }

                    CodegenTarget::Aarch64MacOS => {
                        writeln!(self.output, "    sub x16, x29, #{}", offset)
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                        self.emit_store(*destination, "x16")?;
                    }
                }
            }
            IrInstruction::StructCall {
                destination,
                function,
                arguments,
                struct_id,
            } => todo!(),
            IrInstruction::ConstFloat { destination, value } => todo!(),
        }

        Ok(())
    }

    fn emit_phi_temp_store(&mut self, register: &str) -> Result<(), Vec<CompilerError>> {
        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(
                    self.output,
                    "    mov [rbp-{}], {}",
                    self.phi_temp_offset, register
                )
                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }

            CodegenTarget::Aarch64MacOS => {
                writeln!(
                    self.output,
                    "    str {}, [x29, #-{}]",
                    register, self.phi_temp_offset
                )
                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }
        }

        Ok(())
    }

    fn emit_phi_temp_load(&mut self, register: &str) -> Result<(), Vec<CompilerError>> {
        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(
                    self.output,
                    "    mov {}, [rbp-{}]",
                    register, self.phi_temp_offset
                )
                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }

            CodegenTarget::Aarch64MacOS => {
                writeln!(
                    self.output,
                    "    ldr {}, [x29, #-{}]",
                    register, self.phi_temp_offset
                )
                .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }
        }

        Ok(())
    }

    fn emit_load_value(
        &mut self,
        value: ValueId,
        register: &str,
    ) -> Result<(), Vec<CompilerError>> {
        let offset = self.value_slots.get(&value).ok_or_else(|| {
            vec![CompilerError::internal(format!(
                "no stack slot allocated for SSA value {:?}",
                value
            ))]
        })?;

        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(self.output, "    mov {}, [rbp-{}]", register, offset)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }

            CodegenTarget::Aarch64MacOS => {
                writeln!(self.output, "    ldr {}, [x29, #-{}]", register, offset)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }
        }

        Ok(())
    }

    fn emit_store_value(
        &mut self,
        value: ValueId,
        register: &str,
    ) -> Result<(), Vec<CompilerError>> {
        let offset = self.value_slots.get(&value).ok_or_else(|| {
            vec![CompilerError::internal(format!(
                "no stack slot allocated for SSA value {:?}",
                value
            ))]
        })?;

        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(self.output, "    mov [rbp-{}], {}", offset, register)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }

            CodegenTarget::Aarch64MacOS => {
                writeln!(self.output, "    str {}, [x29, #-{}]", register, offset)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }
        }

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Terminators
    // ---------------------------------------------------------------------

    fn emit_terminator(
        &mut self,
        predecessor: BlockId,
        terminator: &Terminator,
    ) -> Result<(), Vec<CompilerError>> {
        match terminator {
            Terminator::Jump(block) => {
                self.emit_edge_copies(predecessor, *block)?;

                match self.target {
                    CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                        writeln!(self.output, "    jmp {}", self.block_label(*block))
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                    }
                    CodegenTarget::Aarch64MacOS => {
                        writeln!(self.output, "    b {}", self.block_label(*block))
                            .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                    }
                }
            }

            Terminator::Branch {
                condition,
                then_block,
                else_block,
            } => match self.target {
                CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                    self.emit_load(*condition, "rax")?;

                    writeln!(self.output, "    cmp rax, 0")
                        .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                    writeln!(self.output, "    jne {}", self.block_label(*then_block))
                        .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                    writeln!(self.output, "    jmp {}", self.block_label(*else_block))
                        .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                }

                CodegenTarget::Aarch64MacOS => {
                    self.emit_load(*condition, "x0")?;

                    writeln!(self.output, "    cmp x0, #0")
                        .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                    writeln!(self.output, "    b.ne {}", self.block_label(*then_block))
                        .map_err(|e| vec![CompilerError::internal(e.to_string())])?;

                    writeln!(self.output, "    b {}", self.block_label(*else_block))
                        .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                }
            },

            Terminator::Return { value } => {
                if let Some(value) = value {
                    let register = self.target.return_register();
                    self.emit_load(*value, register)?;
                }

                self.emit_epilogue()?;
            }

            Terminator::Unreachable => match self.target {
                CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                    writeln!(self.output, "    ud2")
                        .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                }

                CodegenTarget::Aarch64MacOS => {
                    writeln!(self.output, "    brk #0")
                        .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
                }
            },
        }

        Ok(())
    }

    // ---------------------------------------------------------------------
    // Values
    // ---------------------------------------------------------------------

    fn emit_load(&mut self, value: ValueId, register: &str) -> Result<(), Vec<CompilerError>> {
        let offset = self.value_slots.get(&value).ok_or_else(|| {
            vec![CompilerError::internal(format!(
                "no stack slot allocated for SSA value {:?}",
                value
            ))]
        })?;

        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(self.output, "    mov {}, [rbp-{}]", register, offset)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }

            CodegenTarget::Aarch64MacOS => {
                writeln!(self.output, "    ldr {}, [x29, #-{}]", register, offset)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }
        }

        Ok(())
    }

    fn emit_store(&mut self, value: ValueId, register: &str) -> Result<(), Vec<CompilerError>> {
        let offset = self.value_slots.get(&value).ok_or_else(|| {
            vec![CompilerError::internal(format!(
                "no stack slot allocated for SSA value {:?}",
                value
            ))]
        })?;

        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(self.output, "    mov [rbp-{}], {}", offset, register)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }

            CodegenTarget::Aarch64MacOS => {
                writeln!(self.output, "    str {}, [x29, #-{}]", register, offset)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }
        }

        Ok(())
    }

    fn emit_load_immediate(
        &mut self,
        register: &str,
        value: i64,
    ) -> Result<(), Vec<CompilerError>> {
        match self.target {
            CodegenTarget::X86_64 | CodegenTarget::X86_64MacOS => {
                writeln!(self.output, "    mov {}, {}", register, value)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }

            CodegenTarget::Aarch64MacOS => {
                writeln!(self.output, "    mov {}, #{}", register, value)
                    .map_err(|e| vec![CompilerError::internal(e.to_string())])?;
            }
        }

        Ok(())
    }
}

// -------------------------------------------------------------------------
// Helpers
// -------------------------------------------------------------------------

fn instruction_destination(instruction: &IrInstruction) -> Option<ValueId> {
    match instruction {
        IrInstruction::Parameter { destination, .. } => Some(*destination),

        IrInstruction::ConstInt { destination, .. } => Some(*destination),

        IrInstruction::ConstFloat { destination, .. } => Some(*destination),

        IrInstruction::ConstString { destination, .. } => Some(*destination),

        IrInstruction::ConstBool { destination, .. } => Some(*destination),

        IrInstruction::LoadLocal { destination, .. } => Some(*destination),

        IrInstruction::StoreLocal { .. } => None,

        IrInstruction::Binary { destination, .. } => Some(*destination),

        IrInstruction::Call { destination, .. } => *destination,

        IrInstruction::StructCall { destination, .. } => Some(*destination),

        IrInstruction::Phi { destination, .. } => Some(*destination),

        IrInstruction::LoadField { destination, .. } => Some(*destination),

        IrInstruction::StructCopy { destination, .. } => Some(*destination),

        IrInstruction::StoreField { .. } => None,
        IrInstruction::Copy { destination, .. } => Some(*destination),
        IrInstruction::StackAllocStruct { destination, .. } => Some(*destination),
    }
}

fn generate_function(
    output: &mut String,
    program: &IrProgram,
    function: &IrFunction,
    function_names: &HashMap<Option<FunctionId>, String>,
    string_labels: &BTreeMap<String, String>,
    target: CodegenTarget,
) -> Result<(), Vec<CompilerError>> {
    FunctionCodegen::new(
        output,
        program,
        function,
        function_names,
        string_labels,
        target,
    )
    .generate()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::ir::{
        BasicBlock, IrFunction, IrInstruction, IrProgram, IrStruct, IrType, Terminator, ValueId,
    };
    use crate::semantic::symbols::{FunctionId, StructId};

    fn function(instructions: Vec<IrInstruction>) -> IrFunction {
        IrFunction {
            id: Some(FunctionId(0)),
            name: "main".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions,
                terminator: Terminator::Return {
                    value: Some(ValueId(0)),
                },
            }],
        }
    }

    fn program(function: IrFunction) -> IrProgram {
        IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        }
    }

    #[test]
    fn generates_integer_constant() {
        let function = function(vec![IrInstruction::ConstInt {
            destination: ValueId(0),
            value: 42,
        }]);

        let assembly =
            generate(&program(function), CodegenTarget::X86_64).expect("codegen should succeed");

        assert!(assembly.contains("mov rax, 42"));
        assert!(assembly.contains("mov [rbp-8], rax"));
        assert!(assembly.contains("leave"));
        assert!(assembly.contains("ret"));
    }

    #[test]
    fn generates_boolean_constants() {
        let function = function(vec![IrInstruction::ConstBool {
            destination: ValueId(0),
            value: true,
        }]);

        let assembly =
            generate(&program(function), CodegenTarget::X86_64).expect("codegen should succeed");

        assert!(assembly.contains("mov rax, 1"));
    }

    #[test]
    fn generates_addition() {
        let function = function(vec![
            IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 10,
            },
            IrInstruction::ConstInt {
                destination: ValueId(1),
                value: 32,
            },
            IrInstruction::Binary {
                destination: ValueId(2),
                op: IrBinaryOp::Add,
                left: ValueId(0),
                right: ValueId(1),
            },
        ]);

        let assembly =
            generate(&program(function), CodegenTarget::X86_64).expect("codegen should succeed");

        assert!(assembly.contains("add rax, rcx"));
    }

    #[test]
    fn generates_division() {
        let function = function(vec![
            IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 20,
            },
            IrInstruction::ConstInt {
                destination: ValueId(1),
                value: 4,
            },
            IrInstruction::Binary {
                destination: ValueId(2),
                op: IrBinaryOp::Divide,
                left: ValueId(0),
                right: ValueId(1),
            },
        ]);

        let assembly =
            generate(&program(function), CodegenTarget::X86_64).expect("codegen should succeed");

        assert!(assembly.contains("cqo"));
        assert!(assembly.contains("idiv rcx"));
    }

    #[test]
    fn generates_equality() {
        let function = function(vec![
            IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 10,
            },
            IrInstruction::ConstInt {
                destination: ValueId(1),
                value: 10,
            },
            IrInstruction::Binary {
                destination: ValueId(2),
                op: IrBinaryOp::Equal,
                left: ValueId(0),
                right: ValueId(1),
            },
        ]);

        let assembly =
            generate(&program(function), CodegenTarget::X86_64).expect("codegen should succeed");

        assert!(assembly.contains("cmp rax, rcx"));
        assert!(assembly.contains("sete al"));
        assert!(assembly.contains("movzx rax, al"));
    }
}

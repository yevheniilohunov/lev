use std::collections::{HashMap, HashSet};

use crate::{
    compiler::error::CompilerError,
    ir::{BlockId, IrInstruction, Terminator, ValueId},
};

use super::ir::{IrBinaryOp, IrFunction, IrProgram};

pub fn remove_unreachable_blocks(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = cleanup_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

pub fn eliminate_dead_code(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = eliminate_dead_code_from_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn eliminate_dead_code_from_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let mut live = HashSet::<ValueId>::new();

    // Values used by terminators are always live.
    for block in &function.blocks {
        match &block.terminator {
            super::ir::Terminator::Jump(_) | super::ir::Terminator::Unreachable => {}

            super::ir::Terminator::Branch { condition, .. } => {
                live.insert(*condition);
            }

            super::ir::Terminator::Return { value } => {
                if let Some(value) = value {
                    live.insert(*value);
                }
            }
        }
    }

    // Side-effecting instructions are roots.
    //
    // Their input values must remain live even if their own result is unused.
    for block in &function.blocks {
        for instruction in &block.instructions {
            match instruction {
                IrInstruction::Call { arguments, .. } => {
                    live.extend(arguments.iter().copied());
                }

                IrInstruction::StoreLocal { value, .. } => {
                    live.insert(*value);
                }

                IrInstruction::StoreField {
                    receiver, value, ..
                } => {
                    live.insert(*receiver);
                    live.insert(*value);
                }

                IrInstruction::Phi { sources, .. } => {
                    live.extend(sources.iter().map(|(_, value)| *value));
                }

                _ => {}
            }
        }
    }

    // Propagate liveness backwards through instruction dependencies.
    loop {
        let mut changed = false;

        for block in &function.blocks {
            for instruction in &block.instructions {
                let Some(destination) = instruction_destination(instruction) else {
                    continue;
                };

                if !live.contains(&destination) {
                    continue;
                }

                match instruction {
                    IrInstruction::Copy { source, .. } => {
                        changed |= live.insert(*source);
                    }

                    IrInstruction::StructCopy { source, .. } => {
                        changed |= live.insert(*source);
                    }

                    IrInstruction::Binary { left, right, .. } => {
                        changed |= live.insert(*left);
                        changed |= live.insert(*right);
                    }

                    IrInstruction::LoadField { receiver, .. } => {
                        changed |= live.insert(*receiver);
                    }

                    IrInstruction::Call { arguments, .. } => {
                        for argument in arguments {
                            changed |= live.insert(*argument);
                        }
                    }

                    IrInstruction::Phi { sources, .. } => {
                        for (_, value) in sources {
                            changed |= live.insert(*value);
                        }
                    }

                    IrInstruction::Parameter { .. }
                    | IrInstruction::ConstInt { .. }
                    | IrInstruction::ConstString { .. }
                    | IrInstruction::ConstBool { .. }
                    | IrInstruction::LoadLocal { .. }
                    | IrInstruction::StoreLocal { .. }
                    | IrInstruction::AllocStruct { .. }
                    | IrInstruction::StoreField { .. } => {}
                }
            }
        }

        if !changed {
            break;
        }
    }

    for block in &mut function.blocks {
        block.instructions.retain(|instruction| {
            let Some(destination) = instruction_destination(instruction) else {
                // Instructions without a destination are side-effecting.
                return true;
            };

            if live.contains(&destination) {
                return true;
            }

            !is_pure_instruction(instruction)
        });
    }

    Ok(())
}

fn is_pure_instruction(instruction: &IrInstruction) -> bool {
    matches!(
        instruction,
        IrInstruction::ConstInt { .. }
            | IrInstruction::ConstString { .. }
            | IrInstruction::ConstBool { .. }
            | IrInstruction::Copy { .. }
            | IrInstruction::Binary { .. }
            | IrInstruction::LoadField { .. }
    )
}

fn instruction_destination(instruction: &IrInstruction) -> Option<ValueId> {
    match instruction {
        IrInstruction::Parameter { destination, .. }
        | IrInstruction::ConstInt { destination, .. }
        | IrInstruction::ConstString { destination, .. }
        | IrInstruction::ConstBool { destination, .. }
        | IrInstruction::LoadLocal { destination, .. }
        | IrInstruction::Copy { destination, .. }
        | IrInstruction::StructCopy { destination, .. }
        | IrInstruction::AllocStruct { destination, .. }
        | IrInstruction::LoadField { destination, .. }
        | IrInstruction::Binary { destination, .. }
        | IrInstruction::Phi { destination, .. } => Some(*destination),

        IrInstruction::Call { destination, .. } => *destination,

        IrInstruction::StoreLocal { .. } | IrInstruction::StoreField { .. } => None,
    }
}

fn cleanup_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let reachable = function.reachable_blocks();

    if !reachable.contains(&function.entry) {
        return Err(vec![CompilerError::internal(format!(
            "function {} has an unreachable entry block {:?}",
            function.name, function.entry
        ))]);
    }

    function
        .blocks
        .retain(|block| reachable.contains(&block.id));

    Ok(())
}

pub fn constant_fold(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = constant_fold_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn constant_fold_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let mut constants = HashMap::<ValueId, i64>::new();

    for block in &mut function.blocks {
        for instruction in &mut block.instructions {
            let folded = match instruction {
                IrInstruction::ConstInt { destination, value } => {
                    constants.insert(*destination, *value);
                    None
                }

                IrInstruction::Binary {
                    destination,
                    op,
                    left,
                    right,
                } => {
                    let Some(left_value) = constants.get(left).copied() else {
                        continue;
                    };

                    let Some(right_value) = constants.get(right).copied() else {
                        continue;
                    };

                    fold_integer_binary(*op, left_value, right_value)
                        .map(|value| (*destination, value))
                }

                _ => None,
            };

            if let Some((destination, value)) = folded {
                *instruction = IrInstruction::ConstInt { destination, value };

                constants.insert(destination, value);
            }
        }
    }

    Ok(())
}

fn fold_integer_binary(op: IrBinaryOp, left: i64, right: i64) -> Option<i64> {
    match op {
        IrBinaryOp::Add => left.checked_add(right),
        IrBinaryOp::Subtract => left.checked_sub(right),
        IrBinaryOp::Multiply => left.checked_mul(right),
        IrBinaryOp::Divide => {
            if right == 0 {
                None
            } else {
                left.checked_div(right)
            }
        }
        IrBinaryOp::Equal => Some((left == right) as i64),
    }
}

pub fn constant_propagate(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = constant_propagate_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn constant_propagate_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    let mut in_facts = HashMap::<BlockId, HashMap<ValueId, i64>>::new();
    let mut out_facts = HashMap::<BlockId, HashMap<ValueId, i64>>::new();

    // The entry block has no incoming constant facts.
    in_facts.insert(function.entry, HashMap::new());

    // Compute the conservative fixed point.
    //
    // A constant is propagated into a block only when every predecessor
    // agrees on the same constant value.
    loop {
        let mut changed = false;

        for block in &function.blocks {
            let block_id = block.id;

            let new_in = if block_id == function.entry {
                HashMap::new()
            } else {
                let preds = predecessors.get(&block_id).cloned().unwrap_or_default();

                if preds.is_empty() {
                    HashMap::new()
                } else {
                    intersect_constant_facts(&preds, &out_facts)
                }
            };

            if in_facts.get(&block_id) != Some(&new_in) {
                in_facts.insert(block_id, new_in.clone());
                changed = true;
            }

            let mut facts = new_in;

            for instruction in &block.instructions {
                transfer_constant_fact(instruction, &mut facts);
            }

            if out_facts.get(&block_id) != Some(&facts) {
                out_facts.insert(block_id, facts);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    // Rewrite only after the analysis has reached a fixed point.
    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &mut block.instructions {
            let replacement = match instruction {
                IrInstruction::ConstInt { destination, value } => {
                    facts.insert(*destination, *value);
                    None
                }

                IrInstruction::Copy {
                    destination,
                    source,
                } => {
                    if let Some(value) = facts.get(source).copied() {
                        facts.insert(*destination, value);

                        Some(IrInstruction::ConstInt {
                            destination: *destination,
                            value,
                        })
                    } else {
                        facts.remove(destination);
                        None
                    }
                }

                _ => {
                    if let Some(destination) = instruction_destination(instruction) {
                        facts.remove(&destination);
                    }

                    None
                }
            };

            if let Some(replacement) = replacement {
                *instruction = replacement;
            }
        }
    }

    Ok(())
}

fn intersect_constant_facts(
    predecessors: &[BlockId],
    out_facts: &HashMap<BlockId, HashMap<ValueId, i64>>,
) -> HashMap<ValueId, i64> {
    let Some(first) = predecessors.first() else {
        return HashMap::new();
    };

    let Some(first_facts) = out_facts.get(first) else {
        return HashMap::new();
    };

    let mut result = first_facts.clone();

    for predecessor in &predecessors[1..] {
        let Some(facts) = out_facts.get(predecessor) else {
            return HashMap::new();
        };

        result.retain(|value, constant| facts.get(value) == Some(constant));
    }

    result
}

fn transfer_constant_fact(instruction: &IrInstruction, facts: &mut HashMap<ValueId, i64>) {
    match instruction {
        IrInstruction::ConstInt { destination, value } => {
            facts.insert(*destination, *value);
        }

        IrInstruction::Copy {
            destination,
            source,
        } => {
            if let Some(value) = facts.get(source).copied() {
                facts.insert(*destination, value);
            } else {
                facts.remove(destination);
            }
        }

        _ => {
            if let Some(destination) = instruction_destination(instruction) {
                facts.remove(&destination);
            }
        }
    }
}

pub fn copy_propagate(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = copy_propagate_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn copy_propagate_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    let mut in_facts = HashMap::<BlockId, HashMap<ValueId, ValueId>>::new();
    let mut out_facts = HashMap::<BlockId, HashMap<ValueId, ValueId>>::new();

    // The entry block starts with no incoming copy facts.
    in_facts.insert(function.entry, HashMap::new());

    // Compute a conservative fixed point.
    //
    // For blocks with multiple predecessors, a copy is propagated only
    // when every predecessor agrees on the same source.
    loop {
        let mut changed = false;

        for block in &function.blocks {
            let block_id = block.id;

            let new_in = if block_id == function.entry {
                HashMap::new()
            } else {
                let preds = predecessors.get(&block_id).cloned().unwrap_or_default();

                if preds.is_empty() {
                    HashMap::new()
                } else {
                    intersect_copy_facts(&preds, &out_facts)
                }
            };

            if in_facts.get(&block_id) != Some(&new_in) {
                in_facts.insert(block_id, new_in.clone());
                changed = true;
            }

            let mut facts = new_in;

            for instruction in &block.instructions {
                transfer_copy_fact(instruction, &mut facts);
            }

            if out_facts.get(&block_id) != Some(&facts) {
                out_facts.insert(block_id, facts);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    // Rewrite using the fixed-point facts.
    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &mut block.instructions {
            rewrite_instruction_values(instruction, &facts);

            if let IrInstruction::Copy {
                destination,
                source,
            } = instruction
            {
                let source = resolve_copy(*source, &facts);
                facts.insert(*destination, source);
            }
        }

        rewrite_terminator_values(&mut block.terminator, &facts);

        block
            .instructions
            .retain(|instruction| !matches!(instruction, IrInstruction::Copy { .. }));
    }

    Ok(())
}

fn build_predecessors(function: &IrFunction) -> HashMap<BlockId, Vec<BlockId>> {
    let mut predecessors = HashMap::<BlockId, Vec<BlockId>>::new();

    for block in &function.blocks {
        match &block.terminator {
            Terminator::Jump(target) => {
                predecessors.entry(*target).or_default().push(block.id);
            }

            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                predecessors.entry(*then_block).or_default().push(block.id);

                predecessors.entry(*else_block).or_default().push(block.id);
            }

            Terminator::Return { .. } | Terminator::Unreachable => {}
        }
    }

    predecessors
}

fn intersect_copy_facts(
    predecessors: &[BlockId],
    out_facts: &HashMap<BlockId, HashMap<ValueId, ValueId>>,
) -> HashMap<ValueId, ValueId> {
    let Some(first) = predecessors.first() else {
        return HashMap::new();
    };

    let Some(first_facts) = out_facts.get(first) else {
        return HashMap::new();
    };

    let mut result = first_facts.clone();

    for predecessor in &predecessors[1..] {
        let Some(facts) = out_facts.get(predecessor) else {
            return HashMap::new();
        };

        result.retain(|value, source| facts.get(value) == Some(source));
    }

    result
}

fn transfer_copy_fact(instruction: &IrInstruction, facts: &mut HashMap<ValueId, ValueId>) {
    if let IrInstruction::Copy {
        destination,
        source,
    } = instruction
    {
        let source = resolve_copy(*source, facts);
        facts.insert(*destination, source);
    }
}

fn resolve_copy(value: ValueId, copies: &HashMap<ValueId, ValueId>) -> ValueId {
    let mut current = value;

    while let Some(&source) = copies.get(&current) {
        if source == current {
            break;
        }

        current = source;
    }

    current
}

fn rewrite_instruction_values(instruction: &mut IrInstruction, copies: &HashMap<ValueId, ValueId>) {
    match instruction {
        IrInstruction::Copy { source, .. } => {
            *source = resolve_copy(*source, copies);
        }

        IrInstruction::StoreLocal { value, .. } => {
            *value = resolve_copy(*value, copies);
        }

        IrInstruction::StoreField {
            receiver, value, ..
        } => {
            *receiver = resolve_copy(*receiver, copies);
            *value = resolve_copy(*value, copies);
        }

        IrInstruction::LoadField { receiver, .. } => {
            *receiver = resolve_copy(*receiver, copies);
        }

        IrInstruction::Binary { left, right, .. } => {
            *left = resolve_copy(*left, copies);
            *right = resolve_copy(*right, copies);
        }

        IrInstruction::Call { arguments, .. } => {
            for argument in arguments {
                *argument = resolve_copy(*argument, copies);
            }
        }

        IrInstruction::StructCopy { source, .. } => {
            *source = resolve_copy(*source, copies);
        }

        IrInstruction::Phi { sources, .. } => {
            for (_, value) in sources {
                *value = resolve_copy(*value, copies);
            }
        }

        IrInstruction::Parameter { .. }
        | IrInstruction::ConstInt { .. }
        | IrInstruction::ConstString { .. }
        | IrInstruction::ConstBool { .. }
        | IrInstruction::LoadLocal { .. }
        | IrInstruction::AllocStruct { .. } => {}
    }
}

fn rewrite_terminator_values(terminator: &mut Terminator, copies: &HashMap<ValueId, ValueId>) {
    match terminator {
        Terminator::Branch { condition, .. } => {
            *condition = resolve_copy(*condition, copies);
        }

        Terminator::Return { value } => {
            if let Some(value) = value {
                *value = resolve_copy(*value, copies);
            }
        }

        Terminator::Jump(_) | Terminator::Unreachable => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ir::ir::{
        BasicBlock, IrFunction, IrInstruction, IrProgram, IrType, Terminator, ValueId,
    };
    use crate::ir::BlockId;
    use crate::semantic::symbols::{FunctionId, LocalId};

    fn function_with_unreachable_block() -> IrFunction {
        IrFunction {
            id: Some(FunctionId(0)),
            name: "unreachable_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 42,
                    }],
                    terminator: Terminator::Jump(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Return {
                        value: Some(ValueId(0)),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 999,
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                },
            ],
        }
    }

    #[test]
    fn removes_unreachable_block() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function_with_unreachable_block()],
        };

        remove_unreachable_blocks(&mut program).expect("unreachable-block cleanup should succeed");

        let function = &program.functions[0];

        assert_eq!(function.blocks.len(), 2);

        assert!(function.blocks.iter().any(|block| block.id == BlockId(0)));
        assert!(function.blocks.iter().any(|block| block.id == BlockId(1)));

        assert!(
            !function.blocks.iter().any(|block| block.id == BlockId(2)),
            "unreachable block should be removed"
        );
    }

    #[test]
    fn preserves_all_reachable_blocks() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "reachable_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Void,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Return { value: None },
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Return { value: None },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        remove_unreachable_blocks(&mut program).expect("unreachable-block cleanup should succeed");

        let function = &program.functions[0];

        assert_eq!(function.blocks.len(), 3);

        for id in [BlockId(0), BlockId(1), BlockId(2)] {
            assert!(
                function.blocks.iter().any(|block| block.id == id),
                "reachable block {:?} should be preserved",
                id
            );
        }
    }

    #[test]
    fn removes_unreachable_chain() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "unreachable_chain_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Void,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: Vec::new(),
                    terminator: Terminator::Return { value: None },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Jump(BlockId(2)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: Vec::new(),
                    terminator: Terminator::Return { value: None },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        remove_unreachable_blocks(&mut program).expect("unreachable-block cleanup should succeed");

        let function = &program.functions[0];

        assert_eq!(function.blocks.len(), 1);

        assert_eq!(function.blocks[0].id, BlockId(0));
    }

    #[test]
    fn removes_unused_pure_instructions() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "dce_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 10,
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 20,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Add,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                ],
                terminator: Terminator::Return {
                    value: Some(ValueId(0)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        eliminate_dead_code(&mut program).expect("DCE should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert_eq!(instructions.len(), 1);

        assert!(matches!(
            instructions[0],
            IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 10,
            }
        ));
    }

    #[test]
    fn preserves_side_effecting_calls() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "dce_call_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Void,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 42,
                    },
                    IrInstruction::Call {
                        destination: None,
                        function: FunctionId(1),
                        arguments: vec![ValueId(0)],
                    },
                ],
                terminator: Terminator::Return { value: None },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![
                function,
                IrFunction {
                    id: Some(FunctionId(1)),
                    name: "callee".to_string(),
                    owner: None,
                    parameters: Vec::new(),
                    locals: Vec::new(),
                    return_type: IrType::Void,
                    entry: BlockId(0),
                    blocks: vec![BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    }],
                },
            ],
        };

        eliminate_dead_code(&mut program).expect("DCE should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert_eq!(instructions.len(), 2);

        assert!(matches!(
            instructions[0],
            IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 42,
            }
        ));

        assert!(matches!(
            instructions[1],
            IrInstruction::Call {
                destination: None,
                function: FunctionId(1),
                ..
            }
        ));
    }

    #[test]
    fn removes_dead_instruction_chain() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "dce_chain_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
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
                    IrInstruction::Binary {
                        destination: ValueId(3),
                        op: IrBinaryOp::Multiply,
                        left: ValueId(2),
                        right: ValueId(1),
                    },
                ],
                terminator: Terminator::Return {
                    value: Some(ValueId(0)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        eliminate_dead_code(&mut program).expect("DCE should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert_eq!(instructions.len(), 1);

        assert!(matches!(
            instructions[0],
            IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 1,
            }
        ));
    }

    #[test]
    fn folds_integer_addition() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "constant_fold_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 10,
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 20,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Add,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                ],
                terminator: Terminator::Return {
                    value: Some(ValueId(2)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        constant_fold(&mut program).expect("constant folding should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert_eq!(instructions.len(), 3);

        assert!(matches!(
            instructions[2],
            IrInstruction::ConstInt {
                destination: ValueId(2),
                value: 30,
            }
        ));
    }

    #[test]
    fn folds_integer_arithmetic() {
        let cases = [
            (IrBinaryOp::Subtract, 20, 5, 15),
            (IrBinaryOp::Multiply, 6, 7, 42),
            (IrBinaryOp::Divide, 42, 6, 7),
        ];

        for (op, left, right, expected) in cases {
            let function = IrFunction {
                id: Some(FunctionId(0)),
                name: "constant_fold_test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::ConstInt {
                            destination: ValueId(0),
                            value: left,
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: right,
                        },
                        IrInstruction::Binary {
                            destination: ValueId(2),
                            op,
                            left: ValueId(0),
                            right: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            };

            let mut program = IrProgram {
                structs: Vec::new(),
                functions: vec![function],
            };

            constant_fold(&mut program).expect("constant folding should succeed");

            let instructions = &program.functions[0].blocks[0].instructions;

            assert!(matches!(
                instructions[2],
                IrInstruction::ConstInt {
                    destination: ValueId(2),
                    value,
                } if value == expected
            ));
        }
    }

    #[test]
    fn does_not_fold_division_by_zero() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "constant_fold_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 42,
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 0,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Divide,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                ],
                terminator: Terminator::Return {
                    value: Some(ValueId(2)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        constant_fold(&mut program).expect("constant folding should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            instructions[2],
            IrInstruction::Binary {
                destination: ValueId(2),
                op: IrBinaryOp::Divide,
                left: ValueId(0),
                right: ValueId(1),
            }
        ));
    }

    #[test]
    fn propagates_integer_constant_through_copy() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "constant_propagation_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 42,
                    },
                    IrInstruction::Copy {
                        destination: ValueId(1),
                        source: ValueId(0),
                    },
                ],
                terminator: Terminator::Return {
                    value: Some(ValueId(1)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        constant_propagate(&mut program).expect("constant propagation should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert_eq!(instructions.len(), 2);

        assert!(matches!(
            instructions[1],
            IrInstruction::ConstInt {
                destination: ValueId(1),
                value: 42,
            }
        ));
    }

    #[test]
    fn propagates_constants_into_constant_folding() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "constant_propagation_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::ConstInt {
                        destination: ValueId(0),
                        value: 10,
                    },
                    IrInstruction::Copy {
                        destination: ValueId(1),
                        source: ValueId(0),
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 20,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(3),
                        op: IrBinaryOp::Add,
                        left: ValueId(1),
                        right: ValueId(2),
                    },
                ],
                terminator: Terminator::Return {
                    value: Some(ValueId(3)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        constant_propagate(&mut program).expect("constant propagation should succeed");

        constant_fold(&mut program).expect("constant folding should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            instructions[3],
            IrInstruction::ConstInt {
                destination: ValueId(3),
                value: 30,
            }
        ));
    }

    #[test]
    fn propagates_copy_into_binary_instruction() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "copy_propagation_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::Parameter {
                        destination: ValueId(0),
                        local: LocalId(0),
                    },
                    IrInstruction::Copy {
                        destination: ValueId(1),
                        source: ValueId(0),
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 10,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(3),
                        op: IrBinaryOp::Add,
                        left: ValueId(1),
                        right: ValueId(2),
                    },
                ],
                terminator: Terminator::Return {
                    value: Some(ValueId(3)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        copy_propagate(&mut program).expect("copy propagation should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert_eq!(instructions.len(), 3);

        assert!(matches!(
            instructions[2],
            IrInstruction::Binary {
                destination: ValueId(3),
                op: IrBinaryOp::Add,
                left: ValueId(0),
                right: ValueId(2),
            }
        ));
    }

    #[test]
    fn does_not_propagate_copy_when_predecessors_disagree() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "cfg_copy_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::Parameter {
                            destination: ValueId(0),
                            local: LocalId(0),
                        },
                        IrInstruction::Parameter {
                            destination: ValueId(1),
                            local: LocalId(1),
                        },
                    ],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::Copy {
                        destination: ValueId(2),
                        source: ValueId(0),
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![IrInstruction::Copy {
                        destination: ValueId(2),
                        source: ValueId(1),
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        copy_propagate(&mut program).expect("copy propagation should succeed");

        assert!(matches!(
            program.functions[0].blocks[3].terminator,
            Terminator::Return {
                value: Some(ValueId(2)),
            }
        ));
    }

    #[test]
    fn propagates_copy_when_all_predecessors_agree() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "cfg_copy_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::Parameter {
                        destination: ValueId(0),
                        local: LocalId(0),
                    }],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::Copy {
                        destination: ValueId(2),
                        source: ValueId(0),
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![IrInstruction::Copy {
                        destination: ValueId(2),
                        source: ValueId(0),
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        copy_propagate(&mut program).expect("copy propagation should succeed");

        assert!(matches!(
            program.functions[0].blocks[3].terminator,
            Terminator::Return {
                value: Some(ValueId(0)),
            }
        ));
    }

    #[test]
    fn propagates_constant_when_all_predecessors_agree() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "cfg_constant_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::Parameter {
                        destination: ValueId(0),
                        local: LocalId(0),
                    }],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 42,
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 42,
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![IrInstruction::Copy {
                        destination: ValueId(3),
                        source: ValueId(2),
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(3)),
                    },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        constant_propagate(&mut program).expect("constant propagation should succeed");

        let instructions = &program.functions[0].blocks[3].instructions;

        assert!(matches!(
            instructions[0],
            IrInstruction::ConstInt {
                destination: ValueId(3),
                value: 42,
            }
        ));
    }

    #[test]
    fn does_not_propagate_constant_when_predecessors_disagree() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "cfg_constant_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::Parameter {
                        destination: ValueId(0),
                        local: LocalId(0),
                    }],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 42,
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 99,
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![IrInstruction::Copy {
                        destination: ValueId(3),
                        source: ValueId(2),
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(3)),
                    },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        constant_propagate(&mut program).expect("constant propagation should succeed");

        let instructions = &program.functions[0].blocks[3].instructions;

        assert!(matches!(
            instructions[0],
            IrInstruction::Copy {
                destination: ValueId(3),
                source: ValueId(2),
            }
        ));
    }
}

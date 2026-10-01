use std::collections::{HashMap, HashSet};

use crate::{
    compiler::error::CompilerError,
    ir::{BlockId, IrInstruction, Terminator, ValueId},
    semantic::symbols::LocalId,
};

use super::ir::{IrBinaryOp, IrFunction, IrProgram};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GvnExpression {
    op: IrBinaryOp,
    left: ValueId,
    right: ValueId,
}

pub fn gvn_cse(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = gvn_cse_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn gvn_cse_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    let mut in_facts = HashMap::<BlockId, HashMap<GvnExpression, ValueId>>::new();
    let mut out_facts = HashMap::<BlockId, HashMap<GvnExpression, ValueId>>::new();

    in_facts.insert(function.entry, HashMap::new());

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
                    intersect_gvn_facts(&preds, &out_facts)
                }
            };

            if in_facts.get(&block_id) != Some(&new_in) {
                in_facts.insert(block_id, new_in.clone());
                changed = true;
            }

            let mut facts = new_in;
            let mut aliases = HashMap::<ValueId, ValueId>::new();

            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::Binary {
                        destination,
                        op,
                        left,
                        right,
                    } => {
                        let left = canonical_gvn_value(*left, &aliases);
                        let right = canonical_gvn_value(*right, &aliases);

                        let (left, right) = canonical_gvn_operands(*op, left, right);

                        let expression = GvnExpression {
                            op: *op,
                            left,
                            right,
                        };

                        facts.insert(expression, *destination);
                    }

                    IrInstruction::Copy {
                        destination,
                        source,
                    } => {
                        let source = canonical_gvn_value(*source, &aliases);

                        aliases.insert(*destination, source);
                    }

                    _ => {
                        if let Some(destination) = instruction_destination(instruction) {
                            aliases.remove(&destination);
                        }
                    }
                }
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

    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        let mut aliases = HashMap::<ValueId, ValueId>::new();

        for instruction in &mut block.instructions {
            match instruction {
                IrInstruction::Binary {
                    destination,
                    op,
                    left,
                    right,
                } => {
                    let canonical_left = canonical_gvn_value(*left, &aliases);

                    let canonical_right = canonical_gvn_value(*right, &aliases);

                    let (canonical_left, canonical_right) =
                        canonical_gvn_operands(*op, canonical_left, canonical_right);

                    let expression = GvnExpression {
                        op: *op,
                        left: canonical_left,
                        right: canonical_right,
                    };

                    if let Some(existing) = facts.get(&expression).copied() {
                        if existing != *destination {
                            aliases.insert(*destination, existing);

                            *instruction = IrInstruction::Copy {
                                destination: *destination,
                                source: existing,
                            };
                        } else {
                            aliases.remove(destination);
                        }
                    } else {
                        facts.insert(expression, *destination);
                        aliases.remove(destination);
                    }
                }

                IrInstruction::Copy {
                    destination,
                    source,
                } => {
                    let canonical_source = canonical_gvn_value(*source, &aliases);

                    aliases.insert(*destination, canonical_source);

                    if *source != canonical_source {
                        *instruction = IrInstruction::Copy {
                            destination: *destination,
                            source: canonical_source,
                        };
                    }
                }

                _ => {
                    if let Some(destination) = instruction_destination(instruction) {
                        aliases.remove(&destination);
                    }
                }
            }
        }
    }

    Ok(())
}

fn canonical_gvn_operands(op: IrBinaryOp, left: ValueId, right: ValueId) -> (ValueId, ValueId) {
    match op {
        IrBinaryOp::Add | IrBinaryOp::Multiply | IrBinaryOp::Equal => {
            if left <= right {
                (left, right)
            } else {
                (right, left)
            }
        }
        IrBinaryOp::Subtract | IrBinaryOp::Divide => (left, right),
    }
}

fn canonical_gvn_value(value: ValueId, aliases: &HashMap<ValueId, ValueId>) -> ValueId {
    let mut current = value;

    while let Some(next) = aliases.get(&current) {
        if *next == current {
            break;
        }

        current = *next;
    }

    current
}

pub fn remove_unreachable_blocks(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = remove_unreachable_blocks_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn intersect_gvn_facts(
    predecessors: &[BlockId],
    out_facts: &HashMap<BlockId, HashMap<GvnExpression, ValueId>>,
) -> HashMap<GvnExpression, ValueId> {
    let Some(first) = predecessors.first() else {
        return HashMap::new();
    };

    let Some(first_facts) = out_facts.get(first) else {
        return HashMap::new();
    };

    let mut result = first_facts.clone();

    for predecessor in &predecessors[1..] {
        let Some(facts) = out_facts.get(predecessor) else {
            result.clear();
            break;
        };

        result.retain(|expression, value| facts.get(expression) == Some(value));
    }

    result
}

fn remove_unreachable_blocks_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let reachable = function.reachable_blocks();

    if !reachable.contains(&function.entry) {
        return Err(vec![CompilerError {
            message: format!(
                "function '{}': entry block {:?} is unreachable",
                function.name, function.entry
            ),
            src: None,
            span: None,
        }]);
    }

    function
        .blocks
        .retain(|block| reachable.contains(&block.id));

    renumber_blocks(function);

    Ok(())
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
                    | IrInstruction::StackAllocStruct { .. }
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
            | IrInstruction::LoadLocal { .. }
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
        | IrInstruction::StackAllocStruct { destination, .. }
        | IrInstruction::Phi { destination, .. } => Some(*destination),

        IrInstruction::Call { destination, .. } => *destination,

        IrInstruction::StoreLocal { .. } | IrInstruction::StoreField { .. } => None,
    }
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
    let predecessors = build_predecessors(function);

    let mut in_facts = HashMap::<BlockId, HashMap<ValueId, i64>>::new();
    let mut out_facts = HashMap::<BlockId, HashMap<ValueId, i64>>::new();

    in_facts.insert(function.entry, HashMap::new());

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
                transfer_fold_facts(instruction, &mut facts);
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

    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &mut block.instructions {
            let replacement = match instruction {
                IrInstruction::ConstInt { destination, value } => {
                    facts.insert(*destination, *value);
                    None
                }

                IrInstruction::Binary {
                    destination,
                    op,
                    left,
                    right,
                } => {
                    let left_value = facts.get(left).copied();
                    let right_value = facts.get(right).copied();

                    match (left_value, right_value) {
                        (Some(left), Some(right)) => {
                            fold_integer_binary(*destination, *op, left, right)
                        }
                        _ => {
                            facts.remove(destination);
                            None
                        }
                    }
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
                if let IrInstruction::ConstInt { destination, value } = &replacement {
                    facts.insert(*destination, *value);
                }

                *instruction = replacement;
            }
        }
    }

    Ok(())
}

fn transfer_fold_facts(instruction: &IrInstruction, facts: &mut HashMap<ValueId, i64>) {
    match instruction {
        IrInstruction::ConstInt { destination, value } => {
            facts.insert(*destination, *value);
        }

        IrInstruction::Binary {
            destination,
            op,
            left,
            right,
        } => {
            let Some(left_value) = facts.get(left).copied() else {
                facts.remove(destination);
                return;
            };

            let Some(right_value) = facts.get(right).copied() else {
                facts.remove(destination);
                return;
            };

            match fold_integer_binary(*destination, *op, left_value, right_value) {
                Some(IrInstruction::ConstInt { value, .. }) => {
                    facts.insert(*destination, value);
                }

                _ => {
                    facts.remove(destination);
                }
            }
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

fn fold_integer_binary(
    destination: ValueId,
    op: IrBinaryOp,
    left: i64,
    right: i64,
) -> Option<IrInstruction> {
    match op {
        IrBinaryOp::Add => left
            .checked_add(right)
            .map(|value| IrInstruction::ConstInt { destination, value }),

        IrBinaryOp::Subtract => left
            .checked_sub(right)
            .map(|value| IrInstruction::ConstInt { destination, value }),

        IrBinaryOp::Multiply => left
            .checked_mul(right)
            .map(|value| IrInstruction::ConstInt { destination, value }),

        IrBinaryOp::Divide => {
            if right == 0 {
                None
            } else {
                left.checked_div(right)
                    .map(|value| IrInstruction::ConstInt { destination, value })
            }
        }

        IrBinaryOp::Equal => Some(IrInstruction::ConstBool {
            destination,
            value: left == right,
        }),
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

pub fn forward_local_stores(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = forward_local_stores_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn forward_local_stores_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    let mut in_facts = HashMap::<BlockId, HashMap<LocalId, ValueId>>::new();
    let mut out_facts = HashMap::<BlockId, HashMap<LocalId, ValueId>>::new();

    in_facts.insert(function.entry, HashMap::new());

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
                    intersect_local_facts(&preds, &out_facts)
                }
            };

            if in_facts.get(&block_id) != Some(&new_in) {
                in_facts.insert(block_id, new_in.clone());
                changed = true;
            }

            let mut facts = new_in;

            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::StoreLocal { local, value } => {
                        facts.insert(*local, *value);
                    }

                    IrInstruction::LoadLocal { destination, local } => {
                        facts.insert(*local, *destination);
                    }

                    _ => {}
                }
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

    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &mut block.instructions {
            let replacement = match instruction {
                IrInstruction::LoadLocal { destination, local } => {
                    facts.get(local).copied().map(|source| IrInstruction::Copy {
                        destination: *destination,
                        source,
                    })
                }

                _ => None,
            };

            if let Some(replacement) = replacement {
                *instruction = replacement;
            }

            match instruction {
                IrInstruction::StoreLocal { local, value } => {
                    facts.insert(*local, *value);
                }

                IrInstruction::LoadLocal { destination, local } => {
                    facts.insert(*local, *destination);
                }

                _ => {}
            }
        }
    }

    Ok(())
}

fn intersect_local_facts(
    predecessors: &[BlockId],
    out_facts: &HashMap<BlockId, HashMap<LocalId, ValueId>>,
) -> HashMap<LocalId, ValueId> {
    let Some(first) = predecessors.first() else {
        return HashMap::new();
    };

    let Some(first_facts) = out_facts.get(first) else {
        return HashMap::new();
    };

    let mut result = first_facts.clone();

    for predecessor in &predecessors[1..] {
        let Some(facts) = out_facts.get(predecessor) else {
            result.clear();
            break;
        };

        result.retain(|local, value| facts.get(local) == Some(value));
    }

    result
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
        | IrInstruction::StackAllocStruct { .. }
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

pub fn simplify_constant_branches(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = simplify_constant_branches_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn simplify_constant_branches_function(
    function: &mut IrFunction,
) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    let mut in_facts = HashMap::<BlockId, HashMap<ValueId, bool>>::new();
    let mut out_facts = HashMap::<BlockId, HashMap<ValueId, bool>>::new();

    in_facts.insert(function.entry, HashMap::new());

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
                    intersect_bool_facts(&preds, &out_facts)
                }
            };

            if in_facts.get(&block_id) != Some(&new_in) {
                in_facts.insert(block_id, new_in.clone());
                changed = true;
            }

            let mut facts = new_in;

            for instruction in &block.instructions {
                transfer_bool_fact(instruction, &mut facts);
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

    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &block.instructions {
            transfer_bool_fact(instruction, &mut facts);
        }

        if let Terminator::Branch {
            condition,
            then_block,
            else_block,
        } = block.terminator
        {
            if let Some(value) = facts.get(&condition).copied() {
                block.terminator = if value {
                    Terminator::Jump(then_block)
                } else {
                    Terminator::Jump(else_block)
                };
            }
        }
    }

    Ok(())
}

fn intersect_bool_facts(
    predecessors: &[BlockId],
    out_facts: &HashMap<BlockId, HashMap<ValueId, bool>>,
) -> HashMap<ValueId, bool> {
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

fn transfer_bool_fact(instruction: &IrInstruction, facts: &mut HashMap<ValueId, bool>) {
    match instruction {
        IrInstruction::ConstBool { destination, value } => {
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

pub fn remove_empty_blocks(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = remove_empty_blocks_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn remove_empty_blocks_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    loop {
        let mut target = None;

        for block in &function.blocks {
            if block.id == function.entry {
                continue;
            }

            if block.instructions.is_empty() {
                if let Terminator::Jump(destination) = block.terminator {
                    if destination != block.id {
                        target = Some((block.id, destination));
                        break;
                    }
                }
            }
        }

        let Some((removed, destination)) = target else {
            break;
        };

        for block in &mut function.blocks {
            rewrite_block_target(&mut block.terminator, removed, destination);
        }

        function.blocks.retain(|block| block.id != removed);
    }

    renumber_blocks(function);

    Ok(())
}

fn rewrite_block_target(terminator: &mut Terminator, removed: BlockId, destination: BlockId) {
    match terminator {
        Terminator::Jump(target) => {
            if *target == removed {
                *target = destination;
            }
        }

        Terminator::Branch {
            then_block,
            else_block,
            ..
        } => {
            if *then_block == removed {
                *then_block = destination;
            }

            if *else_block == removed {
                *else_block = destination;
            }
        }

        Terminator::Return { .. } | Terminator::Unreachable => {}
    }
}

fn renumber_blocks(function: &mut IrFunction) {
    let mut block_id_map = HashMap::<BlockId, BlockId>::new();

    for (index, block) in function.blocks.iter().enumerate() {
        block_id_map.insert(block.id, BlockId(index));
    }

    for block in &mut function.blocks {
        block.id = *block_id_map
            .get(&block.id)
            .expect("block must have a new block id");

        match &mut block.terminator {
            Terminator::Jump(target) => {
                *target = *block_id_map.get(target).expect("jump target must exist");
            }

            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                *then_block = *block_id_map.get(then_block).expect("then block must exist");

                *else_block = *block_id_map.get(else_block).expect("else block must exist");
            }

            Terminator::Return { .. } | Terminator::Unreachable => {}
        }
    }

    function.entry = *block_id_map
        .get(&function.entry)
        .expect("entry block must exist");
}

pub fn simplify_redundant_branches(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = simplify_redundant_branches_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn simplify_redundant_branches_function(
    function: &mut IrFunction,
) -> Result<(), Vec<CompilerError>> {
    for block in &mut function.blocks {
        if let Terminator::Branch {
            then_block,
            else_block,
            ..
        } = block.terminator
        {
            if then_block == else_block {
                block.terminator = Terminator::Jump(then_block);
            }
        }
    }

    Ok(())
}

pub fn thread_jumps(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = thread_jumps_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn thread_jumps_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    loop {
        let mut changed = false;

        let destinations: HashMap<BlockId, BlockId> = function
            .blocks
            .iter()
            .filter_map(|block| {
                if block.instructions.is_empty() {
                    if let Terminator::Jump(destination) = block.terminator {
                        if destination != block.id {
                            return Some((block.id, destination));
                        }
                    }
                }

                None
            })
            .collect();

        for block in &mut function.blocks {
            match &mut block.terminator {
                Terminator::Jump(target) => {
                    if let Some(destination) = destinations.get(target) {
                        *target = *destination;
                        changed = true;
                    }
                }

                Terminator::Branch {
                    then_block,
                    else_block,
                    ..
                } => {
                    if let Some(destination) = destinations.get(then_block) {
                        *then_block = *destination;
                        changed = true;
                    }

                    if let Some(destination) = destinations.get(else_block) {
                        *else_block = *destination;
                        changed = true;
                    }
                }

                Terminator::Return { .. } | Terminator::Unreachable => {}
            }
        }

        if !changed {
            break;
        }
    }

    Ok(())
}

pub fn simplify_algebraic(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = simplify_algebraic_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn simplify_algebraic_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    let mut in_facts = HashMap::<BlockId, HashMap<ValueId, i64>>::new();
    let mut out_facts = HashMap::<BlockId, HashMap<ValueId, i64>>::new();

    in_facts.insert(function.entry, HashMap::new());

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

    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &mut block.instructions {
            let replacement = match instruction {
                IrInstruction::Binary {
                    destination,
                    op,
                    left,
                    right,
                } => {
                    let left_constant = facts.get(left).copied();
                    let right_constant = facts.get(right).copied();
                    if *op == IrBinaryOp::Equal && left == right {
                        Some(IrInstruction::ConstBool {
                            destination: *destination,
                            value: true,
                        })
                    } else {
                        match (op, left_constant, right_constant) {
                            (IrBinaryOp::Add, _, Some(0)) => Some(IrInstruction::Copy {
                                destination: *destination,
                                source: *left,
                            }),

                            (IrBinaryOp::Add, Some(0), _) => Some(IrInstruction::Copy {
                                destination: *destination,
                                source: *right,
                            }),

                            (IrBinaryOp::Subtract, _, Some(0)) => Some(IrInstruction::Copy {
                                destination: *destination,
                                source: *left,
                            }),

                            (IrBinaryOp::Multiply, _, Some(1)) => Some(IrInstruction::Copy {
                                destination: *destination,
                                source: *left,
                            }),

                            (IrBinaryOp::Multiply, Some(1), _) => Some(IrInstruction::Copy {
                                destination: *destination,
                                source: *right,
                            }),

                            (IrBinaryOp::Multiply, _, Some(0)) => Some(IrInstruction::ConstInt {
                                destination: *destination,
                                value: 0,
                            }),

                            (IrBinaryOp::Multiply, Some(0), _) => Some(IrInstruction::ConstInt {
                                destination: *destination,
                                value: 0,
                            }),

                            (IrBinaryOp::Divide, _, Some(1)) => Some(IrInstruction::Copy {
                                destination: *destination,
                                source: *left,
                            }),

                            _ => None,
                        }
                    }
                }

                _ => None,
            };

            if let Some(replacement) = replacement {
                *instruction = replacement;
            }

            transfer_constant_fact(instruction, &mut facts);
        }
    }

    Ok(())
}

pub fn eliminate_redundant_copies(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = eliminate_redundant_copies_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn eliminate_redundant_copies_function(
    function: &mut IrFunction,
) -> Result<(), Vec<CompilerError>> {
    for block in &mut function.blocks {
        block.instructions.retain(|instruction| {
            !matches!(
                instruction,
                IrInstruction::Copy {
                    destination,
                    source,
                } if destination == source
            )
        });
    }

    Ok(())
}

pub fn eliminate_redundant_loads(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = eliminate_redundant_loads_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn eliminate_redundant_loads_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    let mut in_facts = HashMap::<BlockId, HashMap<LocalId, ValueId>>::new();
    let mut out_facts = HashMap::<BlockId, HashMap<LocalId, ValueId>>::new();

    in_facts.insert(function.entry, HashMap::new());

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
                    intersect_local_facts(&preds, &out_facts)
                }
            };

            if in_facts.get(&block_id) != Some(&new_in) {
                in_facts.insert(block_id, new_in.clone());
                changed = true;
            }

            let mut facts = new_in;

            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::StoreLocal { local, value } => {
                        facts.insert(*local, *value);
                    }

                    IrInstruction::LoadLocal { destination, local } => {
                        facts.insert(*local, *destination);
                    }

                    _ => {}
                }
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

    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &mut block.instructions {
            match instruction {
                IrInstruction::LoadLocal { destination, local } => {
                    if let Some(source) = facts.get(local).copied() {
                        let destination = *destination;
                        let local = *local;

                        *instruction = IrInstruction::Copy {
                            destination,
                            source,
                        };

                        facts.insert(local, destination);
                    } else {
                        facts.insert(*local, *destination);
                    }
                }

                IrInstruction::StoreLocal { local, value } => {
                    facts.insert(*local, *value);
                }

                _ => {}
            }
        }
    }

    Ok(())
}

pub fn eliminate_dead_stores(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = eliminate_dead_stores_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn eliminate_dead_stores_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let mut successors = HashMap::<BlockId, Vec<BlockId>>::new();

    for block in &function.blocks {
        let targets = match block.terminator {
            Terminator::Jump(destination) => vec![destination],

            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                if then_block == else_block {
                    vec![then_block]
                } else {
                    vec![then_block, else_block]
                }
            }

            Terminator::Return { .. } | Terminator::Unreachable => Vec::new(),
        };

        successors.insert(block.id, targets);
    }

    let mut live_in = HashMap::<BlockId, HashSet<LocalId>>::new();
    let mut live_out = HashMap::<BlockId, HashSet<LocalId>>::new();

    for block in &function.blocks {
        live_in.insert(block.id, HashSet::new());
        live_out.insert(block.id, HashSet::new());
    }

    loop {
        let mut changed = false;

        for block in function.blocks.iter().rev() {
            let mut new_live_out = HashSet::new();

            if let Some(block_successors) = successors.get(&block.id) {
                for successor in block_successors {
                    if let Some(successor_live_in) = live_in.get(successor) {
                        new_live_out.extend(successor_live_in);
                    }
                }
            }

            let mut live = new_live_out.clone();

            for instruction in block.instructions.iter().rev() {
                match instruction {
                    IrInstruction::LoadLocal { local, .. } => {
                        live.insert(*local);
                    }

                    IrInstruction::StoreLocal { local, .. } => {
                        live.remove(local);
                    }

                    _ => {}
                }
            }

            if live_out.get(&block.id) != Some(&new_live_out) {
                live_out.insert(block.id, new_live_out);
                changed = true;
            }

            if live_in.get(&block.id) != Some(&live) {
                live_in.insert(block.id, live);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    for block in &mut function.blocks {
        let mut live = live_out.get(&block.id).cloned().unwrap_or_default();

        let mut remove = HashSet::<usize>::new();

        for (index, instruction) in block.instructions.iter().enumerate().rev() {
            match instruction {
                IrInstruction::LoadLocal { local, .. } => {
                    live.insert(*local);
                }

                IrInstruction::StoreLocal { local, .. } => {
                    if live.contains(local) {
                        live.remove(local);
                    } else {
                        remove.insert(index);
                    }
                }

                _ => {}
            }
        }

        let mut index = 0;

        block.instructions.retain(|_| {
            let keep = !remove.contains(&index);
            index += 1;
            keep
        });
    }

    Ok(())
}

pub fn merge_linear_blocks(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = merge_linear_blocks_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn merge_linear_blocks_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    loop {
        let predecessors = build_predecessors(function);

        let Some((source, destination)) = function.blocks.iter().find_map(|block| {
            let destination = match block.terminator {
                Terminator::Jump(destination) => destination,
                _ => return None,
            };

            if destination == block.id || destination == function.entry {
                return None;
            }

            let destination_predecessors = predecessors.get(&destination)?;

            if destination_predecessors.len() == 1 && destination_predecessors[0] == block.id {
                Some((block.id, destination))
            } else {
                None
            }
        }) else {
            break;
        };

        let source_index = function
            .blocks
            .iter()
            .position(|block| block.id == source)
            .expect("source block must exist");

        let destination_index = function
            .blocks
            .iter()
            .position(|block| block.id == destination)
            .expect("destination block must exist");

        let destination_block = function.blocks.remove(destination_index);

        let source_index = function
            .blocks
            .iter()
            .position(|block| block.id == source)
            .expect("source block must still exist");

        function.blocks[source_index]
            .instructions
            .extend(destination_block.instructions);

        function.blocks[source_index].terminator = destination_block.terminator;
    }

    renumber_blocks(function);

    Ok(())
}

pub fn eliminate_redundant_field_loads(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = eliminate_redundant_field_loads_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn eliminate_redundant_field_loads_function(
    function: &mut IrFunction,
) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    type FieldKey = (ValueId, usize);
    type FieldFacts = HashMap<FieldKey, ValueId>;

    let mut in_facts = HashMap::<BlockId, FieldFacts>::new();
    let mut out_facts = HashMap::<BlockId, FieldFacts>::new();

    in_facts.insert(function.entry, HashMap::new());

    // Compute the facts available at the entry and exit of every block.
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
                    intersect_field_facts(&preds, &out_facts)
                }
            };

            if in_facts.get(&block_id) != Some(&new_in) {
                in_facts.insert(block_id, new_in.clone());
                changed = true;
            }

            let mut facts = new_in;

            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::LoadField {
                        destination,
                        receiver,
                        field,
                    } => {
                        facts.insert((*receiver, *field), *destination);
                    }

                    IrInstruction::StoreField {
                        receiver, field, ..
                    } => {
                        facts.remove(&(*receiver, *field));
                    }

                    IrInstruction::Call { .. } => {
                        // A call may mutate any object.
                        facts.clear();
                    }

                    _ => {}
                }
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

    // Rewrite loads using the facts available at each block.
    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &mut block.instructions {
            match instruction {
                IrInstruction::LoadField {
                    destination,
                    receiver,
                    field,
                } => {
                    let destination_id = *destination;
                    let key = (*receiver, *field);

                    if let Some(source) = facts.get(&key).copied() {
                        *instruction = IrInstruction::Copy {
                            destination: destination_id,
                            source,
                        };
                    } else {
                        facts.insert(key, destination_id);
                    }
                }

                IrInstruction::StoreField {
                    receiver, field, ..
                } => {
                    facts.remove(&(*receiver, *field));
                }

                IrInstruction::Call { .. } => {
                    facts.clear();
                }

                _ => {}
            }
        }
    }

    Ok(())
}

fn intersect_field_facts(
    predecessors: &[BlockId],
    out_facts: &HashMap<BlockId, HashMap<(ValueId, usize), ValueId>>,
) -> HashMap<(ValueId, usize), ValueId> {
    let Some(first) = predecessors.first() else {
        return HashMap::new();
    };

    let Some(first_facts) = out_facts.get(first) else {
        return HashMap::new();
    };

    let mut result = first_facts.clone();

    for predecessor in &predecessors[1..] {
        let Some(facts) = out_facts.get(predecessor) else {
            result.clear();
            break;
        };

        result.retain(|key, value| facts.get(key) == Some(value));
    }

    result
}

pub fn forward_field_stores(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = forward_field_stores_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn forward_field_stores_function(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let predecessors = build_predecessors(function);

    type FieldKey = (ValueId, usize);
    type FieldFacts = HashMap<FieldKey, ValueId>;

    let mut in_facts = HashMap::<BlockId, FieldFacts>::new();
    let mut out_facts = HashMap::<BlockId, FieldFacts>::new();

    in_facts.insert(function.entry, HashMap::new());

    // Compute the field values known at every block boundary.
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
                    intersect_field_facts(&preds, &out_facts)
                }
            };

            if in_facts.get(&block_id) != Some(&new_in) {
                in_facts.insert(block_id, new_in.clone());
                changed = true;
            }

            let mut facts = new_in;

            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::StoreField {
                        receiver,
                        field,
                        value,
                    } => {
                        facts.insert((*receiver, *field), *value);
                    }

                    IrInstruction::LoadField { .. } => {}

                    IrInstruction::Call { .. } => {
                        // Calls may mutate arbitrary objects.
                        facts.clear();
                    }

                    _ => {}
                }
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

    // Forward stores into subsequent loads.
    for block in &mut function.blocks {
        let mut facts = in_facts.get(&block.id).cloned().unwrap_or_default();

        for instruction in &mut block.instructions {
            match instruction {
                IrInstruction::LoadField {
                    destination,
                    receiver,
                    field,
                } => {
                    let destination_id = *destination;
                    let key = (*receiver, *field);

                    if let Some(source) = facts.get(&key).copied() {
                        *instruction = IrInstruction::Copy {
                            destination: destination_id,
                            source,
                        };
                    } else {
                        // Do not cache this load here. The dedicated
                        // redundant-field-load pass handles load caching.
                        facts.remove(&key);
                    }
                }

                IrInstruction::StoreField {
                    receiver,
                    field,
                    value,
                } => {
                    facts.insert((*receiver, *field), *value);
                }

                IrInstruction::Call { .. } => {
                    facts.clear();
                }

                _ => {}
            }
        }
    }

    Ok(())
}

pub fn eliminate_dead_field_stores(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = eliminate_dead_field_stores_function(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn eliminate_dead_field_stores_function(
    function: &mut IrFunction,
) -> Result<(), Vec<CompilerError>> {
    type FieldKey = (ValueId, usize);

    let mut successors = HashMap::<BlockId, Vec<BlockId>>::new();

    for block in &function.blocks {
        let targets = match block.terminator {
            Terminator::Jump(destination) => vec![destination],

            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                if then_block == else_block {
                    vec![then_block]
                } else {
                    vec![then_block, else_block]
                }
            }

            Terminator::Return { .. } | Terminator::Unreachable => Vec::new(),
        };

        successors.insert(block.id, targets);
    }

    let mut live_in = HashMap::<BlockId, HashSet<FieldKey>>::new();
    let mut live_out = HashMap::<BlockId, HashSet<FieldKey>>::new();

    for block in &function.blocks {
        live_in.insert(block.id, HashSet::new());
        live_out.insert(block.id, HashSet::new());
    }

    // Backward field liveness.
    //
    // A call is treated conservatively: it may inspect any field of any
    // object, so every StoreField before a call must be preserved.
    let mut call_live_in = HashMap::<BlockId, bool>::new();
    let mut call_live_out = HashMap::<BlockId, bool>::new();

    for block in &function.blocks {
        call_live_in.insert(block.id, false);
        call_live_out.insert(block.id, false);
    }

    loop {
        let mut changed = false;

        for block in function.blocks.iter().rev() {
            let mut new_live_out = HashSet::new();
            let mut new_call_live_out = false;

            if let Some(block_successors) = successors.get(&block.id) {
                for successor in block_successors {
                    if let Some(successor_live_in) = live_in.get(successor) {
                        new_live_out.extend(successor_live_in);
                    }

                    if call_live_in.get(successor).copied().unwrap_or(false) {
                        new_call_live_out = true;
                    }
                }
            }

            let mut live = new_live_out.clone();
            let mut call_live = new_call_live_out;

            for instruction in block.instructions.iter().rev() {
                match instruction {
                    IrInstruction::LoadField {
                        receiver, field, ..
                    } => {
                        live.insert((*receiver, *field));
                    }

                    IrInstruction::StoreField {
                        receiver, field, ..
                    } => {
                        let key = (*receiver, *field);

                        if !call_live {
                            live.remove(&key);
                        }
                    }

                    IrInstruction::Call { .. } => {
                        call_live = true;
                    }

                    _ => {}
                }
            }

            if live_in.get(&block.id) != Some(&live) {
                live_in.insert(block.id, live);
                changed = true;
            }

            if live_out.get(&block.id) != Some(&new_live_out) {
                live_out.insert(block.id, new_live_out);
                changed = true;
            }

            if call_live_in.get(&block.id) != Some(&call_live) {
                call_live_in.insert(block.id, call_live);
                changed = true;
            }

            if call_live_out.get(&block.id) != Some(&new_call_live_out) {
                call_live_out.insert(block.id, new_call_live_out);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    // Remove stores whose field value is never observed.
    for block in &mut function.blocks {
        let mut live = live_out.get(&block.id).cloned().unwrap_or_default();
        let mut call_live = call_live_out.get(&block.id).copied().unwrap_or(false);

        let mut remove = HashSet::<usize>::new();

        for (index, instruction) in block.instructions.iter().enumerate().rev() {
            match instruction {
                IrInstruction::LoadField {
                    receiver, field, ..
                } => {
                    live.insert((*receiver, *field));
                }

                IrInstruction::StoreField {
                    receiver, field, ..
                } => {
                    let key = (*receiver, *field);

                    if !call_live && !live.contains(&key) {
                        remove.insert(index);
                    } else if !call_live {
                        live.remove(&key);
                    }
                }

                IrInstruction::Call { .. } => {
                    call_live = true;
                }

                _ => {}
            }
        }

        let mut index = 0;

        block.instructions.retain(|_| {
            let keep = !remove.contains(&index);
            index += 1;
            keep
        });
    }

    Ok(())
}

pub fn eliminate_dead_stack_allocs(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    for function in &mut program.functions {
        let mut used = HashSet::<ValueId>::new();

        // Values used by terminators are live.
        for block in &function.blocks {
            match &block.terminator {
                Terminator::Branch { condition, .. } => {
                    used.insert(*condition);
                }

                Terminator::Return { value } => {
                    if let Some(value) = value {
                        used.insert(*value);
                    }
                }

                Terminator::Jump(_) | Terminator::Unreachable => {}
            }
        }

        // Collect every value consumed by an instruction.
        for block in &function.blocks {
            for instruction in &block.instructions {
                match instruction {
                    IrInstruction::Copy { source, .. } => {
                        used.insert(*source);
                    }

                    IrInstruction::StructCopy { source, .. } => {
                        used.insert(*source);
                    }

                    IrInstruction::StoreLocal { value, .. } => {
                        used.insert(*value);
                    }

                    IrInstruction::StoreField {
                        receiver, value, ..
                    } => {
                        used.insert(*receiver);
                        used.insert(*value);
                    }

                    IrInstruction::LoadField { receiver, .. } => {
                        used.insert(*receiver);
                    }

                    IrInstruction::Binary { left, right, .. } => {
                        used.insert(*left);
                        used.insert(*right);
                    }

                    IrInstruction::Call { arguments, .. } => {
                        used.extend(arguments.iter().copied());
                    }

                    IrInstruction::Phi { sources, .. } => {
                        used.extend(sources.iter().map(|(_, value)| *value));
                    }

                    IrInstruction::Parameter { .. }
                    | IrInstruction::ConstInt { .. }
                    | IrInstruction::ConstString { .. }
                    | IrInstruction::ConstBool { .. }
                    | IrInstruction::LoadLocal { .. }
                    | IrInstruction::AllocStruct { .. }
                    | IrInstruction::StackAllocStruct { .. } => {}
                }
            }
        }

        for block in &mut function.blocks {
            block.instructions.retain(|instruction| match instruction {
                IrInstruction::StackAllocStruct { destination, .. } => used.contains(destination),

                _ => true,
            });
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ir::ir::{
        BasicBlock, IrFunction, IrInstruction, IrProgram, IrType, Terminator, ValueId,
    };
    use crate::ir::{BlockId, IrField, IrLocal, IrStruct};
    use crate::semantic::symbols::{FunctionId, LocalId, StructId};

    #[test]
    fn eliminates_unused_stack_alloc() {
        let mut program = IrProgram {
            structs: vec![IrStruct {
                id: StructId(0),
                name: "Test".to_string(),
                base: None,
                fields: vec![],
            }],
            functions: vec![IrFunction {
                id: Some(FunctionId(0)),
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::StackAllocStruct {
                        destination: ValueId(0),
                        struct_id: StructId(0),
                    }],
                    terminator: Terminator::Return { value: None },
                }],
            }],
        };

        eliminate_dead_stack_allocs(&mut program)
            .expect("dead stack allocation elimination should succeed");

        assert!(program.functions[0].blocks[0].instructions.is_empty());
    }

    #[test]
    fn preserves_stack_alloc_used_by_store_field() {
        let mut program = IrProgram {
            structs: vec![IrStruct {
                id: StructId(0),
                name: "Test".to_string(),
                base: None,
                fields: vec![IrField {
                    name: "value".to_string(),
                    ty: IrType::Int,
                }],
            }],
            functions: vec![IrFunction {
                id: Some(FunctionId(0)),
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::StackAllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return { value: None },
                }],
            }],
        };

        eliminate_dead_stack_allocs(&mut program)
            .expect("dead stack allocation elimination should succeed");

        assert!(matches!(
            program.functions[0].blocks[0].instructions.as_slice(),
            [
                IrInstruction::StackAllocStruct {
                    destination: ValueId(0),
                    struct_id: StructId(0),
                },
                IrInstruction::ConstInt {
                    destination: ValueId(1),
                    value: 42,
                },
                IrInstruction::StoreField {
                    receiver: ValueId(0),
                    field: 0,
                    value: ValueId(1),
                }
            ]
        ));
    }

    #[test]
    fn preserves_stack_alloc_passed_to_call() {
        let mut program = IrProgram {
            structs: vec![IrStruct {
                id: StructId(0),
                name: "Test".to_string(),
                base: None,
                fields: Vec::new(),
            }],
            functions: vec![IrFunction {
                id: Some(FunctionId(0)),
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::StackAllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::Call {
                            destination: None,
                            function: FunctionId(1),
                            arguments: vec![ValueId(0)],
                        },
                    ],
                    terminator: Terminator::Return { value: None },
                }],
            }],
        };

        eliminate_dead_stack_allocs(&mut program)
            .expect("dead stack allocation elimination should succeed");

        assert!(matches!(
            &program.functions[0].blocks[0].instructions[0],
            IrInstruction::StackAllocStruct {
                destination: ValueId(0),
                struct_id: StructId(0),
            }
        ));
    }

    #[test]
    fn does_not_eliminate_alloc_struct() {
        let mut program = IrProgram {
            structs: vec![IrStruct {
                id: StructId(0),
                name: "Test".to_string(),
                base: None,
                fields: Vec::new(),
            }],
            functions: vec![IrFunction {
                id: Some(FunctionId(0)),
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::AllocStruct {
                        destination: ValueId(0),
                        struct_id: StructId(0),
                    }],
                    terminator: Terminator::Return { value: None },
                }],
            }],
        };

        eliminate_dead_stack_allocs(&mut program)
            .expect("dead stack allocation elimination should succeed");

        assert!(matches!(
            &program.functions[0].blocks[0].instructions[0],
            IrInstruction::AllocStruct {
                destination: ValueId(0),
                struct_id: StructId(0),
            }
        ));
    }

    #[test]
    fn eliminates_dead_field_store() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                }],
            }],
        };

        eliminate_dead_field_stores(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(!instructions
            .iter()
            .any(|instruction| { matches!(instruction, IrInstruction::StoreField { .. }) }));
    }

    #[test]
    fn eliminates_only_unobserved_field_store() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 10,
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(2),
                            value: 20,
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 1,
                            value: ValueId(2),
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(3),
                            receiver: ValueId(0),
                            field: 1,
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(3)),
                    },
                }],
            }],
        };

        eliminate_dead_field_stores(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(!instructions.iter().any(|instruction| {
            matches!(
                instruction,
                IrInstruction::StoreField {
                    receiver: ValueId(0),
                    field: 0,
                    ..
                }
            )
        }));

        assert!(instructions.iter().any(|instruction| {
            matches!(
                instruction,
                IrInstruction::StoreField {
                    receiver: ValueId(0),
                    field: 1,
                    value: ValueId(2),
                }
            )
        }));
    }

    #[test]
    fn preserves_field_store_before_call() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        },
                        IrInstruction::Call {
                            destination: None,
                            function: FunctionId(0),
                            arguments: vec![ValueId(0)],
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                }],
            }],
        };

        eliminate_dead_field_stores(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(instructions.iter().any(|instruction| {
            matches!(
                instruction,
                IrInstruction::StoreField {
                    receiver: ValueId(0),
                    field: 0,
                    value: ValueId(1),
                }
            )
        }));
    }

    #[test]
    fn forwards_field_store_into_load() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
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
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        forward_field_stores(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            &instructions[3],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(1),
            }
        ));
    }

    #[test]
    fn does_not_forward_field_store_after_overwrite() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 10,
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(2),
                            value: 20,
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(2),
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(3),
                            receiver: ValueId(0),
                            field: 0,
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(3)),
                    },
                }],
            }],
        };

        forward_field_stores(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            &instructions[5],
            IrInstruction::Copy {
                destination: ValueId(3),
                source: ValueId(2),
            }
        ));
    }

    #[test]
    fn does_not_forward_field_store_across_call() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        },
                        IrInstruction::Call {
                            destination: None,
                            function: FunctionId(0),
                            arguments: Vec::new(),
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(2),
                            receiver: ValueId(0),
                            field: 0,
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        forward_field_stores(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            &instructions[4],
            IrInstruction::LoadField {
                destination: ValueId(2),
                receiver: ValueId(0),
                field: 0,
            }
        ));
    }

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

    #[test]
    fn folds_equal_to_const_bool_true() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "equal_fold_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Bool,
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
                        value: 42,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Equal,
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

        assert!(matches!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::ConstBool {
                destination: ValueId(2),
                value: true,
            }
        ));
    }

    #[test]
    fn folds_equal_to_const_bool_false() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "equal_fold_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Bool,
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
                        value: 99,
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Equal,
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

        assert!(matches!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::ConstBool {
                destination: ValueId(2),
                value: false,
            }
        ));
    }

    #[test]
    fn preserves_call_even_when_result_is_unused() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::Call {
                        destination: Some(ValueId(1)),
                        function: FunctionId(0),
                        arguments: Vec::new(),
                    }],
                    terminator: Terminator::Return { value: None },
                }],
            }],
        };

        eliminate_dead_code(&mut program).unwrap();

        assert!(matches!(
            program.functions[0].blocks[0].instructions.as_slice(),
            [IrInstruction::Call { .. }]
        ));
    }

    #[test]
    fn preserves_value_used_by_successor_block() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
                        }],
                        terminator: Terminator::Jump(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![IrInstruction::Copy {
                            destination: ValueId(2),
                            source: ValueId(1),
                        }],
                        terminator: Terminator::Return {
                            value: Some(ValueId(2)),
                        },
                    },
                ],
            }],
        };

        eliminate_dead_code(&mut program).unwrap();

        assert!(matches!(
            program.functions[0].blocks[0].instructions.as_slice(),
            [IrInstruction::ConstInt {
                destination: ValueId(1),
                value: 42
            }]
        ));

        assert!(matches!(
            program.functions[0].blocks[1].instructions.as_slice(),
            [IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(1)
            }]
        ));
    }

    #[test]
    fn simplifies_true_constant_branch() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![IrInstruction::ConstBool {
                            destination: ValueId(0),
                            value: true,
                        }],
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
            }],
        };

        simplify_constant_branches(&mut program).unwrap();

        assert_eq!(
            program.functions[0].blocks[0].terminator,
            Terminator::Jump(BlockId(1))
        );
    }

    #[test]
    fn simplifies_false_constant_branch() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![IrInstruction::ConstBool {
                            destination: ValueId(0),
                            value: false,
                        }],
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
            }],
        };

        simplify_constant_branches(&mut program).unwrap();

        assert_eq!(
            program.functions[0].blocks[0].terminator,
            Terminator::Jump(BlockId(2))
        );
    }

    #[test]
    fn simplifies_constant_branch_through_copy() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![
                            IrInstruction::ConstBool {
                                destination: ValueId(0),
                                value: true,
                            },
                            IrInstruction::Copy {
                                destination: ValueId(1),
                                source: ValueId(0),
                            },
                        ],
                        terminator: Terminator::Branch {
                            condition: ValueId(1),
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
            }],
        };

        simplify_constant_branches(&mut program).unwrap();

        assert_eq!(
            program.functions[0].blocks[0].terminator,
            Terminator::Jump(BlockId(1))
        );
    }

    #[test]
    fn simplifies_constant_branch_when_predecessors_agree() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![IrInstruction::ConstBool {
                            destination: ValueId(0),
                            value: true,
                        }],
                        terminator: Terminator::Branch {
                            condition: ValueId(0),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![IrInstruction::ConstBool {
                            destination: ValueId(1),
                            value: true,
                        }],
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![IrInstruction::ConstBool {
                            destination: ValueId(1),
                            value: true,
                        }],
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch {
                            condition: ValueId(1),
                            then_block: BlockId(4),
                            else_block: BlockId(5),
                        },
                    },
                    BasicBlock {
                        id: BlockId(4),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    },
                    BasicBlock {
                        id: BlockId(5),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    },
                ],
            }],
        };

        simplify_constant_branches(&mut program).unwrap();

        assert_eq!(
            program.functions[0].blocks[3].terminator,
            Terminator::Jump(BlockId(4))
        );
    }

    #[test]
    fn does_not_simplify_constant_branch_when_predecessors_disagree() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![IrInstruction::ConstBool {
                            destination: ValueId(0),
                            value: true,
                        }],
                        terminator: Terminator::Branch {
                            condition: ValueId(0),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![IrInstruction::ConstBool {
                            destination: ValueId(1),
                            value: true,
                        }],
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![IrInstruction::ConstBool {
                            destination: ValueId(1),
                            value: false,
                        }],
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: Vec::new(),
                        terminator: Terminator::Branch {
                            condition: ValueId(1),
                            then_block: BlockId(4),
                            else_block: BlockId(5),
                        },
                    },
                    BasicBlock {
                        id: BlockId(4),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    },
                    BasicBlock {
                        id: BlockId(5),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    },
                ],
            }],
        };

        simplify_constant_branches(&mut program).unwrap();

        assert_eq!(
            program.functions[0].blocks[3].terminator,
            Terminator::Branch {
                condition: ValueId(1),
                then_block: BlockId(4),
                else_block: BlockId(5),
            }
        );
    }

    #[test]
    fn removes_unreachable_blocks_and_rewrites_block_ids() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(2)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![IrInstruction::ConstInt {
                            destination: ValueId(0),
                            value: 999,
                        }],
                        terminator: Terminator::Return {
                            value: Some(ValueId(0)),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
                        }],
                        terminator: Terminator::Return {
                            value: Some(ValueId(1)),
                        },
                    },
                ],
            }],
        };

        remove_unreachable_blocks(&mut program).unwrap();

        let function = &program.functions[0];

        assert_eq!(function.blocks.len(), 2);

        assert_eq!(function.blocks[0].id, BlockId(0));
        assert_eq!(function.blocks[1].id, BlockId(1));

        assert_eq!(function.blocks[0].terminator, Terminator::Jump(BlockId(1)));

        assert!(matches!(
            function.blocks[1].instructions.as_slice(),
            [IrInstruction::ConstInt {
                destination: ValueId(1),
                value: 42
            }]
        ));
    }

    #[test]
    fn removes_empty_jump_block() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Void,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(2)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![IrInstruction::ConstInt {
                            destination: ValueId(0),
                            value: 42,
                        }],
                        terminator: Terminator::Return {
                            value: Some(ValueId(0)),
                        },
                    },
                ],
            }],
        };

        remove_empty_blocks(&mut program).unwrap();

        let function = &program.functions[0];

        assert_eq!(function.blocks.len(), 2);

        assert_eq!(function.blocks[0].id, BlockId(0));
        assert_eq!(function.blocks[1].id, BlockId(1));

        assert_eq!(function.blocks[0].terminator, Terminator::Jump(BlockId(1)));

        assert!(matches!(
            function.blocks[1].instructions.as_slice(),
            [IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 42
            }]
        ));
    }

    #[test]
    fn threads_branch_target_through_empty_block() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
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
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    },
                ],
            }],
        };

        thread_jumps(&mut program).expect("jump threading should succeed");

        assert_eq!(
            program.functions[0].blocks[0].terminator,
            Terminator::Branch {
                condition: ValueId(0),
                then_block: BlockId(3),
                else_block: BlockId(2),
            }
        );
    }

    #[test]
    fn threads_jump_through_empty_block() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(2)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    },
                ],
            }],
        };

        thread_jumps(&mut program).expect("jump threading should succeed");

        assert_eq!(
            program.functions[0].blocks[0].terminator,
            Terminator::Jump(BlockId(2))
        );
    }

    #[test]
    fn does_not_thread_through_non_empty_block() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![IrInstruction::ConstInt {
                            destination: ValueId(0),
                            value: 42,
                        }],
                        terminator: Terminator::Jump(BlockId(2)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: Vec::new(),
                        terminator: Terminator::Return { value: None },
                    },
                ],
            }],
        };

        thread_jumps(&mut program).expect("jump threading should succeed");

        assert_eq!(
            program.functions[0].blocks[0].terminator,
            Terminator::Jump(BlockId(1))
        );
    }

    #[test]
    fn threads_multiple_empty_jump_blocks() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(1)),
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
            }],
        };

        thread_jumps(&mut program).expect("jump threading should succeed");

        assert_eq!(
            program.functions[0].blocks[0].terminator,
            Terminator::Jump(BlockId(3))
        );
    }

    #[test]
    fn threading_can_expose_redundant_branch() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
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
                        terminator: Terminator::Jump(BlockId(3)),
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
            }],
        };

        thread_jumps(&mut program).expect("jump threading should succeed");

        assert_eq!(
            program.functions[0].blocks[0].terminator,
            Terminator::Branch {
                condition: ValueId(0),
                then_block: BlockId(3),
                else_block: BlockId(3),
            }
        );
    }

    #[test]
    fn simplifies_add_zero() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
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
                            value: 0,
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
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(0),
            }
        );
    }

    #[test]
    fn simplifies_zero_add() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
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
                            value: 0,
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 10,
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
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(1),
            }
        );
    }

    #[test]
    fn simplifies_subtract_zero() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
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
                            value: 0,
                        },
                        IrInstruction::Binary {
                            destination: ValueId(2),
                            op: IrBinaryOp::Subtract,
                            left: ValueId(0),
                            right: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(0),
            }
        );
    }

    #[test]
    fn simplifies_multiply_one() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
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
                            value: 1,
                        },
                        IrInstruction::Binary {
                            destination: ValueId(2),
                            op: IrBinaryOp::Multiply,
                            left: ValueId(0),
                            right: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(0),
            }
        );
    }

    #[test]
    fn simplifies_one_multiply() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
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
                            value: 10,
                        },
                        IrInstruction::Binary {
                            destination: ValueId(2),
                            op: IrBinaryOp::Multiply,
                            left: ValueId(0),
                            right: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(1),
            }
        );
    }

    #[test]
    fn simplifies_multiply_zero() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
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
                            value: 0,
                        },
                        IrInstruction::Binary {
                            destination: ValueId(2),
                            op: IrBinaryOp::Multiply,
                            left: ValueId(0),
                            right: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::ConstInt {
                destination: ValueId(2),
                value: 0,
            }
        );
    }

    #[test]
    fn simplifies_zero_multiply() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
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
                            value: 0,
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 10,
                        },
                        IrInstruction::Binary {
                            destination: ValueId(2),
                            op: IrBinaryOp::Multiply,
                            left: ValueId(0),
                            right: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::ConstInt {
                destination: ValueId(2),
                value: 0,
            }
        );
    }

    #[test]
    fn simplifies_divide_one() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
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
                            value: 1,
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
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(0),
            }
        );
    }

    #[test]
    fn simplifies_equal_same_value() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Bool,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::Parameter {
                            destination: ValueId(0),
                            local: LocalId(0),
                        },
                        IrInstruction::Binary {
                            destination: ValueId(1),
                            op: IrBinaryOp::Equal,
                            left: ValueId(0),
                            right: ValueId(0),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                }],
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert_eq!(
            program.functions[0].blocks[0].instructions[1],
            IrInstruction::ConstBool {
                destination: ValueId(1),
                value: true,
            }
        );
    }

    #[test]
    fn does_not_simplify_equal_different_values() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Bool,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
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
                        IrInstruction::Binary {
                            destination: ValueId(2),
                            op: IrBinaryOp::Equal,
                            left: ValueId(0),
                            right: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        simplify_algebraic(&mut program).expect("algebraic simplification should succeed");

        assert!(matches!(
            program.functions[0].blocks[0].instructions[2],
            IrInstruction::Binary {
                op: IrBinaryOp::Equal,
                ..
            }
        ));
    }

    #[test]
    fn eliminates_redundant_binary_expression() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
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
                    IrInstruction::Binary {
                        destination: ValueId(3),
                        op: IrBinaryOp::Add,
                        left: ValueId(0),
                        right: ValueId(1),
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

        gvn_cse(&mut program).unwrap();

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            instructions[3],
            IrInstruction::Copy {
                destination: ValueId(3),
                source: ValueId(2),
            }
        ));
    }

    #[test]
    fn eliminates_redundant_commutative_expression() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
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
                    IrInstruction::Parameter {
                        destination: ValueId(1),
                        local: LocalId(1),
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Add,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                    IrInstruction::Binary {
                        destination: ValueId(3),
                        op: IrBinaryOp::Add,
                        left: ValueId(1),
                        right: ValueId(0),
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

        gvn_cse(&mut program).unwrap();

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            instructions[3],
            IrInstruction::Copy {
                destination: ValueId(3),
                source: ValueId(2),
            }
        ));
    }

    #[test]
    fn does_not_canonicalize_subtraction() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
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
                    IrInstruction::Parameter {
                        destination: ValueId(1),
                        local: LocalId(1),
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Subtract,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                    IrInstruction::Binary {
                        destination: ValueId(3),
                        op: IrBinaryOp::Subtract,
                        left: ValueId(1),
                        right: ValueId(0),
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

        gvn_cse(&mut program).unwrap();

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            instructions[3],
            IrInstruction::Binary {
                destination: ValueId(3),
                op: IrBinaryOp::Subtract,
                left: ValueId(1),
                right: ValueId(0),
            }
        ));
    }

    #[test]
    fn gvn_canonicalizes_copy_operands() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
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
                    IrInstruction::Parameter {
                        destination: ValueId(1),
                        local: LocalId(1),
                    },
                    IrInstruction::Binary {
                        destination: ValueId(2),
                        op: IrBinaryOp::Add,
                        left: ValueId(0),
                        right: ValueId(1),
                    },
                    IrInstruction::Copy {
                        destination: ValueId(3),
                        source: ValueId(2),
                    },
                    IrInstruction::Parameter {
                        destination: ValueId(4),
                        local: LocalId(2),
                    },
                    IrInstruction::Binary {
                        destination: ValueId(5),
                        op: IrBinaryOp::Add,
                        left: ValueId(3),
                        right: ValueId(4),
                    },
                    IrInstruction::Binary {
                        destination: ValueId(6),
                        op: IrBinaryOp::Add,
                        left: ValueId(2),
                        right: ValueId(4),
                    },
                ],
                terminator: Terminator::Return {
                    value: Some(ValueId(6)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        gvn_cse(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[0].instructions[5],
            IrInstruction::Binary {
                destination: ValueId(5),
                op: IrBinaryOp::Add,
                left: ValueId(3),
                right: ValueId(4),
            }
        ));

        assert!(matches!(
            &function.blocks[0].instructions[6],
            IrInstruction::Copy {
                destination: ValueId(6),
                source: ValueId(5),
            }
        ));
    }

    #[test]
    fn forwards_store_into_load() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: vec![IrLocal {
                id: LocalId(0),
                name: "x".to_string(),
                ty: IrType::Int,
            }],
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
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
                terminator: Terminator::Return {
                    value: Some(ValueId(1)),
                },
            }],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        forward_local_stores(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[0].instructions[2],
            IrInstruction::Copy {
                destination: ValueId(1),
                source: ValueId(0),
            }
        ));
    }

    #[test]
    fn forwards_store_across_single_predecessor() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::ConstInt {
                            destination: ValueId(0),
                            value: 42,
                        },
                        IrInstruction::StoreLocal {
                            local: LocalId(0),
                            value: ValueId(0),
                        },
                    ],
                    terminator: Terminator::Jump(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::LoadLocal {
                        destination: ValueId(1),
                        local: LocalId(0),
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        forward_local_stores(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[1].instructions[0],
            IrInstruction::Copy {
                destination: ValueId(1),
                source: ValueId(0),
            }
        ));
    }

    #[test]
    fn does_not_forward_store_when_predecessors_disagree() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::ConstBool {
                        destination: ValueId(0),
                        value: true,
                    }],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 10,
                        },
                        IrInstruction::StoreLocal {
                            local: LocalId(0),
                            value: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        IrInstruction::ConstInt {
                            destination: ValueId(2),
                            value: 20,
                        },
                        IrInstruction::StoreLocal {
                            local: LocalId(0),
                            value: ValueId(2),
                        },
                    ],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![IrInstruction::LoadLocal {
                        destination: ValueId(3),
                        local: LocalId(0),
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

        forward_local_stores(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[3].instructions[0],
            IrInstruction::LoadLocal {
                destination: ValueId(3),
                local: LocalId(0),
            }
        ));
    }

    #[test]
    fn eliminates_redundant_loads() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::LoadLocal {
                        destination: ValueId(0),
                        local: LocalId(0),
                    },
                    IrInstruction::LoadLocal {
                        destination: ValueId(1),
                        local: LocalId(0),
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

        eliminate_redundant_loads(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[0].instructions[1],
            IrInstruction::Copy {
                destination: ValueId(1),
                source: ValueId(0),
            }
        ));
    }

    #[test]
    fn does_not_eliminate_load_after_store() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                instructions: vec![
                    IrInstruction::LoadLocal {
                        destination: ValueId(0),
                        local: LocalId(0),
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 42,
                    },
                    IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(1),
                    },
                    IrInstruction::LoadLocal {
                        destination: ValueId(2),
                        local: LocalId(0),
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

        eliminate_redundant_loads(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[0].instructions[3],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(1),
            }
        ));
    }

    #[test]
    fn eliminates_overwritten_store() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
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
                    IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(0),
                    },
                    IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 20,
                    },
                    IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(1),
                    },
                    IrInstruction::LoadLocal {
                        destination: ValueId(2),
                        local: LocalId(0),
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

        eliminate_dead_stores(&mut program).unwrap();

        let function = &program.functions[0];

        assert_eq!(function.blocks[0].instructions.len(), 4);

        assert!(matches!(
            &function.blocks[0].instructions[0],
            IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 10,
            }
        ));

        assert!(matches!(
            &function.blocks[0].instructions[1],
            IrInstruction::ConstInt {
                destination: ValueId(1),
                value: 20,
            }
        ));

        assert!(matches!(
            &function.blocks[0].instructions[2],
            IrInstruction::StoreLocal {
                local: LocalId(0),
                value: ValueId(1),
            }
        ));

        assert!(matches!(
            &function.blocks[0].instructions[3],
            IrInstruction::LoadLocal {
                destination: ValueId(2),
                local: LocalId(0),
            }
        ));
    }

    #[test]
    fn preserves_store_observed_by_load() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
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
                    IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(0),
                    },
                    IrInstruction::LoadLocal {
                        destination: ValueId(1),
                        local: LocalId(0),
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

        eliminate_dead_stores(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[0].instructions[1],
            IrInstruction::StoreLocal {
                local: LocalId(0),
                value: ValueId(0),
            }
        ));
    }

    #[test]
    fn preserves_store_when_successor_loads_local() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::ConstInt {
                            destination: ValueId(0),
                            value: 42,
                        },
                        IrInstruction::StoreLocal {
                            local: LocalId(0),
                            value: ValueId(0),
                        },
                    ],
                    terminator: Terminator::Jump(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::LoadLocal {
                        destination: ValueId(1),
                        local: LocalId(0),
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        eliminate_dead_stores(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[0].instructions[1],
            IrInstruction::StoreLocal {
                local: LocalId(0),
                value: ValueId(0),
            }
        ));
    }

    #[test]
    fn preserves_stores_when_join_loads_local() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::ConstBool {
                        destination: ValueId(0),
                        value: true,
                    }],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 10,
                        },
                        IrInstruction::StoreLocal {
                            local: LocalId(0),
                            value: ValueId(1),
                        },
                    ],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![
                        IrInstruction::ConstInt {
                            destination: ValueId(2),
                            value: 20,
                        },
                        IrInstruction::StoreLocal {
                            local: LocalId(0),
                            value: ValueId(2),
                        },
                    ],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![IrInstruction::LoadLocal {
                        destination: ValueId(3),
                        local: LocalId(0),
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

        eliminate_dead_stores(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[1].instructions[1],
            IrInstruction::StoreLocal {
                local: LocalId(0),
                value: ValueId(1),
            }
        ));

        assert!(matches!(
            &function.blocks[2].instructions[1],
            IrInstruction::StoreLocal {
                local: LocalId(0),
                value: ValueId(2),
            }
        ));
    }

    #[test]
    fn merges_linear_blocks() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
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
                        value: 10,
                    }],
                    terminator: Terminator::Jump(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 20,
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        merge_linear_blocks(&mut program).unwrap();

        let function = &program.functions[0];

        assert_eq!(function.blocks.len(), 1);
        assert_eq!(function.blocks[0].id, BlockId(0));
        assert_eq!(function.blocks[0].instructions.len(), 2);

        assert!(matches!(
            &function.blocks[0].instructions[0],
            IrInstruction::ConstInt {
                destination: ValueId(0),
                value: 10,
            }
        ));

        assert!(matches!(
            &function.blocks[0].instructions[1],
            IrInstruction::ConstInt {
                destination: ValueId(1),
                value: 20,
            }
        ));

        assert!(matches!(
            function.blocks[0].terminator,
            Terminator::Return {
                value: Some(ValueId(1)),
            }
        ));
    }

    #[test]
    fn does_not_merge_block_with_multiple_predecessors() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::ConstBool {
                        destination: ValueId(0),
                        value: true,
                    }],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: Vec::new(),
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: Vec::new(),
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 42,
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                },
            ],
        };

        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![function],
        };

        merge_linear_blocks(&mut program).unwrap();

        let function = &program.functions[0];

        assert_eq!(function.blocks.len(), 4);
    }

    #[test]
    fn eliminates_redundant_load_when_predecessors_agree() {
        let function = IrFunction {
            id: Some(FunctionId(0)),
            name: "test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: Vec::new(),
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::ConstBool {
                            destination: ValueId(0),
                            value: true,
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
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
                    instructions: vec![IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(1),
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![IrInstruction::StoreLocal {
                        local: LocalId(0),
                        value: ValueId(1),
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![IrInstruction::LoadLocal {
                        destination: ValueId(2),
                        local: LocalId(0),
                    }],
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

        eliminate_redundant_loads(&mut program).unwrap();

        let function = &program.functions[0];

        assert!(matches!(
            &function.blocks[3].instructions[0],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(1),
            }
        ));
    }

    #[test]
    fn eliminates_unused_load() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: vec![IrLocal {
                    id: LocalId(0),
                    name: "x".to_string(),
                    ty: IrType::Int,
                }],
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
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
                    terminator: Terminator::Return {
                        value: Some(ValueId(0)),
                    },
                }],
            }],
        };

        eliminate_dead_code(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(!instructions
            .iter()
            .any(|instruction| { matches!(instruction, IrInstruction::LoadLocal { .. }) }));
    }

    #[test]
    fn preserves_load_used_by_return() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: vec![IrLocal {
                    id: LocalId(0),
                    name: "x".to_string(),
                    ty: IrType::Int,
                }],
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
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
                    terminator: Terminator::Return {
                        value: Some(ValueId(1)),
                    },
                }],
            }],
        };

        eliminate_dead_code(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(instructions.iter().any(|instruction| {
            matches!(
                instruction,
                IrInstruction::LoadLocal {
                    destination: ValueId(1),
                    local: LocalId(0),
                }
            )
        }));
    }

    #[test]
    fn eliminates_redundant_field_load() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(1),
                            receiver: ValueId(0),
                            field: 0,
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(2),
                            receiver: ValueId(0),
                            field: 0,
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        eliminate_redundant_field_loads(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            &instructions[2],
            IrInstruction::Copy {
                destination: ValueId(2),
                source: ValueId(1),
            }
        ));
    }

    #[test]
    fn does_not_eliminate_field_load_after_store() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::ConstInt {
                            destination: ValueId(1),
                            value: 42,
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(2),
                            receiver: ValueId(0),
                            field: 0,
                        },
                        IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(3),
                            receiver: ValueId(0),
                            field: 0,
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(3)),
                    },
                }],
            }],
        };

        eliminate_redundant_field_loads(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            &instructions[4],
            IrInstruction::LoadField {
                destination: ValueId(3),
                receiver: ValueId(0),
                field: 0,
            }
        ));
    }

    #[test]
    fn does_not_eliminate_load_of_different_field() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    instructions: vec![
                        IrInstruction::AllocStruct {
                            destination: ValueId(0),
                            struct_id: StructId(0),
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(1),
                            receiver: ValueId(0),
                            field: 0,
                        },
                        IrInstruction::LoadField {
                            destination: ValueId(2),
                            receiver: ValueId(0),
                            field: 1,
                        },
                    ],
                    terminator: Terminator::Return {
                        value: Some(ValueId(2)),
                    },
                }],
            }],
        };

        eliminate_redundant_field_loads(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[0].instructions;

        assert!(matches!(
            &instructions[2],
            IrInstruction::LoadField {
                destination: ValueId(2),
                receiver: ValueId(0),
                field: 1,
            }
        ));
    }

    #[test]
    fn eliminates_redundant_field_load_when_predecessors_agree() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![
                            IrInstruction::AllocStruct {
                                destination: ValueId(0),
                                struct_id: StructId(0),
                            },
                            IrInstruction::ConstInt {
                                destination: ValueId(1),
                                value: 42,
                            },
                        ],
                        terminator: Terminator::Branch {
                            condition: ValueId(1),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        }],
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![IrInstruction::StoreField {
                            receiver: ValueId(0),
                            field: 0,
                            value: ValueId(1),
                        }],
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: vec![IrInstruction::LoadField {
                            destination: ValueId(2),
                            receiver: ValueId(0),
                            field: 0,
                        }],
                        terminator: Terminator::Return {
                            value: Some(ValueId(2)),
                        },
                    },
                ],
            }],
        };

        eliminate_redundant_field_loads(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[3].instructions;

        assert!(matches!(
            &instructions[0],
            IrInstruction::LoadField {
                destination: ValueId(2),
                receiver: ValueId(0),
                field: 0,
            }
        ));
    }

    #[test]
    fn eliminates_redundant_field_load_at_join() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![
                            IrInstruction::AllocStruct {
                                destination: ValueId(0),
                                struct_id: StructId(0),
                            },
                            IrInstruction::LoadField {
                                destination: ValueId(1),
                                receiver: ValueId(0),
                                field: 0,
                            },
                            IrInstruction::ConstBool {
                                destination: ValueId(2),
                                value: true,
                            },
                        ],
                        terminator: Terminator::Branch {
                            condition: ValueId(2),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: Vec::new(),
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: vec![IrInstruction::LoadField {
                            destination: ValueId(3),
                            receiver: ValueId(0),
                            field: 0,
                        }],
                        terminator: Terminator::Return {
                            value: Some(ValueId(3)),
                        },
                    },
                ],
            }],
        };

        eliminate_redundant_field_loads(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[3].instructions;

        assert!(matches!(
            &instructions[0],
            IrInstruction::Copy {
                destination: ValueId(3),
                source: ValueId(1),
            }
        ));
    }

    #[test]
    fn does_not_eliminate_field_load_when_predecessors_disagree() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![IrFunction {
                id: None,
                name: "test".to_string(),
                owner: None,
                parameters: Vec::new(),
                locals: Vec::new(),
                return_type: IrType::Int,
                entry: BlockId(0),
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        instructions: vec![
                            IrInstruction::AllocStruct {
                                destination: ValueId(0),
                                struct_id: StructId(0),
                            },
                            IrInstruction::LoadField {
                                destination: ValueId(1),
                                receiver: ValueId(0),
                                field: 0,
                            },
                            IrInstruction::ConstBool {
                                destination: ValueId(2),
                                value: true,
                            },
                        ],
                        terminator: Terminator::Branch {
                            condition: ValueId(2),
                            then_block: BlockId(1),
                            else_block: BlockId(2),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        instructions: vec![IrInstruction::LoadField {
                            destination: ValueId(3),
                            receiver: ValueId(0),
                            field: 0,
                        }],
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(2),
                        instructions: vec![IrInstruction::LoadField {
                            destination: ValueId(4),
                            receiver: ValueId(0),
                            field: 0,
                        }],
                        terminator: Terminator::Jump(BlockId(3)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        instructions: vec![IrInstruction::LoadField {
                            destination: ValueId(5),
                            receiver: ValueId(0),
                            field: 0,
                        }],
                        terminator: Terminator::Return {
                            value: Some(ValueId(5)),
                        },
                    },
                ],
            }],
        };

        eliminate_redundant_field_loads(&mut program).expect("optimization should succeed");

        let instructions = &program.functions[0].blocks[3].instructions;

        assert!(matches!(
            &instructions[0],
            IrInstruction::LoadField {
                destination: ValueId(5),
                receiver: ValueId(0),
                field: 0,
            }
        ));
    }
}

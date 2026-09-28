use std::collections::HashSet;

use crate::{
    compiler::error::CompilerError,
    ir::{IrInstruction, ValueId},
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

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ir::ir::{
        BasicBlock, IrFunction, IrInstruction, IrProgram, IrType, Terminator, ValueId,
    };
    use crate::ir::BlockId;
    use crate::semantic::symbols::FunctionId;

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
}

pub mod error;
pub mod source;

use crate::{ir, lexer, parser, semantic};

use error::CompilerError;

pub fn compile(source: &str) -> Result<ir::IrProgram, Vec<CompilerError>> {
    let source_file = source::SourceFile::new(source);

    let tokens = lexer::lex(&source_file)?;

    let ast = parser::parse(&source_file, &tokens)?;

    let hir = semantic::analyze(ast, source_file)?;

    let mut ir = ir::lower::lower_to_ir(hir)?;

    // Validate the CFG before SSA construction.
    ir::validate(&ir)?;

    // Convert local-variable based IR into SSA.
    ir::construct_ssa(&mut ir)?;

    // Validate the resulting SSA IR.
    ir::validate_ssa(&ir)?;

    ir::phi::lower_phis(&mut ir)?;

    ir::cleanup::simplify_constant_branches(&mut ir)?;

    ir::cleanup::simplify_redundant_branches(&mut ir)?;

    ir::cleanup::thread_jumps(&mut ir)?;

    // Remove unreachable CFG blocks.
    ir::cleanup::remove_unreachable_blocks(&mut ir)?;

    ir::cleanup::remove_empty_blocks(&mut ir)?;

    // Validate the cleaned non-SSA IR.
    ir::validate(&ir)?;

    // Propagate known constants.
    ir::cleanup::constant_propagate(&mut ir)?;

    ir::cleanup::simplify_algebraic(&mut ir)?;

    // Fold constant integer expressions.
    ir::cleanup::constant_fold(&mut ir)?;

    ir::cleanup::gvn_cse(&mut ir)?;

    ir::cleanup::forward_local_stores(&mut ir)?;

    ir::cleanup::eliminate_redundant_loads(&mut ir)?;

    // Copy propagation
    ir::cleanup::copy_propagate(&mut ir)?;

    ir::cleanup::eliminate_redundant_copies(&mut ir)?;

    // Remove unused pure instructions.
    ir::cleanup::eliminate_dead_code(&mut ir)?;

    // Validate the final optimized IR.
    ir::validate(&ir)?;

    Ok(ir)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::ir::IrInstruction;

    #[test]
    fn compiles_simple_integer_function() {
        let source = r#"
            fn main(): int {
                return 42;
            }
        "#;

        let program = compile(source).expect("program should compile");

        assert_eq!(program.functions.len(), 1);
        assert_eq!(program.functions[0].name, "main");
        assert_eq!(program.functions[0].blocks.len(), 1);

        let function = &program.functions[0];

        assert!(function.blocks.iter().all(|block| {
            !block
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, IrInstruction::Phi { .. }))
        }));
    }

    #[test]
    fn compiles_local_variable_through_ssa_and_phi_lowering() {
        let source = r#"
            fn main(): int {
                let x: int = 10;
                return x;
            }
        "#;

        let program = compile(source).expect("program should compile");

        let function = &program.functions[0];

        assert!(
            function.blocks.iter().all(|block| {
                block.instructions.iter().all(|instruction| {
                    !matches!(
                        instruction,
                        IrInstruction::LoadLocal { .. }
                            | IrInstruction::StoreLocal { .. }
                            | IrInstruction::Phi { .. }
                    )
                })
            }),
            "final IR should contain neither locals operations nor phi nodes"
        );
    }

    #[test]
    fn compiles_loop_with_phi_lowering() {
        let source = r#"
            fn test(condition: bool): int {
                let x: int = 0;

                while (condition) {
                    x = 1;
                }

                return x;
            }
        "#;

        let program = compile(source).expect("loop program should compile");

        let function = &program.functions[0];

        assert!(
            function.blocks.len() >= 4,
            "expected loop CFG to contain multiple blocks"
        );

        assert!(
            function.blocks.iter().all(|block| {
                block.instructions.iter().all(|instruction| {
                    !matches!(
                        instruction,
                        IrInstruction::LoadLocal { .. }
                            | IrInstruction::StoreLocal { .. }
                            | IrInstruction::Phi { .. }
                    )
                })
            }),
            "final IR should be non-SSA without local or phi instructions"
        );

        let reachable = function.reachable_blocks();

        for block in &function.blocks {
            assert!(
                reachable.contains(&block.id),
                "final cleanup should leave only reachable blocks"
            );
        }
    }

    #[test]
    fn propagates_compilation_errors() {
        let source = r#"
            fn main(): int {
                return true;
            }
        "#;

        let errors = compile(source).expect_err("invalid program should fail");

        assert!(
            errors.iter().any(|error| error.message.contains("return")),
            "expected return-type error, got: {errors:#?}"
        );
    }

    #[test]
    fn compile_removes_dead_instructions_from_final_ir() {
        let source = r#"
        fn main(): int {
            let used: int = 10;
            let dead: int = 20;
            return used;
        }
    "#;

        let program =
            crate::compiler::compile(source).expect("program should compile successfully");

        let main = program
            .functions
            .iter()
            .find(|function| function.name == "main")
            .expect("main function should exist");

        let instructions = main
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter())
            .collect::<Vec<_>>();

        // The value returned by main is still needed.
        assert!(instructions.iter().any(|instruction| {
            matches!(
                instruction,
                crate::ir::IrInstruction::ConstInt { value: 10, .. }
            )
        }));

        // The unused `dead` local must disappear completely from the final IR.
        assert!(!instructions.iter().any(|instruction| {
            matches!(
                instruction,
                crate::ir::IrInstruction::ConstInt { value: 20, .. }
            )
        }));
    }

    #[test]
    fn compile_propagates_folds_and_removes_dead_constants() {
        let source = r#"
        fn main(): int {
            let x: int = 10;
            let y: int = 20;
            return x + y;
        }
    "#;

        let program =
            crate::compiler::compile(source).expect("program should compile successfully");

        let main = program
            .functions
            .iter()
            .find(|function| function.name == "main")
            .expect("main function should exist");

        let instructions = main
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter())
            .collect::<Vec<_>>();

        let returned_value = match &main.blocks[0].terminator {
            crate::ir::Terminator::Return { value } => value.expect("main should return a value"),
            other => panic!("expected Return terminator, got {other:?}"),
        };

        // Constant propagation + folding should produce 30.
        assert!(instructions.iter().any(|instruction| {
            matches!(
                instruction,
                crate::ir::IrInstruction::ConstInt {
                    destination,
                    value: 30,
                } if *destination == returned_value
            )
        }));

        // DCE should remove the original constants after folding.
        assert!(!instructions.iter().any(|instruction| {
            matches!(
                instruction,
                crate::ir::IrInstruction::ConstInt { value: 10, .. }
            )
        }));

        assert!(!instructions.iter().any(|instruction| {
            matches!(
                instruction,
                crate::ir::IrInstruction::ConstInt { value: 20, .. }
            )
        }));

        // The final expression should no longer be a Binary instruction.
        assert!(!instructions.iter().any(|instruction| {
            matches!(
                instruction,
                crate::ir::IrInstruction::Binary {
                    op: crate::ir::IrBinaryOp::Add,
                    ..
                }
            )
        }));
    }

    #[test]
    fn compile_simplifies_constant_true_branch() {
        let source = r#"
        fn main(): int {
            if (true) {
                return 10;
            } else {
                return 20;
            }
        }
    "#;

        let program = compile(source).expect("program should compile successfully");
        let function = &program.functions[0];

        assert!(
            function.blocks.len() < 4,
            "constant branch should allow unreachable CFG blocks to be removed"
        );

        let instructions = function
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter())
            .collect::<Vec<_>>();

        assert!(instructions.iter().any(|instruction| {
            matches!(instruction, IrInstruction::ConstInt { value: 10, .. })
        }));

        assert!(!instructions.iter().any(|instruction| {
            matches!(instruction, IrInstruction::ConstInt { value: 20, .. })
        }));

        assert!(function
            .blocks
            .iter()
            .all(|block| { !matches!(block.terminator, crate::ir::Terminator::Branch { .. }) }));
    }

    #[test]
    fn compile_simplifies_constant_false_branch() {
        let source = r#"
        fn main(): int {
            if (false) {
                return 10;
            } else {
                return 20;
            }
        }
    "#;

        let program = compile(source).expect("program should compile successfully");
        let function = &program.functions[0];

        let instructions = function
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter())
            .collect::<Vec<_>>();

        assert!(instructions.iter().any(|instruction| {
            matches!(instruction, IrInstruction::ConstInt { value: 20, .. })
        }));

        assert!(!instructions.iter().any(|instruction| {
            matches!(instruction, IrInstruction::ConstInt { value: 10, .. })
        }));

        assert!(function
            .blocks
            .iter()
            .all(|block| { !matches!(block.terminator, crate::ir::Terminator::Branch { .. }) }));
    }

    #[test]
    fn compile_removes_empty_jump_blocks() {
        let source = r#"
        fn main(): int {
            let x: int = 10;

            if (true) {
                x = 20;
            }

            return x;
        }
    "#;

        let program = compile(source).expect("program should compile successfully");

        let function = &program.functions[0];

        assert!(
            function.blocks.len() <= 3,
            "constant condition should not leave redundant CFG blocks"
        );

        assert!(function
            .blocks
            .iter()
            .all(|block| { !matches!(block.terminator, crate::ir::Terminator::Branch { .. }) }));
    }
}

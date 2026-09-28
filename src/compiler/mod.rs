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

    /*
     * Validate the CFG before SSA construction.
     */
    ir::validate(&ir)?;

    /*
     * Convert local-variable based IR into SSA.
     */
    ir::construct_ssa(&mut ir)?;

    /*
     * Validate the resulting SSA IR.
     */
    ir::validate_ssa(&ir)?;

    ir::phi::lower_phis(&mut ir)?;

    // Remove unreachable CFG blocks.
    ir::cleanup::remove_unreachable_blocks(&mut ir)?;

    ir::cleanup::eliminate_dead_code(&mut ir)?;

    // Validate the resulting non-SSA IR.
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
}

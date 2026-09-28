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

    // Validate the resulting non-SSA IR.
    ir::validate(&ir)?;

    Ok(ir)
}

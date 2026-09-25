mod codegen;
mod compiler;
mod ir;
mod lexer;
mod parser;
mod semantic;

use std::{env, fs, process};

use crate::codegen::CodegenTarget;

use miette::Report;

fn main() -> miette::Result<()> {
    let path = match env::args().nth(1) {
        Some(path) => path,
        None => {
            eprintln!("usage: lev <file.lev>");
            process::exit(1);
        }
    };

    let source = match fs::read_to_string(&path) {
        Ok(source) => source,
        Err(err) => {
            eprintln!("failed to read '{}': {}", path, err);
            process::exit(1);
        }
    };

    let program = match compiler::compile(&source) {
        Ok(program) => program,
        Err(errors) => {
            for error in errors {
                eprintln!("{:?}", Report::new(error));
            }

            process::exit(1);
        }
    };

    println!("{}", program);

    match codegen::generate(&program, CodegenTarget::X86_64MacOS) {
        Ok(assembly) => {
            println!("{}", assembly);
            Ok(())
        }
        Err(errors) => {
            for error in errors {
                eprintln!("codegen error: {:?}", Report::new(error));
            }

            process::exit(1);
        }
    }
}

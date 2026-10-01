mod codegen;
mod compiler;
mod ir;
mod lexer;
mod parser;
mod semantic;

use std::{env, fs, process};

use crate::codegen::CodegenTarget;
use clap::Parser;
use miette::Report;

#[derive(Parser, Debug)]
#[command(name = "lev")]
#[command(about = "The Lev compiler")]
struct Cli {
    /// Input Lev source file
    input: String,
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let source = match fs::read_to_string(&cli.input) {
        Ok(source) => source,
        Err(err) => {
            eprintln!("failed to read '{}': {}", cli.input, err);
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

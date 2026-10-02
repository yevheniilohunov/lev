mod codegen;
mod compiler;
mod ir;
mod lexer;
mod parser;
mod semantic;

use std::{
    env, fs,
    process::{self, Command},
};

use crate::codegen::CodegenTarget;
use clap::Parser;
use miette::Report;

#[derive(Parser, Debug)]
#[command(name = "lev")]
#[command(about = "The Lev compiler")]
struct Cli {
    /// Input Lev source file
    input: String,

    /// Output executable name
    #[arg(short, long)]
    output: Option<String>,
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

    let target = CodegenTarget::native();

    eprintln!("target: {:?}", target);

    let assembly = match codegen::generate(&program, CodegenTarget::native()) {
        Ok(assembly) => assembly,
        Err(errors) => {
            for error in errors {
                eprintln!("codegen error: {:?}", Report::new(error));
            }
            process::exit(1);
        }
    };

    match cli.output {
        Some(output) => {
            let assembly_path = format!("{}.s", output);
            let object_path = format!("{}.o", output);

            if let Err(err) = fs::write(&assembly_path, assembly) {
                eprintln!("failed to write '{}': {}", assembly_path, err);
                process::exit(1);
            }

            println!("wrote {}", assembly_path);

            let status = match Command::new("clang")
                .arg("-c")
                .arg(&assembly_path)
                .arg("-o")
                .arg(&object_path)
                .status()
            {
                Ok(status) => status,
                Err(err) => {
                    eprintln!("failed to run clang: {}", err);
                    process::exit(1);
                }
            };

            if !status.success() {
                eprintln!("assembler failed");
                process::exit(1);
            }

            println!("wrote {}", object_path);
        }
        None => {
            println!("{}", assembly);
        }
    }

    Ok(())
}

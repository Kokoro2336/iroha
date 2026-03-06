use clap::Parser;
use lalrpop_util::lalrpop_mod;
use std::fs::read_to_string;
use std::io::Result;

mod analysis;
mod backend;
mod base;
mod cli;
mod debug;
mod frontend;
mod ir;
mod opt;
mod utils;
use crate::base::PassManager;
use crate::cli::Cli;
use crate::debug::log::setup;
use crate::frontend::parse;
use crate::frontend::*;
use crate::opt::*;
use crate::utils::arena::Arena;

use debug::info;

// Import SysY parser.
lalrpop_mod!(sysy);

fn main() -> Result<()> {
    // setup logging
    // We need to keep this guard alive for the entire duration of the program.
    let _guard = setup("rsyc.log");
    info!("Logger initialized.");

    // Parse the args
    let cli = Cli::parse();

    let input_path = cli.input.clone();
    let _ = cli.output.clone();

    // Get input str.
    let input_str = read_to_string(&input_path)?;

    // Parse the input string into an AST.
    let result = {
        let mut parser = parse::Parser::new();
        let root_id = sysy::CompUnitParser::new()
            .parse(&mut parser, &input_str)
            .unwrap();
        // set entry point to the root of the AST
        parser.ast.set_entry(root_id);
        // Clean up the AST.
        parser.ast.gc();
        parser.take()
    };
    // info!("\nParsed result: {:#?}", result);

    let res = std::thread::Builder::new()
        // Temporarily, we set the stack size to 16MB to avoid stack overflow in deep recursion of semantic analysis.
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            info!("Start Semantic Analysis.");
            let result = {
                match Semantic::new(result).run() {
                    Ok(res) => res,
                    Err(e) => {
                        panic!("Semantic Error: {}", e);
                    }
                }
            };
            info!("Finish Semantic Analysis.");

            info!("Start Emitting.");
            let ir = Emit::new(result).run();
            info!("Finish Emitting.");
            ir
        })?
        .join();

    let mut ir = match res {
        Ok(ir) => ir,
        Err(e) => {
            panic!("Thread panicked: {:?}", e);
        }
    };

    // Run optimizations.
    PassManager::new(&cli)
        .register(Box::new(Mem2Reg::new()))
        .register(Box::new(RemoveTrivialPhi::new()))
        .register(Box::new(SCCP::new()))
        .register(Box::new(RemoveTrivialPhi::new()))
        .register(Box::new(DCE::new()))
        .register(Box::new(Compaction::new()))
        .run(&mut ir);

    Ok(())
}

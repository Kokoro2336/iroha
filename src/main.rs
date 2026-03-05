use lalrpop_util::lalrpop_mod;
use std::fs::read_to_string;
use std::io::Result;
use clap::Parser;

mod analysis;
mod backend;
mod base;
mod debug;
mod frontend;
mod ir;
mod opt;
mod utils;
mod cli;
use crate::base::PassManager;
use crate::debug::log::setup;
use crate::frontend::parse;
use crate::frontend::*;
use crate::opt::*;
use crate::utils::arena::Arena;
use crate::cli::Cli;

use debug::info;

// 引用 lalrpop 生成的解析器
// 因为我们刚刚创建了 sysy.lalrpop, 所以模块名是 sysy
lalrpop_mod!(sysy);

fn main() -> Result<()> {
    // setup logging
    // We need to keep this guard alive for the entire duration of the program.
    let _guard = setup("rsyc.log");
    info!("Logger initialized.");

    // Parse the args
    let cli = Cli::parse();

    let input_path = cli.input.clone();
    #[allow(unused)]
    let output = cli.output.clone();

    // 读取输入文件
    let input_str = read_to_string(&input_path)?;

    // 调用 lalrpop 生成的 parser 解析输入文件
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
    let mut ir = Emit::new(result).run();
    info!("Finish Emitting.");

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

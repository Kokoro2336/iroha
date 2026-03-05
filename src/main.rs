use clap::Parser;
use lalrpop_util::lalrpop_mod;
use std::fs::read_to_string;
use std::io::Result;

mod analysis;
mod asm;
mod base;
mod debug;
mod frontend;
mod ir;
mod opt;
mod utils;
use crate::base::PassManager;
use crate::debug::log::setup;
use crate::frontend::parse;
use crate::frontend::*;
use crate::opt::*;
use crate::utils::arena::Arena;

use debug::info;
use debug::DumpLLVMPass;

// 引用 lalrpop 生成的解析器
// 因为我们刚刚创建了 sysy.lalrpop, 所以模块名是 sysy
lalrpop_mod!(sysy);

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// enable this to transform src to koopa ir.
    #[arg(long = "emit-llvm", default_value_t = false)]
    emit_llvm: bool,

    /// positional argument for input file.
    #[arg(value_name = "INPUT")]
    input: std::path::PathBuf,

    /// use this flag to specify output file.
    #[arg(short, long)]
    output: std::path::PathBuf,
}

fn main() -> Result<()> {
    // setup logging
    // We need to keep this guard alive for the entire duration of the program.
    let _guard = setup("rsyc.log");
    info!("Logger initialized.");

    // Parse the args
    let cli = Cli::parse();

    let input_path = cli.input;
    #[allow(unused)]
    let output = cli.output;

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

    PassManager::new()
        .register(Box::new(Mem2Reg::new()))
        .register(Box::new(RemoveTrivialPhi::new()))
        .register(Box::new(SCCP::new()))
        .register(Box::new(RemoveTrivialPhi::new()))
        .register(Box::new(DCE::new()))
        .register(Box::new(Compaction::new()))
        .run(&mut ir);

    info!("Start Dumping LLVM IR.");
    let filename = input_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("output")
        .to_string();
    DumpLLVMPass::new(&mut ir, filename).run();
    info!("Finish Dumping LLVM IR.");

    Ok(())
}

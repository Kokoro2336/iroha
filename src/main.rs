use clap::Parser;
use lalrpop_util::lalrpop_mod;
use std::fs::read_to_string;
use std::io::Result;

mod asm;
mod base;
mod debug;
mod frontend;
mod opt;
mod utils;
use crate::base::Pass;
use crate::debug::setup;
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
    #[arg(short = 'k', long = "koopa", default_value_t = false)]
    koopa: bool,

    /// enable this to transform koopa ir to riscv asm.
    #[arg(short = 'r', long = "riscv", default_value_t = false)]
    riscv: bool,

    /// dump graph
    #[arg(long = "graph", default_value_t = false)]
    graph: bool,

    /// positional argument for input file.
    #[arg(value_name = "INPUT")]
    input: std::path::PathBuf,

    /// use this flag to specify output file.
    #[arg(short, long, default_value = None)]
    output: std::path::PathBuf,
}

fn main() -> Result<()> {
    // setup logging
    // We need to keep this guard alive for the entire duration of the program.
    let _guard = setup("rsyc.log");
    info!("Logger initialized.");

    // preprocess argv so single-dash long-style `-koopa` becomes `--koopa`
    let args = std::env::args_os()
        .enumerate()
        .map(|(i, a)| {
            if i == 0 {
                return a;
            }
            if let Some(s) = a.to_str() {
                if s.starts_with('-') && !s.starts_with("--") && &s[1..] == "koopa" {
                    return std::ffi::OsString::from(format!("--{}", &s[1..]));
                } else if s.starts_with('-') && !s.starts_with("--") && &s[1..] == "riscv" {
                    return std::ffi::OsString::from(format!("--{}", &s[1..]));
                }
            }
            a
        })
        .collect::<Vec<_>>();

    let cli = Cli::parse_from(args);

    let input_path = cli.input;
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
        let mut pass = Semantic::new(result);
        match pass.run() {
            Ok(res) => res,
            Err(e) => {
                panic!("Semantic Error: {}", e);
            }
        }
    };
    info!("Finish Semantic Analysis.");

    // Try to dump graph to log file
    // if cli.graph {
    //     info!("Dumping AST graph.");
    //     info!("Skip AST graph dump: GraphNode is not implemented for enum AST node yet.");
    // }

    info!("Start Emitting.");
    let mut ir = Emit::new(result).run();
    info!("Finish Emitting.");

    info!("Start Running Mem2Reg.");
    Mem2Reg::new(&mut ir).run();
    info!("Finish Running Mem2Reg.");

    info!("Start Running SCCP.");
    SCCP::new(&mut ir).run();
    info!("Finish Running SCCP.");

    info!("Start Running DCE.");
    DCE::new(&mut ir).run();
    info!("Finish Running DCE. Start running compaction pass.");
    Compaction::new(&mut ir).run();
    info!("Finish Running Compaction.");

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

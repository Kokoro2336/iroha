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
use crate::base::{Builder, Pass};
use crate::debug::setup;
use crate::frontend::ast::Node;
use crate::frontend::parse;
use crate::frontend::*;
use crate::opt::*;

use debug::graph::dump_graph;
use debug::info;
use debug::DumpLlvmPass;

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
    let result = sysy::CompUnitParser::new()
        .parse(&mut parse::Parser::new(), &input_str)
        .unwrap();
    // info!("\nParsed result: {:#?}", result);

    info!("Start Semantic Analysis.");
    let result = {
        let mut pass: Box<dyn Pass<Box<dyn Node>>> = Box::new(Semantic::new(result));
        match pass.run() {
            Ok(res) => res,
            Err(e) => {
                panic!("Semantic Analysis Error: {}", e);
            }
        }
    };
    info!("Finish Semantic Analysis.");

    // Try to dump graph to log file
    if cli.graph {
        info!("Dumping AST graph.");
        dump_graph(true, &*result, "ast");
    }

    info!("Start Emitting.");
    let ir = {
        let mut emitter = Emit::new(Builder::new(), &result);
        match emitter.run() {
            Ok(res) => res,
            Err(e) => {
                panic!("Emit Error: {}", e);
            }
        }
    };
    info!("Finish Emitting. IR generated: \n{:#?}", ir);

    info!("Start Running Mem2Reg.");
    let ir = {
        let mut pass = Mem2Reg::new(ir);
        match pass.run() {
            Ok(res) => res,
            Err(e) => {
                panic!("Mem2Reg Error: {}", e);
            }
        }
    };
    info!("Finish Running Mem2Reg.");

    info!("Start Dumping LLVM IR.");
    let ir = {
        let filename = input_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("output")
            .to_string();
        let mut pass = DumpLlvmPass::new(ir, filename);
        match pass.run() {
            Ok(res) => res,
            Err(e) => {
                panic!("DumpLlvmPass Error: {}", e);
            }
        }
    };
    info!("Finish Dumping LLVM IR.");

    Ok(())
}

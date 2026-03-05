/// cli support.
use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Cli {
    /// enable this to stop running optimization passes and directly emit LLVM IR.
    #[arg(long = "emit-llvm", default_value_t = false)]
    pub emit_llvm: bool,

    #[arg(long = "dump-after", default_value_t = String::new())]
    pub dump_after: String,

    /// positional argument for input file.
    #[arg(value_name = "INPUT")]
    pub input: std::path::PathBuf,

    /// use this flag to specify output file.
    #[arg(short, long)]
    pub output: std::path::PathBuf,
}

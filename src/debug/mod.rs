use tracing_appender::non_blocking::WorkerGuard;
// use tracing_appender::rolling;
use tracing_subscriber::{fmt, prelude::*, EnvFilter};

use std::fs::File;
use std::path::PathBuf;

// Expose logging macros for outer use.
pub use tracing::{debug, info, trace, warn};
pub mod graph;
pub mod llvm;
pub use llvm::DumpLlvmPass;

// since tracing crate does not support lazy logging, we need to setup the logger at the start of the program.
pub fn setup(path: &str) -> WorkerGuard {
    const BASE_LOG_DIR: &str = "./logs";
    // let file_appender = rolling::daily(path.parent().unwrap(), path.file_name().unwrap());
    // We don't use rolling logs. We create a new file each time the program starts.
    let file = File::create(PathBuf::new().join(BASE_LOG_DIR).join(path))
        .expect("Failed to create log file");

    let (non_blocking, guard) = tracing_appender::non_blocking(file);

    tracing_subscriber::registry()
        .with(fmt::layer().with_writer(non_blocking).with_ansi(false))
        .with(fmt::layer().with_writer(std::io::stdout))
        .with(EnvFilter::new("info"))
        .init();

    guard
}

// Define an error macro that logs the error and then panics.
macro_rules! error {
    ($($arg:tt)*) => {
        tracing::error!($($arg)*);
        panic!($($arg)*);
    };
}
pub(crate) use error;

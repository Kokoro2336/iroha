// Expose logging macros for outer use.
pub mod llvm;
pub mod log;
#[allow(unused)]
pub use tracing::{debug, info, trace, warn, error};
pub use llvm::DumpLLVMPass;

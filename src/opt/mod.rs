mod compaction;
mod mem2reg;
mod dce;
mod sccp;
pub use {
    compaction::*,
    mem2reg::*,
    dce::*,
    sccp::*,
};

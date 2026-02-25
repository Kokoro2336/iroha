mod compaction;
mod mem2reg;
mod dce;
mod sccp;
pub use {
    compaction::Compaction,
    mem2reg::Mem2Reg,
    dce::DCE,
    sccp::SCCP,
};

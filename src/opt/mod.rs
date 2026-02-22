mod compaction;
mod mem2reg;
mod dce;
pub use {
    compaction::Compaction,
    mem2reg::Mem2Reg,
    dce::DCE,
};

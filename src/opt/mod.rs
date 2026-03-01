mod compaction;
mod mem2reg;
mod dce;
mod sccp;
mod remove_trivial_phi;
pub use {
    compaction::*,
    mem2reg::*,
    dce::*,
    sccp::*,
    remove_trivial_phi::*,
};

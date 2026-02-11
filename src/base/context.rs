use crate::base::ir::Operand;

pub struct LoopInfo {
    pub while_entry: Option<Operand>,
    pub end_block: Option<Operand>,
}

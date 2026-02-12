use crate::base::ir::Operand;

#[derive(Debug, Clone)]
pub struct LoopInfo {
    pub while_entry: Option<Operand>,
    pub end_block: Option<Operand>,
}

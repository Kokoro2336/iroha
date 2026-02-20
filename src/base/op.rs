use std::vec::Vec;
use strum_macros::EnumDiscriminants;

use crate::asm::config::Reg;
use crate::base::Type;
use crate::frontend::ast::Literal;
use crate::utils::arena::*;

pub type DFG = IndexedArena<Op>;

#[derive(Debug, Clone, EnumDiscriminants)]
// Specify the type enum's name
#[strum_discriminants(name(OpType))]
#[strum_discriminants(derive(Hash, Ord, PartialOrd))]
pub enum OpData {
    // customized instructions for convenience
    GlobalAlloca(u32),
    GetArg(Operand),
    // getelementptr
    GEP {
        base: Operand,
        // Vec<Index>
        indices: Vec<Operand>,
    },
    Move {
        value: Operand,
        reg: Reg,
    },
    Declare {
        name: String,
        typ: Type,
    },

    /* regular instructions */
    /// Integer
    AddI {
        lhs: Operand,
        rhs: Operand,
    },
    SubI {
        lhs: Operand,
        rhs: Operand,
    },
    MulI {
        lhs: Operand,
        rhs: Operand,
    },
    DivI {
        lhs: Operand,
        rhs: Operand,
    },
    ModI {
        lhs: Operand,
        rhs: Operand,
    },

    // The comparisons are logical.
    And {
        lhs: Operand,
        rhs: Operand,
    },
    Or {
        lhs: Operand,
        rhs: Operand,
    },
    Xor {
        lhs: Operand,
        rhs: Operand,
    },

    // Comparison(S: Signed. And SysY only has signed comparison)
    SNe {
        lhs: Operand,
        rhs: Operand,
    },
    SEq {
        lhs: Operand,
        rhs: Operand,
    },
    SGt {
        lhs: Operand,
        rhs: Operand,
    },
    SLt {
        lhs: Operand,
        rhs: Operand,
    },
    SGe {
        lhs: Operand,
        rhs: Operand,
    },
    SLe {
        lhs: Operand,
        rhs: Operand,
    },

    // Bitwise shift
    Shl {
        lhs: Operand,
        rhs: Operand,
    },
    Shr {
        lhs: Operand,
        rhs: Operand,
    },
    Sar {
        lhs: Operand,
        rhs: Operand,
    },

    /// Float
    AddF {
        lhs: Operand,
        rhs: Operand,
    },
    SubF {
        lhs: Operand,
        rhs: Operand,
    },
    MulF {
        lhs: Operand,
        rhs: Operand,
    },
    DivF {
        lhs: Operand,
        rhs: Operand,
    },
    // Mod is invalid for float in SysY

    // On the language level, SysY doesn't support And, Or, Xor for float

    // Comparison. SysY doesn't support NaN, so we only have one type of comparison here.
    ONe {
        lhs: Operand,
        rhs: Operand,
    },
    OEq {
        lhs: Operand,
        rhs: Operand,
    },
    OGt {
        lhs: Operand,
        rhs: Operand,
    },
    OLt {
        lhs: Operand,
        rhs: Operand,
    },
    OGe {
        lhs: Operand,
        rhs: Operand,
    },
    OLe {
        lhs: Operand,
        rhs: Operand,
    },

    /// Cast operations
    Sitofp {
        value: Operand,
    }, // int to float
    Fptosi {
        value: Operand,
    }, // float to int

    // SysY doesn't support bitwise shift for float
    /// Memory operations
    Store {
        addr: Operand,
        value: Operand,
    },
    Load {
        addr: Operand,
    },
    Phi {
        incoming: Vec<(Operand, Operand)>, // Vec<(value, bb_id)>
    },
    Alloca(Type),

    /// Control flow
    Call {
        func: Operand,
        args: Vec<Operand>,
    },
    Br {
        cond: Operand,
        then_bb: Operand,
        else_bb: Operand,
    },
    Jump {
        target_bb: Operand,
    },
    Ret {
        value: Option<Operand>,
    },
}

impl OpData {
    pub fn is(&self, op_typ: OpType) -> bool {
        OpType::from(self) == op_typ
    }

    pub fn is_inner_control_flow(&self) -> bool {
        matches!(self, OpData::Br { .. } | OpData::Jump { .. })
    }
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.data {
            OpData::GetArg(idx) => write!(f, "get_arg <idx = {}>", idx),
            OpData::GEP { base, indices } => {
                write!(f, "gep {}, [", base)?;
                for (i, index) in indices.iter().enumerate() {
                    write!(f, "{}", index)?;
                    if i != indices.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")
            }
            OpData::GlobalAlloca(size) => write!(f, "global_alloc {}", size),
            OpData::Move { value, reg } => write!(f, "move {}, <reg = {}>", value, reg),
            OpData::Declare { name, typ } => {
                let (ret_typ, param_typs) = match typ {
                    Type::Function {
                        return_type,
                        param_types,
                    } => (return_type, param_types),
                    _ => unreachable!("Declare op must have function type"),
                };
                write!(
                    f,
                    "declare {} @{}({})",
                    name,
                    ret_typ,
                    param_typs
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<String>>()
                        .join(", ")
                )
            }

            OpData::AddI { lhs, rhs } => write!(f, "add {}, {}", lhs, rhs),
            OpData::SubI { lhs, rhs } => write!(f, "sub {}, {}", lhs, rhs),
            OpData::MulI { lhs, rhs } => write!(f, "mul {}, {}", lhs, rhs),
            OpData::DivI { lhs, rhs } => write!(f, "div {}, {}", lhs, rhs),
            OpData::ModI { lhs, rhs } => write!(f, "mod {}, {}", lhs, rhs),

            OpData::And { lhs, rhs } => write!(f, "and {}, {}", lhs, rhs),
            OpData::Or { lhs, rhs } => write!(f, "or {}, {}", lhs, rhs),
            OpData::Xor { lhs, rhs } => write!(f, "xor {}, {}", lhs, rhs),

            OpData::SNe { lhs, rhs } => write!(f, "sne {}, {}", lhs, rhs),
            OpData::SEq { lhs, rhs } => write!(f, "seq {}, {}", lhs, rhs),
            OpData::SGt { lhs, rhs } => write!(f, "sgt {}, {}", lhs, rhs),
            OpData::SLt { lhs, rhs } => write!(f, "slt {}, {}", lhs, rhs),
            OpData::SGe { lhs, rhs } => write!(f, "sge {}, {}", lhs, rhs),
            OpData::SLe { lhs, rhs } => write!(f, "sle {}, {}", lhs, rhs),

            OpData::Shl { lhs, rhs } => write!(f, "shl {}, {}", lhs, rhs),
            OpData::Shr { lhs, rhs } => write!(f, "shr {}, {}", lhs, rhs),
            OpData::Sar { lhs, rhs } => write!(f, "sar {}, {}", lhs, rhs),

            OpData::AddF { lhs, rhs } => write!(f, "addf {}, {}", lhs, rhs),
            OpData::SubF { lhs, rhs } => write!(f, "subf {}, {}", lhs, rhs),
            OpData::MulF { lhs, rhs } => write!(f, "mulf {}, {}", lhs, rhs),
            OpData::DivF { lhs, rhs } => write!(f, "divf {}, {}", lhs, rhs),

            OpData::ONe { lhs, rhs } => write!(f, "one {}, {}", lhs, rhs),
            OpData::OEq { lhs, rhs } => write!(f, "oeq {}, {}", lhs, rhs),
            OpData::OGt { lhs, rhs } => write!(f, "ogt {}, {}", lhs, rhs),
            OpData::OLt { lhs, rhs } => write!(f, "olt {}, {}", lhs, rhs),
            OpData::OGe { lhs, rhs } => write!(f, "oge {}, {}", lhs, rhs),
            OpData::OLe { lhs, rhs } => write!(f, "ole {}, {}", lhs, rhs),

            OpData::Sitofp { value } => write!(f, "sitofp {}", value),
            OpData::Fptosi { value } => write!(f, "fptosi {}", value),

            OpData::Store { addr, value } => write!(f, "store {}, {}", addr, value),
            OpData::Load { addr } => write!(f, "load {}", addr),
            OpData::Phi { incoming } => {
                write!(f, "phi [")?;
                for (i, (value, bb_id)) in incoming.iter().enumerate() {
                    write!(f, "({}, {})", value, bb_id)?;
                    if i != incoming.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")
            }
            OpData::Alloca(size) => write!(f, "alloc {}", size),
            OpData::Call { func, args } => {
                write!(f, "call {} {:?}", func, args)
            }
            OpData::Br {
                cond,
                then_bb,
                else_bb,
            } => write!(f, "br {}, {}, {}", cond, then_bb, else_bb),
            OpData::Jump { target_bb } => write!(f, "jump {}", target_bb),
            OpData::Ret { value } => write!(f, "ret {:?}", value),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Op {
    pub typ: Type,
    pub attrs: Vec<Attr>,
    pub data: OpData,
    pub uses: Vec<Operand>,
}

impl Op {
    pub fn new(typ: Type, attrs: Vec<Attr>, data: OpData) -> Self {
        Self {
            typ,
            attrs,
            data,
            uses: vec![],
        }
    }

    pub fn is(&self, op_typ: OpType) -> bool {
        self.data.is(op_typ)
    }

    pub fn is_inner_control_flow(&self) -> bool {
        self.data.is_inner_control_flow()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operand {
    Value(usize),
    BB(usize),
    Func(usize),
    Global(usize),
    Int(i32),
    Float(f32),
    // for GEP: Raw integer index
    Index(usize),
    // for GetArg
    ParamId(u32),
    Reg(Reg),
}

impl Operand {
    pub fn get_op_id(&self) -> Result<usize, String> {
        match self {
            Operand::Value(op_id) => Ok(*op_id),
            _ => Err("Operand is not an OpId".to_string()),
        }
    }
    pub fn get_bb_id(&self) -> Result<usize, String> {
        match self {
            Operand::BB(bb_id) => Ok(*bb_id),
            _ => Err("Operand is not a BBId".to_string()),
        }
    }
    pub fn get_global_id(&self) -> Result<usize, String> {
        match self {
            Operand::Global(global_id) => Ok(*global_id),
            _ => Err("Operand is not a GlobalId".to_string()),
        }
    }
    pub fn get_int(&self) -> Result<i32, String> {
        match self {
            Operand::Int(value) => Ok(*value),
            _ => Err("Operand is not an Int".to_string()),
        }
    }
    pub fn get_float(&self) -> Result<f32, String> {
        match self {
            Operand::Float(value) => Ok(*value),
            _ => Err("Operand is not a Float".to_string()),
        }
    }
    pub fn get_param_id(&self) -> Result<u32, String> {
        match self {
            Operand::ParamId(param_id) => Ok(*param_id),
            _ => Err("Operand is not a ParamId".to_string()),
        }
    }
    pub fn get_func_id(&self) -> Result<usize, String> {
        match self {
            Operand::Func(func_id) => Ok(*func_id),
            _ => Err("Operand is not a FuncId".to_string()),
        }
    }
    pub fn get_reg(&self) -> Result<Reg, String> {
        match self {
            Operand::Reg(reg) => Ok(*reg),
            _ => Err("Operand is not a Reg".to_string()),
        }
    }
}

impl std::fmt::Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Value(op_id) => write!(f, "%{}", op_id),
            Operand::BB(bb_id) => write!(f, "%{}", bb_id),
            Operand::Global(global_id) => write!(f, "@{}", global_id),
            Operand::Int(value) => write!(f, "{}", value),
            Operand::Float(value) => write!(f, "{}", value),
            Operand::Index(index) => write!(f, "{}", index),
            Operand::ParamId(param_id) => write!(f, "{}", param_id),
            Operand::Func(func_id) => write!(f, "@{}", func_id),
            Operand::Reg(reg) => write!(f, "{}", reg),
        }
    }
}

// attributes of instructions
#[derive(Clone, Debug)]
pub enum Attr {
    // for global var
    GlobalArray {
        // if mutable -> .data; else .rodata
        name: String,
        mutable: bool,
        typ: Type,
        // None: zeroinitializer; Some: initializer list
        values: Option<Vec<Literal>>,
    },
    Promotion,
    // Name
    Name(String),
    // Old OpId for Phi
    OldIdx(Operand),
    FuncName(String),
}

impl std::fmt::Display for Attr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Attr::GlobalArray {
                name,
                mutable: _,
                typ: _,
                values: _,
            } => write!(f, "<global array: {}>", name),
            Attr::Name(name) => write!(f, "{}", name),
            Attr::Promotion => write!(f, "<promotion>"),
            Attr::OldIdx(op) => write!(f, "<old idx: {}>", op),
            Attr::FuncName(name) => write!(f, "<func name: {}>", name),
        }
    }
}

// impl dfg
impl Arena<Op> for IndexedArena<Op> {
    fn remove(&mut self, idx: usize) -> Result<Op, String> {
        // mark this slot as deleted
        if let ArenaItem::Data(data) = std::mem::replace(&mut self.storage[idx], ArenaItem::None) {
            // if the slot is occupied by data, mark it as deleted and return the data
            Ok(data)
        } else {
            Err("ArenaItem is not Op Data".to_string())
        }
    }

    fn gc(&mut self) -> Result<Vec<ArenaItem<Op>>, String> {
        let mut new_arena: Vec<ArenaItem<Op>> = vec![];

        // Transport
        for item in self.storage.iter_mut() {
            // check if the slot is occupied by data
            if matches!(item, ArenaItem::Data(_)) {
                let new_idx = new_arena.len();
                let data = item.replace(new_idx);
                new_arena.push(data);
            }
        }

        let remap_value =
            |operand: &mut Operand, old_arena: &Vec<ArenaItem<Op>>| -> Result<(), String> {
                if !matches!(operand, Operand::Value(_)) {
                    return Ok(());
                }
                let old_idx = operand.get_op_id()?;
                *operand = match old_arena.get(old_idx) {
                    Some(ArenaItem::NewIndex(new_idx)) => Operand::Value(*new_idx),
                    _ => return Err(format!("DFG gc: op index {} not found", old_idx)),
                };
                Ok(())
            };

        // rewrite idx
        for item in new_arena.iter_mut() {
            // item can't be any other variant than Data here
            if let ArenaItem::Data(node) = item {
                // rewrite uses
                for use_idx in node.uses.iter_mut() {
                    remap_value(use_idx, &self.storage)?;
                }

                // rewrite operands excluding BBId
                match &mut node.data {
                    OpData::AddI { lhs, rhs }
                    | OpData::SubI { lhs, rhs }
                    | OpData::MulI { lhs, rhs }
                    | OpData::DivI { lhs, rhs }
                    | OpData::ModI { lhs, rhs }
                    | OpData::SNe { lhs, rhs }
                    | OpData::SEq { lhs, rhs }
                    | OpData::SGt { lhs, rhs }
                    | OpData::SLt { lhs, rhs }
                    | OpData::SGe { lhs, rhs }
                    | OpData::SLe { lhs, rhs }
                    | OpData::And { lhs, rhs }
                    | OpData::Or { lhs, rhs }
                    | OpData::Xor { lhs, rhs }
                    | OpData::Shl { lhs, rhs }
                    | OpData::Shr { lhs, rhs }
                    | OpData::Sar { lhs, rhs }
                    | OpData::AddF { lhs, rhs }
                    | OpData::SubF { lhs, rhs }
                    | OpData::MulF { lhs, rhs }
                    | OpData::DivF { lhs, rhs }
                    | OpData::ONe { lhs, rhs }
                    | OpData::OEq { lhs, rhs }
                    | OpData::OGt { lhs, rhs }
                    | OpData::OLt { lhs, rhs }
                    | OpData::OGe { lhs, rhs }
                    | OpData::OLe { lhs, rhs } => {
                        remap_value(lhs, &self.storage)?;
                        remap_value(rhs, &self.storage)?;
                    }

                    OpData::Sitofp { value } | OpData::Fptosi { value } => {
                        remap_value(value, &self.storage)?;
                    }
                    OpData::Store { addr, value } => {
                        remap_value(addr, &self.storage)?;
                        remap_value(value, &self.storage)?;
                    }
                    OpData::Load { addr } => {
                        remap_value(addr, &self.storage)?;
                    }
                    OpData::Call { args, .. } => {
                        for arg in args.iter_mut() {
                            remap_value(arg, &self.storage)?;
                        }
                    }
                    OpData::Br { cond, .. } => {
                        remap_value(cond, &self.storage)?;
                    }
                    OpData::Ret { value } => {
                        if let Some(val) = value {
                            remap_value(val, &self.storage)?;
                        }
                    }

                    OpData::GEP { base, indices } => {
                        remap_value(base, &self.storage)?;
                        for index in indices.iter_mut() {
                            remap_value(index, &self.storage)?;
                        }
                    }

                    OpData::Move { value, .. } => {
                        remap_value(value, &self.storage)?;
                    }

                    OpData::Phi { incoming } => {
                        for (value, _bb_id) in incoming.iter_mut() {
                            remap_value(value, &self.storage)?;
                        }
                    }

                    // Get global should be processed outside of gc()
                    // TODO: As long as program global arena is not changed, the indices are stable.
                    OpData::GlobalAlloca { .. }
                    | OpData::GetArg { .. }
                    | OpData::Alloca(_)
                    | OpData::Jump { .. }
                    | OpData::Declare { .. } => { /* no operands to rewrite */ }
                }
            }
        }

        // replace old storage
        Ok(std::mem::replace(&mut self.storage, new_arena))
    }
}

impl IndexedArena<Op> {
    pub fn add_use(&mut self, op_idx: Operand, use_idx: Operand) -> Result<(), String> {
        let op_id = match op_idx {
            Operand::Value(op_id) => op_id,
            // literals don't have uses in the DFG
            // For global variables, we don't maintain uses in the DFG, so just return.
            Operand::Int(_) | Operand::Float(_) | Operand::Global(_) => return Ok(()),
            _ => return Err(format!("Operand is not a valid data: {:?}", op_idx)),
        };

        if let Some(node) = self.get_mut(op_id)? {
            node.uses.push(use_idx);
            Ok(())
        } else {
            Err(format!("DFG add_use: op index {} not found", op_id))
        }
    }

    // @param op_idx: the op whose uses we want to replace with new operand. e.g. "add %1, %2"
    // @param old: the old use we want to replace with e.g. %1 in "add %1, %2"
    // @param new: the new use we want to replace with e.g. %3 in "add %3, %2"
    pub fn replace_use(
        &mut self,
        op_idx: Operand,
        old: Operand,
        new: Operand,
    ) -> Result<(), String> {
        let op_id = match op_idx {
            Operand::Value(op_id) => op_id,
            // literals don't have uses in the DFG
            // For global variables, we don't maintain uses in the DFG, so just return.
            Operand::Int(_) | Operand::Float(_) | Operand::Global(_) => return Ok(()),
            _ => return Err("Operand is not a valid data".to_string()),
        };

        if let Some(op) = self.get_mut(op_id)? {
            match &mut op.data {
                OpData::AddI { lhs, rhs }
                | OpData::SubI { lhs, rhs }
                | OpData::MulI { lhs, rhs }
                | OpData::DivI { lhs, rhs }
                | OpData::ModI { lhs, rhs }
                | OpData::SNe { lhs, rhs }
                | OpData::SEq { lhs, rhs }
                | OpData::SGt { lhs, rhs }
                | OpData::SLt { lhs, rhs }
                | OpData::SGe { lhs, rhs }
                | OpData::SLe { lhs, rhs }
                | OpData::And { lhs, rhs }
                | OpData::Or { lhs, rhs }
                | OpData::Xor { lhs, rhs }
                | OpData::Shl { lhs, rhs }
                | OpData::Shr { lhs, rhs }
                | OpData::Sar { lhs, rhs }
                | OpData::AddF { lhs, rhs }
                | OpData::SubF { lhs, rhs }
                | OpData::MulF { lhs, rhs }
                | OpData::DivF { lhs, rhs }
                | OpData::ONe { lhs, rhs }
                | OpData::OEq { lhs, rhs }
                | OpData::OGt { lhs, rhs }
                | OpData::OLt { lhs, rhs }
                | OpData::OGe { lhs, rhs }
                | OpData::OLe { lhs, rhs } => {
                    if *lhs == old {
                        *lhs = new.clone();
                    };
                    if *rhs == old {
                        *rhs = new.clone();
                    };
                }

                OpData::Sitofp { value: value } | OpData::Fptosi { value: value } => {
                    if *value == old {
                        *value = new.clone();
                    };
                }
                OpData::Store { addr, value } => {
                    if *addr == old {
                        *addr = new.clone();
                    };
                    if *value == old {
                        *value = new.clone();
                    };
                }
                OpData::Load { addr } => {
                    if *addr == old {
                        *addr = new.clone();
                    };
                }
                OpData::Call { args, .. } => {
                    for arg in args.iter_mut() {
                        if *arg == old {
                            *arg = new.clone();
                        };
                    }
                }
                OpData::Br { cond, .. } => {
                    if *cond == old {
                        *cond = new.clone();
                    };
                }
                OpData::Ret { value } => {
                    if let Some(val) = value {
                        if *val == old {
                            *val = new.clone();
                        };
                    }
                }
                OpData::GEP { base, indices } => {
                    if *base == old {
                        *base = new.clone();
                    };
                    for index in indices.iter_mut() {
                        if *index == old {
                            *index = new.clone();
                        };
                    }
                }
                OpData::Move { value, .. } => {
                    if *value == old {
                        *value = new.clone();
                    };
                }
                OpData::Phi { incoming } => {
                    for (value, _bb_id) in incoming.iter_mut() {
                        if *value == old {
                            *value = new.clone();
                        };
                    }
                }
                OpData::GlobalAlloca { .. }
                | OpData::GetArg { .. }
                | OpData::Alloca(_)
                | OpData::Jump { .. }
                | OpData::Declare { .. } => { /* no operands to replace */ }
            }
            Ok(())
        } else {
            Err("DFG replace_use: op index not found".to_string())
        }
    }
}

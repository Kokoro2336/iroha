use std::ops::{Index, IndexMut};
use std::vec::Vec;
use strum_macros::EnumDiscriminants;

use crate::base::Type;
use crate::debug::info;
use crate::frontend::ast::Literal;
use crate::utils::arena::*;

#[allow(clippy::upper_case_acronyms)]
pub type DFG = IndexedArena<Op>;

#[derive(Debug, Clone, EnumDiscriminants)]
// Specify the type enum's name
#[strum_discriminants(name(OpType))]
#[strum_discriminants(derive(Hash, Ord, PartialOrd))]
#[allow(clippy::upper_case_acronyms)]
pub enum OpData {
    // customized instructions for convenience
    GlobalAlloca(u32),
    // getelementptr
    GEP {
        base: Operand,
        // Vec<Index>
        indices: Vec<Operand>,
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
    #[allow(unused)]
    Shl {
        lhs: Operand,
        rhs: Operand,
    },
    #[allow(unused)]
    Shr {
        lhs: Operand,
        rhs: Operand,
    },
    #[allow(unused)]
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
    Uitofp {
        value: Operand,
    }, // bool to float
    Zext {
        value: Operand,
    }, // bool to int

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
        incoming: Vec<PhiIncoming>, // Vec<(value, bb_id)>
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

#[derive(Debug, Clone)]
pub enum PhiIncoming {
    Data { value: Operand, bb: Operand },
    None,
}

impl OpData {
    pub fn is(&self, op_typ: OpType) -> bool {
        OpType::from(self) == op_typ
    }

    pub fn is_impure(&self) -> bool {
        matches!(
            self,
            // In DCE, Load is pure.
            OpData::Call { .. }
                | OpData::Store { .. }
                | OpData::Br { .. }
                | OpData::Jump { .. }
                | OpData::Ret { .. }
                | OpData::Alloca(_)
                | OpData::GlobalAlloca(_)
                | OpData::Declare { .. }
        )
    }
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.data {
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
            OpData::Uitofp { value } => write!(f, "uitofp {}", value),
            OpData::Zext { value } => write!(f, "zext {}", value),

            OpData::Store { addr, value } => write!(f, "store {}, {}", addr, value),
            OpData::Load { addr } => write!(f, "load {}", addr),
            OpData::Phi { incoming } => {
                write!(f, "phi [")?;
                for (i, phi_incoming) in incoming.iter().enumerate() {
                    if let PhiIncoming::Data { value, bb } = phi_incoming {
                        write!(f, "({}, {})", value, bb)?;
                        if i != incoming.len() - 1 {
                            write!(f, ", ")?;
                        }
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

impl Index<Operand> for DFG {
    type Output = Op;

    fn index(&self, index: Operand) -> &Self::Output {
        match index {
            Operand::Value(id) => self.get(id).unwrap(),
            _ => panic!("DFG index: expected Operand::Value, got {:?}", index),
        }
    }
}

impl IndexMut<Operand> for DFG {
    fn index_mut(&mut self, index: Operand) -> &mut Self::Output {
        match index {
            Operand::Value(id) => self.get_mut(id).unwrap(),
            _ => panic!("DFG index_mut: expected Operand::Value, got {:?}", index),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Op {
    pub typ: Type,
    pub attrs: Vec<Attr>,
    pub data: OpData,
    pub users: Vec<Operand>,
}

impl Op {
    pub fn new(typ: Type, attrs: Vec<Attr>, data: OpData) -> Self {
        Self {
            typ,
            attrs,
            data,
            users: vec![],
        }
    }

    pub fn is(&self, op_typ: OpType) -> bool {
        self.data.is(op_typ)
    }

    pub fn is_impure(&self) -> bool {
        self.data.is_impure()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operand {
    // Ids
    Value(usize),
    BB(usize),
    Func(usize),
    Global(usize),

    // Literals
    Int(i32),
    Float(f32),
    Bool(bool),

    // Param
    Param { idx: usize, name: String, typ: Type },
    // for phi
    Undefined,
}

impl From<Operand> for usize {
    fn from(operand: Operand) -> Self {
        match operand {
            Operand::Value(id) => id,
            Operand::Global(id) => id,
            Operand::BB(id) => id,
            Operand::Func(id) => id,
            _ => panic!("Operand cannot be converted to usize: {:?}", operand),
        }
    }
}

#[allow(unused)]
impl Operand {
    pub fn get_op_id(&self) -> usize {
        match self {
            Operand::Value(op_id) => *op_id,
            _ => panic!("Operand is not a Value operand: {:?}", self),
        }
    }
    pub fn get_bb_id(&self) -> usize {
        match self {
            Operand::BB(bb_id) => *bb_id,
            _ => panic!("Operand is not a BBId: {:?}", self),
        }
    }
    pub fn get_global_id(&self) -> usize {
        match self {
            Operand::Global(global_id) => *global_id,
            _ => panic!("Operand is not a GlobalId: {:?}", self),
        }
    }
    pub fn get_int(&self) -> i32 {
        match self {
            Operand::Int(value) => *value,
            _ => panic!("Operand is not an Int: {:?}", self),
        }
    }
    pub fn get_float(&self) -> f32 {
        match self {
            Operand::Float(value) => *value,
            _ => panic!("Operand is not a Float: {:?}", self),
        }
    }
    pub fn get_func_id(&self) -> usize {
        match self {
            Operand::Func(func_id) => *func_id,
            _ => panic!("Operand is not a FuncId: {:?}", self),
        }
    }
    pub fn is_literal(&self) -> bool {
        matches!(self, Operand::Int(_) | Operand::Float(_) | Operand::Bool(_))
    }
}

impl std::fmt::Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Value(op_id) => write!(f, "%val_{}", op_id),
            Operand::BB(bb_id) => write!(f, "%{}", bb_id),
            Operand::Global(global_id) => write!(f, "@{}", global_id),
            Operand::Int(value) => write!(f, "{}", value),
            Operand::Float(value) => write!(f, "{}", value),
            Operand::Bool(value) => write!(f, "{}", value),
            Operand::Param { idx, .. } => write!(f, "%arg{}", idx),
            Operand::Func(func_id) => write!(f, "@{}", func_id),
            Operand::Undefined => write!(f, "undefined"),
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
    fn remove(&mut self, idx: usize) -> Op {
        // mark this slot as deleted
        if let ArenaItem::Data(data) = std::mem::replace(&mut self.storage[idx], ArenaItem::None) {
            // if the slot is occupied by data, mark it as deleted and return the data
            data
        } else {
            panic!("DFG remove: index {} is not occupied by data", idx);
        }
    }

    fn gc(&mut self) -> Vec<ArenaItem<Op>> {
        let new_arena: Vec<ArenaItem<Op>> = vec![];
        let mut old_arena = std::mem::replace(&mut self.storage, new_arena);

        // Transport
        old_arena.iter_mut().for_each(|item| {
            if matches!(item, ArenaItem::Data(_)) {
                let new_idx = self.storage.len();
                let data = item.replace(new_idx);
                self.storage.push(data);
            }
        });

        info!(
            "DFG GC: {} ops collected, recycle rate: {:.2}%",
            old_arena.len() - self.storage.len(),
            (old_arena.len() - self.storage.len()) as f64 / old_arena.len() as f64 * 100.0
        );

        #[allow(unused)]
        let remap_idx = |idx: &mut usize, old_arena: &Vec<ArenaItem<Op>>| {
            *idx = match old_arena.get(*idx) {
                Some(ArenaItem::NewIndex(new_idx)) => *new_idx,
                _ => panic!(
                    "DFG gc: index {} is not a valid NewIndex: {:?}",
                    *idx,
                    old_arena.get(*idx)
                ),
            };
        };

        // TODO: Remap Index when using Invaded List.
        // if let Some(entry) = self.entry.as_mut() {
        //     remap_idx(entry, &old_arena);
        // }

        // for idx in self.map.values_mut() {
        //     remap_idx(idx, &old_arena);
        // }

        let remap_value = |operand: &mut Operand, old_arena: &Vec<ArenaItem<Op>>| {
            if !matches!(operand, Operand::Value(_)) {
                return;
            }
            let old_idx = operand.get_op_id();
            *operand = match old_arena.get(old_idx) {
                Some(ArenaItem::NewIndex(new_idx)) => Operand::Value(*new_idx),
                _ => panic!(
                    "DFG gc: index {} not found for operand {:?}",
                    old_idx, operand
                ),
            };
        };

        // rewrite idx
        for item in self.storage.iter_mut() {
            // item can't be any other variant than Data here
            if let ArenaItem::Data(node) = item {
                // rewrite uses
                for use_idx in node.users.iter_mut() {
                    remap_value(use_idx, &old_arena);
                }

                // rewrite Attr
                node.attrs.iter_mut().for_each(|attr| {
                    match attr {
                        Attr::OldIdx(op) => remap_value(op, &old_arena),
                        Attr::GlobalArray { .. }
                        | Attr::Name(_)
                        | Attr::Promotion
                        | Attr::FuncName(_) => { /* no idx to rewrite */ }
                    }
                });

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
                        remap_value(lhs, &old_arena);
                        remap_value(rhs, &old_arena);
                    }

                    OpData::Sitofp { value }
                    | OpData::Fptosi { value }
                    | OpData::Uitofp { value }
                    | OpData::Zext { value } => {
                        remap_value(value, &old_arena);
                    }
                    OpData::Store { addr, value } => {
                        remap_value(addr, &old_arena);
                        remap_value(value, &old_arena);
                    }
                    OpData::Load { addr } => {
                        remap_value(addr, &old_arena);
                    }
                    OpData::Call { args, .. } => {
                        for arg in args.iter_mut() {
                            remap_value(arg, &old_arena);
                        }
                    }
                    OpData::Br { cond, .. } => {
                        remap_value(cond, &old_arena);
                    }
                    OpData::Ret { value } => {
                        if let Some(val) = value {
                            remap_value(val, &old_arena);
                        }
                    }

                    OpData::GEP { base, indices } => {
                        remap_value(base, &old_arena);
                        for index in indices.iter_mut() {
                            remap_value(index, &old_arena);
                        }
                    }

                    OpData::Phi { incoming } => {
                        for phi_incoming in incoming.iter_mut() {
                            if let PhiIncoming::Data { value, .. } = phi_incoming {
                                remap_value(value, &old_arena);
                            }
                        }
                    }

                    OpData::GlobalAlloca { .. }
                    | OpData::Alloca(_)
                    | OpData::Jump { .. }
                    | OpData::Declare { .. } => { /* no operands to rewrite */ }
                }
            }
        }

        // replace old storage
        old_arena
    }
}

impl IndexedArena<Op> {
    pub fn add_use(&mut self, op_idx: Operand, use_idx: Operand) {
        let op_id = match op_idx {
            Operand::Value(op_id) => op_id,
            Operand::Global(global_id) => global_id,
            // literals don't have uses in the DFG
            // For global variables, we don't maintain uses in the DFG, so just return.
            Operand::Int(_)
            | Operand::Float(_)
            | Operand::Bool(_)
            | Operand::Undefined
            | Operand::Param { .. } => return,
            _ => panic!("Operand is not a valid data: {:?}", op_idx),
        };
        let node = &mut self[op_id];
        // Check whether the use already exists to avoid duplicates
        if node.users.contains(&use_idx) {
            return;
        }
        node.users.push(use_idx);
    }

    // Remove use_idx from the users of op_idx.
    pub fn remove_use(&mut self, op_idx: Operand, use_idx: Operand) {
        let op_id = match op_idx {
            Operand::Value(op_id) => op_id,
            Operand::Global(global_id) => global_id,
            // literals don't have uses in the DFG
            // For global variables, we don't maintain uses in the DFG, so just return.
            Operand::Int(_)
            | Operand::Float(_)
            | Operand::Bool(_)
            | Operand::Undefined
            | Operand::Param { .. } => return,
            _ => panic!(
                "Operand is not a valid data: {}: {:?}",
                op_idx.clone(),
                self[op_idx]
            ),
        };
        let node = &mut self[op_id];
        if let Some(pos) = node.users.iter().position(|x| *x == use_idx) {
            node.users.swap_remove(pos);
        } else {
            panic!(
                "Use {}: {:?} not found in users of op {}: {:?}",
                use_idx.clone(),
                self[use_idx],
                op_idx.clone(),
                self[op_idx]
            );
        }
    }

    // @param op_idx: the op whose uses we want to replace with new operand. e.g. "add %1, %2"
    // @param old: the old use we want to replace with e.g. %1 in "add %1, %2"
    // @param new: the new use we want to replace with e.g. %3 in "add %3, %2"
    pub fn replace_use(&mut self, op_idx: Operand, old: Operand, new: Operand) {
        let op_id = match op_idx {
            Operand::Value(op_id) => op_id,
            Operand::Global(global_id) => global_id,
            // literals don't have uses in the DFG
            // For global variables, we don't maintain uses in the DFG, so just return.
            Operand::Int(_)
            | Operand::Float(_)
            | Operand::Bool(_)
            | Operand::Undefined
            | Operand::Param { .. } => return,
            _ => panic!("Operand is not a valid data: {:?}", op_idx),
        };

        let op = &mut self[op_id];
        // Update Use
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

            OpData::Sitofp { value }
            | OpData::Fptosi { value }
            | OpData::Uitofp { value }
            | OpData::Zext { value } => {
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
            OpData::Phi { incoming } => {
                for phi_incoming in incoming.iter_mut() {
                    if let PhiIncoming::Data { value, .. } = phi_incoming {
                        if *value == old {
                            *value = new.clone();
                        };
                    }
                }
            }
            OpData::GlobalAlloca { .. }
            | OpData::Alloca(_)
            | OpData::Jump { .. }
            | OpData::Declare { .. } => { /* no operands to replace */ }
        }
        // Delete old user
        self.remove_use(old, op_idx.clone());
        // Add new user
        self.add_use(new, op_idx);
    }
}

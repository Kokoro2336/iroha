use crate::base::ir::{OpData, Operand, PhiIncoming, Program, OpType};
use crate::base::Builder;
/**
 * Sparse Conditional Constant Propagation (SCCP).
 * Based on Wegman and Zadeck's paper Constant Propagation with Conditional Branches.
 * Reference: https://dl.acm.org/doi/10.1145/103135.103136
 */
use crate::base::Pass;
use crate::utils::bitset::BitSet;

use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq)]
pub enum Lattice {
    Optimistic,
    Constant(Operand),
    Overdefined,
}

pub struct SCCP<'a> {
    program: &'a mut Program,
    builder: Builder,

    // HashSet<(from, to)> for edges in the control flow graph that are executable. Only store true.
    executable: HashSet<(Operand, Operand)>,
    lattices: Vec<Lattice>,

    // Worklists
    // Vec<(from, to)> for CFG edges that need to be processed.
    edge_list: Vec<(Operand, Operand)>,
    // Vec<(OpId, BBId)>
    inst_list: Vec<Operand>,
    in_inst_list: BitSet,

    current_function: Option<usize>,
}

impl<'a> SCCP<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        Self {
            program,
            builder: Builder::new(),
            executable: HashSet::default(),
            lattices: Vec::new(),
            edge_list: Vec::new(),
            inst_list: Vec::new(),
            in_inst_list: BitSet::new(),
            current_function: None,
        }
    }

    fn meet(lattices: Vec<Lattice>) -> Lattice {
        if lattices.is_empty() {
            return Lattice::Optimistic;
        }
        let mut result = lattices[0].clone();
        for lattice in lattices.into_iter().skip(1) {
            result = Self::meet_two(result, lattice);
        }
        result
    }

    fn meet_two(old: Lattice, new: Lattice) -> Lattice {
        match (old, new) {
            (Lattice::Optimistic, origin) | (origin, Lattice::Optimistic) => origin,
            (Lattice::Constant(c1), Lattice::Constant(c2)) => {
                if c1 == c2 {
                    Lattice::Constant(c1)
                } else {
                    Lattice::Overdefined
                }
            }
            (Lattice::Overdefined, _) | (_, Lattice::Overdefined) => Lattice::Overdefined,
        }
    }

    fn fold(lhs: Lattice, rhs: Lattice, op_typ: OpType) -> Lattice {
        let (lhs, rhs) = match (lhs, rhs) {
            (Lattice::Constant(c1), Lattice::Constant(c2)) => (c1, c2),
            _ => panic!("SCCP fold: both operands must be constants"),
        };
        match (lhs, rhs) {
            (Operand::Int(i1), Operand::Int(i2)) => {
                match &op_typ {
                    OpType::AddI => Lattice::Constant(Operand::Int(i1 + i2)),
                    OpType::SubI => Lattice::Constant(Operand::Int(i1 - i2)),
                    OpType::MulI => Lattice::Constant(Operand::Int(i1 * i2)),
                    OpType::DivI => Lattice::Constant(Operand::Int(i1 / i2)),
                    OpType::ModI => Lattice::Constant(Operand::Int(i1 % i2)),
                    OpType::Xor => Lattice::Constant(Operand::Int(i1 ^ i2)),
                    OpType::Shl => Lattice::Constant(Operand::Int(i1 << i2)),
                    OpType::Shr => Lattice::Constant(Operand::Int(i1 >> i2)),
                    OpType::Sar => Lattice::Constant(Operand::Int(((i1 as i64) >> i2) as i32)),
                    OpType::SNe => Lattice::Constant(Operand::Bool(i1 != i2)),
                    OpType::SEq => Lattice::Constant(Operand::Bool(i1 == i2)),
                    OpType::SGt => Lattice::Constant(Operand::Bool(i1 > i2)),
                    OpType::SLt => Lattice::Constant(Operand::Bool(i1 < i2)),
                    OpType::SGe => Lattice::Constant(Operand::Bool(i1 >= i2)),
                    OpType::SLe => Lattice::Constant(Operand::Bool(i1 <= i2)),
                    _ => panic!("{:?}'s operands can't be folded as integers", op_typ),
                }
            }
            (Operand::Float(f1), Operand::Float(f2)) => {
                match &op_typ {
                    OpType::AddF => Lattice::Constant(Operand::Float(f1 + f2)),
                    OpType::SubF => Lattice::Constant(Operand::Float(f1 - f2)),
                    OpType::MulF => Lattice::Constant(Operand::Float(f1 * f2)),
                    OpType::DivF => Lattice::Constant(Operand::Float(f1 / f2)),
                    OpType::ONe => Lattice::Constant(Operand::Bool(f1 != f2)),
                    OpType::OEq => Lattice::Constant(Operand::Bool(f1 == f2)),
                    OpType::OGt => Lattice::Constant(Operand::Bool(f1 > f2)),
                    OpType::OLt => Lattice::Constant(Operand::Bool(f1 < f2)),
                    _ => panic!("{:?}'s operands can't be folded as floats", op_typ),
                }
            }
            (Operand::Bool(b1), Operand::Bool(b2)) => {
                match &op_typ {
                    OpType::And => Lattice::Constant(Operand::Bool(b1 && b2)),
                    OpType::Or => Lattice::Constant(Operand::Bool(b1 || b2)),
                    OpType::Xor => Lattice::Constant(Operand::Bool(b1 ^ b2)),
                    _ => panic!("{:?}'s operands can't be folded as booleans", op_typ),
                }
            }
            _ => panic!("SCCP fold: both operands must be of the same type"),
        }
    }

    fn init(&mut self, idx: usize) {
        self.current_function = Some(idx);
        let func = &self.program.funcs[idx];
        let entry = match func.cfg.entry {
            Some(e) => e,
            None => return, // empty function
        };

        self.lattices
            .resize(func.dfg.storage.len(), Lattice::Optimistic);
        self.executable.clear();
        self.edge_list.clear();
        self.edge_list.extend(
            func.cfg[entry]
                .succs
                .iter()
                .map(|succ| (Operand::BB(entry), succ.clone()))
                .collect::<Vec<(Operand, Operand)>>(),
        );
        self.inst_list.clear();
        self.in_inst_list.clear();
    }

    fn visit_expr(&mut self, op_id: Operand) {
        let func = match self.current_function {
            Some(idx) => idx,
            None => panic!("SCCP visit_expr: current_function is None"), // should not happen
        };
        let op_data = self.program.funcs[func].dfg[op_id.clone()].data.clone();
        let old = self.lattices[op_id.get_op_id()].clone();

        match op_data {
            OpData::AddF { lhs, rhs }
            | OpData::SubF { lhs, rhs }
            | OpData::MulF { lhs, rhs }
            | OpData::DivF { lhs, rhs }
            | OpData::AddI { lhs, rhs }
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
            | OpData::OEq { lhs, rhs }
            | OpData::OGt { lhs, rhs }
            | OpData::OLt { lhs, rhs }
            | OpData::OGe { lhs, rhs }
            | OpData::OLe { lhs, rhs }
            | OpData::ONe { lhs, rhs }
            | OpData::And { lhs, rhs }
            | OpData::Or { lhs, rhs }
            | OpData::Xor { lhs, rhs }
            | OpData::Shl { lhs, rhs }
            | OpData::Shr { lhs, rhs }
            | OpData::Sar { lhs, rhs } => {
                // Fold the const first
                let lattice_list = {
                    let mut list = Vec::new();
                    // DO NOT invoke get_xx_id() directly. We just ignore non-value operands, never panics.
                    if let Operand::Value(lhs_id) = lhs {
                        list.push(self.lattices[lhs_id].clone());
                    }
                    if let Operand::Value(rhs_id) = rhs {
                        list.push(self.lattices[rhs_id].clone());
                    }
                    list
                };
                self.lattices[op_id.get_op_id()] = Self::meet(lattice_list);

                if old == self.lattices[op_id.get_op_id()] {
                    return;
                }

                // If the lattice has changed, we need to propagate the change to users.
                for user in self.program.funcs[func].dfg[op_id.clone()].users.iter() {
                    if !self.in_inst_list.contains(user.get_op_id()) {
                        self.in_inst_list.insert(user.get_op_id());
                        self.inst_list.push(user.clone());
                    }
                }
            }
            OpData::Sitofp { value } | OpData::Fptosi { value } => {
                // Return the lattice of the operand directly for simplicity
                if let Operand::Value(value_id) = value {
                    self.lattices[op_id.get_op_id()] = self.lattices[value_id].clone()
                }
                if old == self.lattices[op_id.get_op_id()] {
                    return;
                }
                // If the lattice has changed, we need to propagate the change to users.
                for user in self.program.funcs[func].dfg[op_id.clone()].users.iter() {
                    if !self.in_inst_list.contains(user.get_op_id()) {
                        self.in_inst_list.insert(user.get_op_id());
                        self.inst_list.push(user.clone());
                    }
                }
            }

            OpData::GEP { .. } | OpData::Load { .. } | OpData::Call { .. } => {
                self.lattices[op_id.get_op_id()] = Lattice::Overdefined;
                if old == self.lattices[op_id.get_op_id()] {
                    return;
                }
                // If the lattice has changed, we need to propagate the change to users.
                for user in self.program.funcs[func].dfg[op_id.clone()].users.iter() {
                    if !self.in_inst_list.contains(user.get_op_id()) {
                        self.in_inst_list.insert(user.get_op_id());
                        self.inst_list.push(user.clone());
                    }
                }
            }

            OpData::Phi { .. } => unreachable!("Phi nodes should be handled in visit_phi()"),

            OpData::Br { cond, .. } => {
                
            }
            OpData::Jump { .. } | OpData::Ret { .. } => { /* do nothing */ }

            // SCCP doesn't care about these ops.
            OpData::Alloca(_)
            | OpData::GlobalAlloca(_)
            | OpData::Store { .. }
            | OpData::Declare { .. }
            | OpData::Move { .. } => return,
        }
    }

    fn propagate(&mut self) {
        while !(self.edge_list.is_empty() && self.inst_list.is_empty()) {
            // Handle flow graph edge
            if let Some((from, to)) = self.edge_list.pop() {
                if self.executable.contains(&(from.clone(), to.clone())) {
                    continue;
                }
                self.executable.insert((from.clone(), to.clone()));
            }
        }
    }
}

struct Rewrite;

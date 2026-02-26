/**
 * Sparse Conditional Constant Propagation (SCCP).
 * Based on Wegman and Zadeck's paper Constant Propagation with Conditional Branches.
 * Reference: https://dl.acm.org/doi/10.1145/103135.103136
 */
use crate::base::ir::{Op, OpData, OpType, Operand, PhiIncoming, Program};
use crate::base::{context_or_err, Builder, BuilderContext, Pass, Type};
use crate::debug::info;
use crate::opt::RemoveTrivialPhi;
use crate::utils::arena::{Arena, ArenaItem};
use crate::utils::bitset::BitSet;

use rustc_hash::FxHashSet;

#[derive(Debug, Clone, PartialEq)]
pub enum Lattice {
    Top,
    Constant(Operand),
    Bottom,
}

pub struct SCCP<'a> {
    program: &'a mut Program,
    builder: Builder,

    // HashSet<(from, to)> for edges in the control flow graph that are executable. Only store true.
    executable: FxHashSet<(usize, usize)>,
    // Lattices
    lattices: Vec<Lattice>,
    // Whether the block has been visited. We use BitSet for fast lookup.
    visited: BitSet,
    // Whether the instruction is already in the worklist. We use BitSet for fast lookup.
    in_inst_list: BitSet,

    // Worklists
    // Vec<(from, to)> for CFG edges that need to be processed.
    edge_list: Vec<(Operand, Operand)>,
    // Vec<(OpId, BBId)>
    inst_list: Vec<Operand>,

    // Ancillary infrastructure
    // We need to know the mapping from op_id to bb_id for phi nodes.
    op_to_bb: Vec<Operand>,
    phi_ops: Vec<Operand>,
    in_phi_ops: BitSet,
    // br_ops excluding ret.
    br_ops: Vec<Operand>,
    in_br_ops: BitSet,

    current_function: Option<usize>,
}

impl<'a> SCCP<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        Self {
            program,
            builder: Builder::new(),
            executable: FxHashSet::default(),
            lattices: Vec::new(),
            edge_list: Vec::new(),
            inst_list: Vec::new(),
            in_inst_list: BitSet::new(),
            visited: BitSet::new(),
            op_to_bb: Vec::new(),
            phi_ops: Vec::new(),
            in_phi_ops: BitSet::new(),
            br_ops: Vec::new(),
            in_br_ops: BitSet::new(),
            current_function: None,
        }
    }

    fn meet(lattices: Vec<Lattice>) -> Lattice {
        if lattices.is_empty() {
            return Lattice::Top;
        }
        let mut result = lattices[0].clone();
        for lattice in lattices.into_iter().skip(1) {
            result = Self::meet_two(result, lattice);
        }
        result
    }

    fn meet_two(old: Lattice, new: Lattice) -> Lattice {
        match (old, new) {
            (Lattice::Top, origin) | (origin, Lattice::Top) => origin,
            (Lattice::Constant(c1), Lattice::Constant(c2)) => {
                if c1 == c2 {
                    Lattice::Constant(c1)
                } else {
                    Lattice::Bottom
                }
            }
            (Lattice::Bottom, _) | (_, Lattice::Bottom) => Lattice::Bottom,
        }
    }

    // If the operand is a value, return its lattice.
    // If it's a constant, return the constant lattice.
    // The functio doesn't support other types of operands and will panic if called with them.
    fn get_lattice(&self, operand: &Operand) -> Lattice {
        match operand {
            Operand::Value(id) => self.lattices[*id].clone(),
            Operand::Int(_) | Operand::Float(_) | Operand::Bool(_) | Operand::Index(_) => {
                Lattice::Constant(operand.clone())
            }

            Operand::Undefined => Lattice::Top,

            Operand::Global(_) | Operand::Param { .. } => Lattice::Bottom,

            Operand::BB(_) | Operand::Func(_) | Operand::Reg(_) => panic!(
                "SCCP get_lattice: operand {:?} is not a value or constant",
                operand
            ),
        }
    }

    fn fold(lhs: Lattice, rhs: Lattice, op_typ: OpType) -> Lattice {
        let (lhs, rhs) = match (lhs, rhs) {
            (Lattice::Constant(c1), Lattice::Constant(c2)) => (c1, c2),
            _ => panic!("SCCP fold: both operands must be constants"),
        };
        match (lhs, rhs) {
            (Operand::Int(i1), Operand::Int(i2)) => match &op_typ {
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
            },
            (Operand::Float(f1), Operand::Float(f2)) => match &op_typ {
                OpType::AddF => Lattice::Constant(Operand::Float(f1 + f2)),
                OpType::SubF => Lattice::Constant(Operand::Float(f1 - f2)),
                OpType::MulF => Lattice::Constant(Operand::Float(f1 * f2)),
                OpType::DivF => Lattice::Constant(Operand::Float(f1 / f2)),
                OpType::ONe => Lattice::Constant(Operand::Bool(f1 != f2)),
                OpType::OEq => Lattice::Constant(Operand::Bool(f1 == f2)),
                OpType::OGt => Lattice::Constant(Operand::Bool(f1 > f2)),
                OpType::OLt => Lattice::Constant(Operand::Bool(f1 < f2)),
                OpType::OLe => Lattice::Constant(Operand::Bool(f1 <= f2)),
                OpType::OGe => Lattice::Constant(Operand::Bool(f1 >= f2)),
                _ => panic!("{:?}'s operands can't be folded as floats", op_typ),
            },
            (Operand::Bool(b1), Operand::Bool(b2)) => match &op_typ {
                OpType::And => Lattice::Constant(Operand::Bool(b1 && b2)),
                OpType::Or => Lattice::Constant(Operand::Bool(b1 || b2)),
                OpType::Xor => Lattice::Constant(Operand::Bool(b1 ^ b2)),
                _ => panic!("{:?}'s operands can't be folded as booleans", op_typ),
            },
            _ => panic!("SCCP fold: both operands must be of the same type"),
        }
    }

    fn cast(operand: Lattice, op_typ: OpType) -> Lattice {
        let operand = match operand {
            Lattice::Constant(c) => c,
            _ => panic!("SCCP cast: operand must be a constant"),
        };
        match operand {
            Operand::Int(i) => match &op_typ {
                OpType::Sitofp => Lattice::Constant(Operand::Float(i as f32)),
                _ => unreachable!(),
            },
            Operand::Float(f) => match &op_typ {
                OpType::Fptosi => Lattice::Constant(Operand::Int(f as i32)),
                _ => unreachable!(),
            },
            Operand::Bool(b) => match &op_typ {
                OpType::Zext => Lattice::Constant(Operand::Int(if b { 1 } else { 0 })),
                OpType::Uitofp => Lattice::Constant(Operand::Float(if b { 1.0 } else { 0.0 })),
                _ => unreachable!(),
            },
            _ => panic!("SCCP cast: operand must be an integer, float or boolean constant"),
        }
    }

    fn init(&mut self, idx: usize) {
        self.current_function = Some(idx);
        let func = &self.program.funcs[idx];
        let entry = match func.cfg.entry {
            Some(e) => e,
            None => return, // empty function
        };

        self.lattices.resize(func.dfg.storage.len(), Lattice::Top);

        // map OpId to BBId
        self.op_to_bb.clear();
        self.op_to_bb.resize(func.dfg.storage.len(), Operand::BB(0));
        func.cfg
            .storage
            .iter()
            .enumerate()
            .for_each(|(bb_id, item)| {
                if let ArenaItem::Data(bb) = item {
                    for op_id in bb.cur.iter() {
                        self.op_to_bb[op_id.get_op_id()] = Operand::BB(bb_id);
                    }
                }
            });

        self.executable.clear();
        self.visited.clear();
        self.edge_list.clear();

        self.edge_list.extend(
            func.cfg[entry]
                .succs
                .iter()
                .map(|succ| (Operand::BB(entry), succ.clone()))
                .collect::<Vec<(Operand, Operand)>>(),
        );
        self.visited.insert(entry);

        self.inst_list.clear();
        self.in_inst_list.clear();

        self.phi_ops.clear();
        self.in_phi_ops.clear();
        self.br_ops.clear();
        self.in_br_ops.clear();
    }

    fn visit_expr(&mut self, op_id: Operand, bb_id: Operand) {
        let func = match self.current_function {
            Some(idx) => idx,
            None => panic!("SCCP visit_expr: current_function is None"), // should not happen
        };
        let op_data = self.program.funcs[func].dfg[op_id.clone()].data.clone();
        let old = self.lattices[op_id.get_op_id()].clone();

        match op_data.clone() {
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
                let left_lattice = self.get_lattice(&lhs);
                let right_lattice = self.get_lattice(&rhs);
                if matches!(left_lattice, Lattice::Constant(_))
                    && matches!(right_lattice, Lattice::Constant(_))
                {
                    self.lattices[op_id.get_op_id()] =
                        Self::fold(left_lattice, right_lattice, OpType::from(&op_data));
                } else {
                    // If not foldable, we just meet the lattices of the operands.
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

            OpData::Sitofp { value }
            | OpData::Fptosi { value }
            | OpData::Zext { value }
            | OpData::Uitofp { value } => {
                let operand_lattice = self.get_lattice(&value);
                if matches!(operand_lattice, Lattice::Constant(_)) {
                    self.lattices[op_id.get_op_id()] =
                        Self::cast(operand_lattice, OpType::from(&op_data));
                } else {
                    self.lattices[op_id.get_op_id()] = operand_lattice;
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
                // TODO: We are not able to fold these instructions for now.
                self.lattices[op_id.get_op_id()] = Lattice::Bottom;

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

            OpData::Br {
                cond,
                then_bb,
                else_bb,
            } => {
                let cond_lattice = self.get_lattice(&cond);
                match cond_lattice {
                    Lattice::Constant(c) => {
                        if let Operand::Bool(b) = c {
                            if b {
                                self.edge_list.push((bb_id.clone(), then_bb.clone()));
                            } else {
                                self.edge_list.push((bb_id.clone(), else_bb.clone()));
                            }
                        } else {
                            panic!("SCCP: condition of br must be a boolean constant: {:?}", c);
                        }
                    }
                    // Top requires conservative assumption, and Bottom requires no assumption. So we need to push both branches to the edge list.
                    Lattice::Bottom | Lattice::Top => {
                        self.edge_list.push((bb_id.clone(), then_bb.clone()));
                        self.edge_list.push((bb_id.clone(), else_bb.clone()));
                    }
                }
                // Push the terminator to the worklist for later rewriting.
                if !self.in_br_ops.contains(op_id.get_op_id()) {
                    self.in_br_ops.insert(op_id.get_op_id());
                    self.br_ops.push(op_id.clone());
                }
            }

            OpData::Phi { .. } => unreachable!("Phi nodes should be handled in visit_phi()"),

            // Jump is unconditional, and it's been processed outside of visit_expr().
            OpData::Jump { .. }
            | OpData::Ret { .. }
            // SCCP doesn't care about these ops.
            | OpData::Alloca(_)
            | OpData::GlobalAlloca(_)
            | OpData::Store { .. }
            | OpData::Declare { .. }
            | OpData::Move { .. } => {}
        }
    }

    fn visit_phi(&mut self, op_id: Operand, bb_id: Operand) {
        // push the phi first.
        if !self.in_phi_ops.contains(op_id.get_op_id()) {
            self.in_phi_ops.insert(op_id.get_op_id());
            self.phi_ops.push(op_id.clone());
        }
        let func = match self.current_function {
            Some(idx) => idx,
            None => panic!("SCCP visit_phi: current_function is None"), // should not happen
        };
        let op_data = self.program.funcs[func].dfg[op_id.clone()].data.clone();
        let old = self.lattices[op_id.get_op_id()].clone();

        if let OpData::Phi { incoming } = op_data {
            let lattice_list = incoming
                .iter()
                .filter_map(|incoming| {
                    if let PhiIncoming::Data {
                        value,
                        bb: Operand::BB(pred),
                    } = incoming
                    {
                        if self.executable.contains(&(*pred, bb_id.get_bb_id())) {
                            // DO NOT invoke get_xx_id() directly. We just ignore non-value operands, never panics.
                            if let Operand::Value(value_id) = value {
                                Some(self.lattices[*value_id].clone())
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
                .collect::<Vec<Lattice>>();
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
        } else {
            panic!("SCCP visit_phi: op is not a phi node");
        }
    }

    fn propagate(&mut self) {
        while !(self.edge_list.is_empty() && self.inst_list.is_empty()) {
            // Handle flow graph edge
            if let Some((from, to)) = self.edge_list.pop() {
                if self
                    .executable
                    .contains(&(from.get_bb_id(), to.get_bb_id()))
                {
                    continue;
                }
                self.executable.insert((from.get_bb_id(), to.get_bb_id()));

                // Visit the successor block. We need to check all phi nodes in the successor block and update their lattices.
                {
                    let mut ctx = context_or_err!(self, "SCCP: no context in propagate");
                    let phis = self
                        .builder
                        .get_all_ops_in_block(&mut ctx, to.clone(), OpType::Phi);
                    for phi in phis {
                        self.visit_phi(phi, to.clone());
                    }
                }

                // If to is visited for the first time, we need to visit all non-phi instructions in the block.
                if !self.visited.contains(to.get_bb_id()) {
                    self.visited.insert(to.get_bb_id());
                    let mut ctx = context_or_err!(self, "SCCP: no context in propagate");
                    let non_phis = self.builder.get_all_non_phi_in_block(&mut ctx, to.clone());
                    for non_phi in non_phis {
                        self.visit_expr(non_phi, to.clone());
                    }
                }

                // If to only has only one outgoing edge, push succ to edge_list.
                let cfg = &mut self.program.funcs[self.current_function.unwrap()].cfg;
                if cfg[to.get_bb_id()].succs.len() == 1 {
                    let succ = cfg[to.get_bb_id()].succs[0].clone();
                    self.edge_list.push((to.clone(), succ));
                }
            }

            // Handle instruction
            if let Some(op_id) = self.inst_list.pop() {
                // Critical: remove the inst first.
                self.in_inst_list.remove(op_id.get_op_id());

                let dfg = &mut self.program.funcs[self.current_function.unwrap()].dfg;
                let op_data = dfg[op_id.clone()].data.clone();
                if op_data.is(OpType::Phi) {
                    self.visit_phi(op_id.clone(), self.op_to_bb[op_id.get_op_id()].clone());
                } else {
                    // If any incoming edge is executable, we need to visit the instruction.
                    if self
                        .visited
                        .contains(self.op_to_bb[op_id.get_op_id()].get_bb_id())
                    {
                        self.visit_expr(op_id.clone(), self.op_to_bb[op_id.get_op_id()].clone());
                    }
                }
            }
        }
    }

    // Rewrite the program based on the results of propagation. And then return the existing phi nodes after rewriting.
    fn rewrite(&mut self) -> Vec<(Operand, Operand)> {
        // Slay the edge of dead block in phi operations.
        for phi_op in self.phi_ops.iter() {
            let dfg = &mut self.program.funcs[self.current_function.unwrap()].dfg;
            let op = dfg[phi_op.clone()].clone();
            if let OpData::Phi { incoming } = op.data {
                for incoming in incoming.iter() {
                    if let PhiIncoming::Data { bb, .. } = incoming {
                        if let Operand::BB(bb_id) = bb {
                            if !self.visited.contains(*bb_id) {
                                let mut ctx = context_or_err!(self, "SCCP: no context in rewrite");
                                self.builder.slay_phi_incoming(
                                    &mut ctx,
                                    phi_op.clone(),
                                    bb.clone(),
                                );
                            }
                        } else {
                            panic!("SCCP rewrite: phi incoming bb is not a BB operand");
                        }
                    }
                }
            } else {
                panic!("SCCP rewrite: op is not a phi node");
            }
        }

        // Replace br with jump if the condition is a constant.
        for br_op in self.br_ops.iter() {
            let dfg = &mut self.program.funcs[self.current_function.unwrap()].dfg;
            let op = dfg[br_op.clone()].clone();
            if let OpData::Br {
                cond,
                then_bb,
                else_bb,
            } = op.data
            {
                let cond_lattice = self.get_lattice(&cond);
                match cond_lattice {
                    Lattice::Constant(c) => {
                        if let Operand::Bool(b) = c {
                            let target_bb = if b { then_bb } else { else_bb };
                            let bb_id = self.op_to_bb[br_op.get_op_id()].clone();
                            let mut ctx = context_or_err!(self, "SCCP: no context in rewrite");
                            self.builder.replace_op(
                                &mut ctx,
                                br_op.clone(),
                                bb_id,
                                Op {
                                    typ: Type::Void,
                                    attrs: vec![],
                                    data: OpData::Jump { target_bb },
                                    users: vec![],
                                },
                            );
                        } else {
                            panic!("SCCP: condition of br must be a boolean constant");
                        }
                    }
                    _ => {/*do nothing*/}
                }
            } else {
                panic!("SCCP rewrite: op is not a br node");
            }
        }

        // Replace optimizable instructions with constants.
        let removed = self
            .lattices
            .iter()
            .enumerate()
            .filter_map(|(op_id, lattice)| {
                if let Lattice::Constant(c) = lattice {
                    let bb_id = self.op_to_bb[op_id].clone();
                    let op_id = Operand::Value(op_id);
                    let mut ctx = context_or_err!(self, "SCCP: no context in rewrite");
                    self.builder
                        .replace_all_uses(&mut ctx, op_id.clone(), c.clone());
                    Some((op_id.clone(), bb_id.clone()))
                } else {
                    None
                }
            })
            .collect::<Vec<(Operand, Operand)>>();

        // Remove the ops
        removed.into_iter().for_each(|(op_id, bb_id)| {
            let mut ctx = context_or_err!(self, "SCCP: no context in rewrite");
            self.builder.remove_op(&mut ctx, op_id, Some(bb_id));
        });

        // Phase 1: Isolate the dead blocks, disconnect the edges from live blocks to dead blocks.
        let dead_blocks = self.program.funcs[self.current_function.unwrap()]
            .cfg
            .collect()
            .into_iter()
            .filter(|bb_id| !self.visited.contains(*bb_id))
            .collect::<FxHashSet<usize>>();

        dead_blocks.iter().for_each(|bb_id| {
            let (last, terminator) = {
                let cfg = &mut self.program.funcs[self.current_function.unwrap()].cfg;
                let bb = &cfg[*bb_id];
                let last = match bb.cur.last() {
                    Some(last) => last.clone(),
                    None => return,
                };
                let data = {
                    let dfg = &mut self.program.funcs[self.current_function.unwrap()].dfg;
                    dfg[last.clone()].data.clone()
                };
                (last, data)
            };
            if matches!(terminator, OpData::Br { .. } | OpData::Jump { .. }) {
                // remove the op
                let mut ctx = context_or_err!(self, "SCCP: no context in rewrite");
                self.builder
                    .remove_op(&mut ctx, last.clone(), Some(Operand::BB(*bb_id)));
            }
        });

        // Phase 2: Check users in dead blocks.
        for bb_id in &dead_blocks {
            let cfg = &mut self.program.funcs[self.current_function.unwrap()].cfg;
            let cur = cfg[*bb_id].cur.clone();

            // Split users check and removal due to data dependency.
            for inst in cur.iter().rev() {
                let func_id = self.current_function.unwrap();
                let (funcs, globals) = (&mut self.program.funcs, &mut self.program.globals);
                let dfg = &mut funcs[func_id].dfg;

                // inst can be used by the instructions inside the block, but it cannot be used by instructions outside the block.
                let users = dfg[inst.get_op_id()].users.clone();
                for user in users {
                    let user_bb = self.op_to_bb[user.get_op_id()].clone();
                    // The user can be in the same block, or in another dead block. But it cannot be in a live block.
                    if dead_blocks.contains(&user_bb.get_bb_id()) {
                        // continue. users will be removed later.
                        continue;
                    }
                    panic!(
                        "Builder remove_block: instruction {:#?} has user {:#?} outside the block",
                        dfg[inst.get_op_id()],
                        dfg[user.get_op_id()]
                    );
                }

                // Check whether the instruction uses a value outside dead block. If so, remove the use first.
                let data = dfg[inst.clone()].data.clone();
                let op = inst.clone();
                let is_live_value = |operand: &Operand| match operand {
                    Operand::Value(id) => {
                        let bb = self.op_to_bb[*id].get_bb_id();
                        !dead_blocks.contains(&bb)
                    }
                    _ => false,
                };

                match data {
                    OpData::Load { addr } => {
                        if matches!(addr, Operand::Global(_)) {
                            globals.remove_use(addr, op);
                        } else if is_live_value(&addr) {
                            dfg.remove_use(addr, op);
                        }
                    }
                    OpData::Store { addr, value } => {
                        if matches!(addr, Operand::Global(_)) {
                            globals.remove_use(addr, op.clone());
                        } else if is_live_value(&addr) {
                            dfg.remove_use(addr, op.clone());
                        }
                        if is_live_value(&value) {
                            dfg.remove_use(value, op);
                        }
                    }
                    OpData::Br { cond, .. } => {
                        if is_live_value(&cond) {
                            dfg.remove_use(cond, op);
                        }
                    }
                    OpData::Call { args, .. } => {
                        for arg in args {
                            if is_live_value(&arg) {
                                dfg.remove_use(arg, op.clone());
                            }
                        }
                    }
                    OpData::Ret { value } => {
                        if let Some(val) = value {
                            if is_live_value(&val) {
                                dfg.remove_use(val, op);
                            }
                        }
                    }
                    OpData::Phi { incoming } => {
                        for phi_incoming in incoming {
                            if let PhiIncoming::Data { value, .. } = phi_incoming {
                                if is_live_value(&value) {
                                    dfg.remove_use(value, op.clone());
                                }
                            }
                        }
                    }

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
                        if is_live_value(&lhs) {
                            dfg.remove_use(lhs, op.clone());
                        }
                        if is_live_value(&rhs) {
                            dfg.remove_use(rhs, op);
                        }
                    }

                    OpData::Sitofp { value }
                    | OpData::Fptosi { value }
                    | OpData::Uitofp { value }
                    | OpData::Zext { value } => {
                        if is_live_value(&value) {
                            dfg.remove_use(value, op);
                        }
                    }

                    OpData::GEP { base, indices } => {
                        if matches!(base, Operand::Global(_)) {
                            globals.remove_use(base, op.clone());
                        } else if is_live_value(&base) {
                            dfg.remove_use(base, op.clone());
                        }
                        for index in indices {
                            if is_live_value(&index) {
                                dfg.remove_use(index, op.clone());
                            }
                        }
                    }

                    OpData::Move { value, .. } => {
                        if is_live_value(&value) {
                            dfg.remove_use(value, op);
                        }
                    }

                    OpData::GlobalAlloca(_)
                    | OpData::Alloca(_)
                    | OpData::Jump { .. }
                    | OpData::Declare { .. } => {}
                }
            }
        }

        // Phase 3: Remove the instructions in dead blocks directly by dfg.
        for bb_id in &dead_blocks {
            let cfg = &mut self.program.funcs[self.current_function.unwrap()].cfg;
            let cur = cfg[*bb_id].cur.clone();
            let dfg = &mut self.program.funcs[self.current_function.unwrap()].dfg;
            for inst in cur.iter().rev() {
                // Remove the uses
                dfg.remove(inst.get_op_id());
            }
        }

        // Phase 4: Remove the blocks directly by cfg.
        for bb_id in dead_blocks {
            // remove the block from cfg
            let cfg = &mut self.program.funcs[self.current_function.unwrap()].cfg;
            cfg.remove(bb_id);
            crate::debug::info!("SCCP: removed dead block {}", bb_id);
        }

        // Collect the surviving phi nodes after rewriting.
        self.phi_ops
            .iter()
            .filter_map(|phi_op| {
                let dfg = &mut self.program.funcs[self.current_function.unwrap()].dfg;
                // Bypass the Index operator
                if let Some(ArenaItem::Data(data)) = dfg.storage.get(phi_op.get_op_id()) {
                    if data.data.is(OpType::Phi) {
                        Some((phi_op.clone(), self.op_to_bb[phi_op.get_op_id()].clone()))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect::<Vec<(Operand, Operand)>>()
    }

    pub fn run(&mut self) {
        let mut phi_ops: Vec<Vec<(Operand, Operand)>> =
            vec![vec![]; self.program.funcs.storage.len()];
        for func_id in self.program.funcs.collect_internal() {
            self.init(func_id);
            self.propagate();
            phi_ops[func_id] = self.rewrite();
        }

        // Remove trivial phi.
        info!("SCCP: removing trivial phi nodes...");
        RemoveTrivialPhi::new(self.program, phi_ops).run();
        info!("SCCP: done");
    }
}

impl Pass<()> for SCCP<'_> {
    fn run(&mut self) {
        self.run()
    }
}

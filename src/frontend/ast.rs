/**
 * Definition of AST nodes and related types.
 */
use crate::base::Type;
use crate::utils::arena::*;

use strum_macros::EnumDiscriminants;

pub type AST = IndexedArena<Node>;
pub type NodeId = usize;

#[derive(Debug, EnumDiscriminants, Clone)]
#[strum_discriminants(name(NodeType))]
#[strum_discriminants(derive(Hash, Ord, PartialOrd))]
pub enum Node {
    FnDecl {
        name: String,
        params: Vec<(String, Type)>,
        typ: Type,
        body: NodeId,
    },

    Break,
    Continue,

    Return(Option<NodeId>),

    Block {
        statements: Vec<NodeId>,
    },

    Assign {
        lhs: NodeId,
        rhs: NodeId,
    },

    If {
        condition: NodeId,
        then_block: NodeId,
        else_block: Option<NodeId>,
    },

    While {
        condition: NodeId,
        body: NodeId,
    },

    BinaryOp {
        typ: Type,
        lhs: NodeId,
        op: Op,
        rhs: NodeId,
    },

    UnaryOp {
        typ: Type,
        op: Op,
        operand: NodeId,
    },

    Call {
        typ: Type,
        func_name: String,
        args: Vec<NodeId>,
    },

    // Var
    VarDecl {
        name: String,
        typ: Type,
        is_global: bool,
        mutable: bool,
        init_value: Option<NodeId>,
    },

    VarAccess {
        name: String,
        typ: Type,
    },

    // Array
    ConstArray {
        name: String,
        typ: Type,
        // None: zeroinitializer
        init_values: Option<Vec<NodeId>>,
    },

    VarArray {
        name: String,
        is_global: bool,
        typ: Type,
        // None: If is_global then zeroinitializer, else uninitialized
        init_values: Option<Vec<NodeId>>,
    },

    ArrayAccess {
        name: String,
        indices: Vec<NodeId>,
        typ: Type,
    },

    Empty,

    Literal(Literal),

    // Raw struct passed through parsing phase
    // Processed declaration aggregation
    DeclAggr {
        decls: Vec<NodeId>,
    },

    // Original declaration aggregation
    RawDecl {
        typ: Type,
        mutable: bool,
        raw_decls: Vec<RawDef>,
    },

    // Original signle declaration
    RawDef {
        ident: String,
        const_exps: Vec<NodeId>,
        init_val: Option<NodeId>,
    },

    // Original array initialization values
    ArrayInitVal {
        init_vals: Vec<NodeId>,
    },
}

#[derive(Debug, Clone)]
pub struct RawDef {
    pub ident: String,
    pub const_exps: Vec<NodeId>,
    pub init_val: Option<NodeId>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Literal {
    Int(i32),
    Float(f32),
    String(String),
}

impl Literal {
    pub fn get_int(&self) -> i32 {
        if let Literal::Int(val) = self {
            *val
        } else {
            panic!("Literal is not Int");
        }
    }
    pub fn get_float(&self) -> f32 {
        if let Literal::Float(val) = self {
            *val
        } else {
            panic!("Literal is not Float");
        }
    }
    pub fn is_zero(&self) -> bool {
        match self {
            Literal::Int(val) => *val == 0,
            Literal::Float(val) => *val == 0.0,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Op {
    // unary
    Plus,
    Minus,
    Not,
    // special op which only occurs in type casting
    Cast(Type, Type),

    // binary
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    Ne,
    And,
    Or,
}

impl Op {
    // Check if the operation only returns int type
    pub fn only_ret_int(&self) -> bool {
        matches!(
            self,
            Op::And | Op::Or | Op::Lt | Op::Gt | Op::Le | Op::Ge | Op::Eq | Op::Ne
        )
    }
}

impl Default for Node {
    fn default() -> Self {
        Node::Empty
    }
}

impl Node {
    pub fn is(&self, typ: NodeType) -> bool {
        matches!(NodeType::from(self), typ)
    }
}

impl AST {
    pub fn get_node_type(&self, idx: usize) -> NodeType {
        if idx >= self.storage.len() {
            panic!("AST get_type: index {} out of bounds", idx);
        }
        match &self.storage[idx] {
            ArenaItem::Data(node) => NodeType::from(node),
            _ => panic!("AST get_type: index {} is not a valid node", idx),
        }
    }
}

impl Arena<Node> for AST {
    fn remove(&mut self, idx: usize) -> Node {
        if idx >= self.storage.len() {
            panic!("Index {} out of bounds", idx);
        } else {
            match std::mem::replace(&mut self.storage[idx], ArenaItem::None) {
                ArenaItem::Data(node) => node,
                _ => panic!("Index {} is not a valid node", idx),
            }
        }
    }

    fn gc(&mut self) -> Vec<ArenaItem<Node>> {
        let new_arena: Vec<ArenaItem<Node>> = vec![];
        let old_arena = std::mem::replace(&mut self.storage, new_arena);

        let old_arena = old_arena
            .into_iter()
            .map(|mut item| {
                if matches!(item, ArenaItem::Data(_)) {
                    let new_idx = self.storage.len();
                    let data = item.replace(new_idx);
                    self.storage.push(data);
                    ArenaItem::NewIndex(new_idx)
                } else {
                    ArenaItem::None
                }
            })
            .collect::<Vec<ArenaItem<Node>>>();

        let remap_idx = |idx: &mut NodeId| {
            *idx = match old_arena.get(*idx).unwrap() {
                ArenaItem::NewIndex(new_idx) => *new_idx,
                _ => panic!("AST gc: node index not found"),
            };
        };

        if let Some(entry) = self.entry.as_mut() {
            remap_idx(entry);
        }

        for idx in self.map.values_mut() {
            remap_idx(idx);
        }

        for item in self.storage.iter_mut() {
            if let ArenaItem::Data(node) = item {
                match node {
                    Node::FnDecl { body, .. } => {
                        remap_idx(body);
                    }
                    Node::Return(ret) => {
                        if let Some(ret) = ret {
                            remap_idx(ret);
                        }
                    }
                    Node::Block { statements } => {
                        for stmt in statements.iter_mut() {
                            remap_idx(stmt);
                        }
                    }
                    Node::Assign { lhs, rhs, .. } => {
                        remap_idx(lhs);
                        remap_idx(rhs);
                    }
                    Node::If {
                        condition,
                        then_block,
                        else_block,
                    } => {
                        remap_idx(condition);
                        remap_idx(then_block);
                        if let Some(else_block) = else_block {
                            remap_idx(else_block);
                        }
                    }
                    Node::While {
                        condition, body, ..
                    } => {
                        remap_idx(condition);
                        remap_idx(body);
                    }
                    Node::BinaryOp { lhs, rhs, .. } => {
                        remap_idx(lhs);
                        remap_idx(rhs);
                    }
                    Node::UnaryOp { operand, .. } => {
                        remap_idx(operand);
                    }
                    Node::Call { args, .. } => {
                        for arg in args.iter_mut() {
                            remap_idx(arg);
                        }
                    }
                    Node::VarDecl { init_value, .. } => {
                        if let Some(init_value) = init_value {
                            remap_idx(init_value);
                        }
                    }
                    Node::ConstArray { init_values, .. } | Node::VarArray { init_values, .. } => {
                        if let Some(init_values) = init_values {
                            for init_value in init_values.iter_mut() {
                                remap_idx(init_value);
                            }
                        }
                    }
                    Node::ArrayAccess { indices, .. } => {
                        for index in indices.iter_mut() {
                            remap_idx(index);
                        }
                    }
                    Node::DeclAggr { decls } => {
                        for decl in decls.iter_mut() {
                            remap_idx(decl);
                        }
                    }
                    Node::RawDecl { raw_decls, .. } => {
                        for raw_decl in raw_decls.iter_mut() {
                            for const_exp in raw_decl.const_exps.iter_mut() {
                                remap_idx(const_exp);
                            }
                            if let Some(init_val) = &mut raw_decl.init_val {
                                remap_idx(init_val);
                            }
                        }
                    }
                    Node::RawDef {
                        const_exps,
                        init_val,
                        ..
                    } => {
                        for const_exp in const_exps.iter_mut() {
                            remap_idx(const_exp);
                        }
                        if let Some(init_val) = init_val {
                            remap_idx(init_val);
                        }
                    }
                    Node::ArrayInitVal { init_vals } => {
                        for init_val in init_vals.iter_mut() {
                            remap_idx(init_val);
                        }
                    }
                    Node::Break
                    | Node::Continue
                    | Node::VarAccess { .. }
                    | Node::Empty
                    | Node::Literal(_) => {}
                }
            }
        }

        old_arena
    }
}

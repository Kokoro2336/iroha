use crate::debug::graph::{
    self, attr, id, Attribute, Edge, EdgeTy, GraphNode, Id, NodeId as GraphNodeId, Stmt, Vertex,
};
use crate::frontend::ast::{Literal, Node, Op, AST};

fn node_name(node_id: usize) -> String {
    format!("\"n{}\"", node_id)
}

fn node_label(node: &Node) -> String {
    match node {
        Node::FnDecl {
            name, params, typ, ..
        } => format!(
            "FnDecl: {}() | Params: [{}] | Type: {}",
            name,
            params
                .iter()
                .map(|(n, t)| format!("{} {}", t, n))
                .collect::<Vec<_>>()
                .join("; "),
            typ
        ),
        Node::Break => "Break".to_string(),
        Node::Continue => "Continue".to_string(),
        Node::Return(_) => "Return".to_string(),
        Node::Block { .. } => "Block".to_string(),
        Node::Assign { .. } => "Assign".to_string(),
        Node::If { .. } => "If".to_string(),
        Node::While { .. } => "While".to_string(),
        Node::BinaryOp { op, typ, .. } => format!("BinaryOp: {:?} | {}", op, typ),
        Node::UnaryOp { op, typ, .. } => format!("UnaryOp: {:?} | {}", op, typ),
        Node::Call { func_name, typ, .. } => format!("Call: {}() | {}", func_name, typ),
        Node::VarDecl {
            name,
            typ,
            mutable,
            is_global,
            ..
        } => format!(
            "VarDecl: {} | {} | mutable: {} | global: {}",
            name, typ, mutable, is_global
        ),
        Node::VarAccess { name, typ } => format!("VarAccess: {} | {}", name, typ),
        Node::ConstArray {
            name,
            typ,
            init_values,
        } => {
            if init_values.is_some() {
                format!("ConstArray: {} | {}", name, typ)
            } else {
                format!("ConstArray: {} | {} | zeroinitializer", name, typ)
            }
        }
        Node::VarArray {
            name,
            typ,
            is_global,
            init_values,
        } => {
            if init_values.is_some() {
                format!("VarArray: {} | {} | global: {}", name, typ, is_global)
            } else {
                format!(
                    "VarArray: {} | {} | global: {} | zeroinitializer",
                    name, typ, is_global
                )
            }
        }
        Node::ArrayAccess { name, typ, .. } => format!("ArrayAccess: {} | {}", name, typ),
        Node::Empty => "Empty".to_string(),
        Node::Literal(Literal::Int(v)) => format!("Literal: Int({})", v),
        Node::Literal(Literal::Float(v)) => format!("Literal: Float({})", v),
        Node::Literal(Literal::String(v)) => format!("Literal: String({})", v),
        Node::DeclAggr { .. } => "DeclAggr".to_string(),
        Node::RawDecl { typ, mutable, .. } => format!("RawDecl: {} | mutable: {}", typ, mutable),
        Node::RawDef {
            ident,
            const_exps,
            init_val,
        } => format!(
            "RawDef: {} | dims: {} | has_init: {}",
            ident,
            const_exps.len(),
            init_val.is_some()
        ),
        Node::ArrayInitVal { init_vals } => format!("ArrayInitVal: {} vals", init_vals.len()),
    }
}

fn node_shape(node: &Node) -> &'static str {
    match node {
        Node::If { .. } | Node::While { .. } => "diamond",
        Node::Break | Node::Continue => "diamond",
        Node::VarAccess { .. } | Node::ArrayAccess { .. } => "ellipse",
        Node::Literal(_) | Node::Return(_) => "oval",
        _ => "box",
    }
}

fn children(node: &Node) -> Vec<usize> {
    match node {
        Node::FnDecl { body, .. } => vec![*body],
        Node::Return(expr) => expr.iter().copied().collect(),
        Node::Block { statements } => statements.clone(),
        Node::Assign { lhs, rhs } => vec![*lhs, *rhs],
        Node::If {
            condition,
            then_block,
            else_block,
        } => {
            let mut out = vec![*condition, *then_block];
            if let Some(else_id) = else_block {
                out.push(*else_id);
            }
            out
        }
        Node::While { condition, body } => vec![*condition, *body],
        Node::BinaryOp { lhs, rhs, op, .. } => {
            if matches!(op, Op::And | Op::Or) {
                vec![*lhs, *rhs]
            } else {
                vec![*lhs, *rhs]
            }
        }
        Node::UnaryOp { operand, .. } => vec![*operand],
        Node::Call { args, .. } => args.clone(),
        Node::VarDecl { init_value, .. } => init_value.iter().copied().collect(),
        Node::ConstArray { init_values, .. } | Node::VarArray { init_values, .. } => {
            init_values.clone().unwrap_or_default()
        }
        Node::ArrayAccess { indices, .. } => indices.clone(),
        Node::DeclAggr { decls } => decls.clone(),
        Node::RawDef {
            const_exps,
            init_val,
            ..
        } => {
            let mut out = const_exps.clone();
            if let Some(init_id) = init_val {
                out.push(*init_id);
            }
            out
        }
        Node::ArrayInitVal { init_vals } => init_vals.clone(),
        _ => vec![],
    }
}

impl GraphNode for AST {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        fn dfs(
            ast: &AST,
            node_id: usize,
            stmts: &mut Vec<Stmt>,
            visited: &mut std::collections::HashSet<usize>,
        ) {
            if !visited.insert(node_id) {
                return;
            }

            let node = &ast[node_id];
            let from = node_name(node_id);

            stmts.push(Stmt::Node(graph::Node::new(
                graph::NodeId(Id::Plain(from.clone()), None),
                vec![
                    attr!("label", { format!("\"{}\"", node_label(node)) }),
                    attr!("shape", { node_shape(node) }),
                ],
            )));

            for child in children(node) {
                if child >= ast.storage.len() {
                    continue;
                }
                let to = node_name(child);
                stmts.push(Stmt::Edge(Edge {
                    ty: EdgeTy::Pair(
                        Vertex::N(GraphNodeId(Id::Plain(from.clone()), None)),
                        Vertex::N(GraphNodeId(Id::Plain(to.clone()), None)),
                    ),
                    attributes: vec![],
                }));
                dfs(ast, child, stmts, visited);
            }
        }

        if let Some(entry) = self.entry {
            dfs(self, entry, stmts, visited);
        }
    }
}

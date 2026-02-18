use crate::base::Type;
use crate::debug::graph::{
    self, attr, id, Attribute, Edge, EdgeTy, GraphNode, Id, NodeId, Stmt, Vertex,
};
use crate::frontend::ast::*;

/* GraphNode implementations for AST nodes */
impl GraphNode for FnDecl {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", {
                    format!(
                        "\"FnDecl: {}() | Params: [{}] | Return Type: {:?}\"",
                        self.name,
                        self.params
                            .iter()
                            .map(|x| format!("{} {}", x.1, x.0))
                            .collect::<Vec<String>>()
                            .join("; "),
                        match self.typ {
                            Type::Function {
                                ref return_type, ..
                            } => return_type.as_ref(),
                            _ => &Type::Void,
                        }
                    )
                }),
                attr!("shape", "box"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);

        let to = (&*self.body as *const dyn Node) as *const () as usize;
        if visited.contains(&to) {
            return;
        }

        stmts.push(Stmt::Edge(Edge {
            ty: EdgeTy::Pair(
                Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to)), None)),
            ),
            attributes: vec![],
        }));

        self.body.visit(stmts, visited);
    }
}

impl GraphNode for Break {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", "\"Break\""), attr!("shape", "diamond")],
        )));
        // Add to visited
        visited.insert(ptr);
    }
}

impl GraphNode for Continue {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", "\"Continue\""), attr!("shape", "diamond")],
        )));
        // Add to visited
        visited.insert(ptr);
    }
}

impl GraphNode for Return {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", "\"Return\""), attr!("shape", "oval")],
        )));
        // Add to visited
        visited.insert(ptr);

        if let Some(val) = &self.0 {
            let to = (&**val as *const dyn Node) as *const () as usize;
            if visited.contains(&to) {
                return;
            }

            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to)), None)),
                ),
                attributes: vec![],
            }));

            val.visit(stmts, visited);
        }
    }
}

impl GraphNode for Block {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", "\"Block\""), attr!("shape", "box")],
        )));
        // Add to visited
        visited.insert(ptr);

        for stmt in &self.statements {
            let to = (&**stmt as *const dyn Node) as *const () as usize;
            if visited.contains(&to) {
                continue;
            }

            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to)), None)),
                ),
                attributes: vec![],
            }));

            stmt.visit(stmts, visited);
        }
    }
}

impl GraphNode for Assign {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", "\"Assign\""), attr!("shape", "box")],
        )));
        // Add to visited
        visited.insert(ptr);

        let to_lhs = (&*self.lhs as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_lhs) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_lhs)), None)),
                ),
                attributes: vec![],
            }));

            self.lhs.visit(stmts, visited);
        }

        let to_rhs = (&*self.rhs as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_rhs) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_rhs)), None)),
                ),
                attributes: vec![],
            }));

            self.rhs.visit(stmts, visited);
        }
    }
}

impl GraphNode for If {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", "\"If\""), attr!("shape", "diamond")],
        )));
        // Add to visited
        visited.insert(ptr);

        let to_cond = (&*self.condition as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_cond) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_cond)), None)),
                ),
                attributes: vec![],
            }));
            self.condition.visit(stmts, visited);
        }

        let to_then = (&*self.then_block as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_then) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_then)), None)),
                ),
                attributes: vec![],
            }));
            self.then_block.visit(stmts, visited);
        }

        if let Some(else_block) = &self.else_block {
            let to_else = (&**else_block as *const dyn Node) as *const () as usize;
            if !visited.contains(&to_else) {
                stmts.push(Stmt::Edge(Edge {
                    ty: EdgeTy::Pair(
                        Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                        Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_else)), None)),
                    ),
                    attributes: vec![],
                }));
                else_block.visit(stmts, visited);
            }
        }
    }
}

impl GraphNode for While {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", "\"While\""), attr!("shape", "diamond")],
        )));
        // Add to visited
        visited.insert(ptr);

        let to_cond = (&*self.condition as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_cond) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_cond)), None)),
                ),
                attributes: vec![],
            }));
            self.condition.visit(stmts, visited);
        }

        let to_body = (&*self.body as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_body) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_body)), None)),
                ),
                attributes: vec![],
            }));
            self.body.visit(stmts, visited);
        }
    }
}

impl GraphNode for BinaryOp {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", { format!("\"BinaryOp: {:?}\"", self.op) }),
                attr!("shape", "box"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);

        let to_lhs = (&*self.lhs as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_lhs) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_lhs)), None)),
                ),
                attributes: vec![],
            }));
            self.lhs.visit(stmts, visited);
        }

        let to_rhs = (&*self.rhs as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_rhs) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_rhs)), None)),
                ),
                attributes: vec![],
            }));
            self.rhs.visit(stmts, visited);
        }
    }
}

impl GraphNode for UnaryOp {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", { format!("\"UnaryOp: {:?}\"", self.op) }),
                attr!("shape", "box"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);

        let to_operand = (&*self.operand as *const dyn Node) as *const () as usize;
        if !visited.contains(&to_operand) {
            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_operand)), None)),
                ),
                attributes: vec![],
            }));
            self.operand.visit(stmts, visited);
        }
    }
}

impl GraphNode for Call {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", { format!("\"Call: {}()\"", self.func_name) }),
                attr!("shape", "box"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);

        for arg in &self.args {
            let to_arg = (&**arg as *const dyn Node) as *const () as usize;
            if visited.contains(&to_arg) {
                continue;
            }

            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_arg)), None)),
                ),
                attributes: vec![],
            }));

            arg.visit(stmts, visited);
        }
    }
}

impl GraphNode for VarDecl {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", {
                    format!(
                        "\"VarDecl: {} | Type: {} | Mutable: {}\"",
                        self.name, self.typ, self.mutable
                    )
                }),
                attr!("shape", "box"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);

        if let Some(init_value) = &self.init_value {
            let to_init = (&**init_value as *const dyn Node) as *const () as usize;
            if !visited.contains(&to_init) {
                stmts.push(Stmt::Edge(Edge {
                    ty: EdgeTy::Pair(
                        Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                        Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_init)), None)),
                    ),
                    attributes: vec![],
                }));
                init_value.visit(stmts, visited);
            }
        }
    }
}

impl GraphNode for VarAccess {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", {
                    format!("\"VarAccess: {} | Type: {}\"", self.name, self.typ)
                }),
                attr!("shape", "ellipse"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);
    }
}

impl GraphNode for ConstArray {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", {
                    if self.init_values.is_some() {
                        format!("\"ConstArray: {} | Type: {}\"", self.name, self.typ)
                    } else {
                        format!(
                            "\"ConstArray: {} | Type: {} | zeroinitializer\"",
                            self.name, self.typ
                        )
                    }
                }),
                attr!("shape", "box"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);

        if let Some(init_values) = &self.init_values {
            for init_value in init_values {
                let to_init = (&**init_value as *const dyn Node) as *const () as usize;
                if visited.contains(&to_init) {
                    continue;
                }

                stmts.push(Stmt::Edge(Edge {
                    ty: EdgeTy::Pair(
                        Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                        Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_init)), None)),
                    ),
                    attributes: vec![],
                }));

                init_value.visit(stmts, visited);
            }
        }
    }
}

impl GraphNode for VarArray {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", {
                    if self.init_values.is_some() {
                        format!(
                            "\"VarArray: {} | Type: {} | is_global: {}\"",
                            self.name, self.typ, self.is_global
                        )
                    } else {
                        format!(
                            "\"VarArray: {} | Type: {} | is_global: {} | zeroinitializer\"",
                            self.name, self.typ, self.is_global
                        )
                    }
                }),
                attr!("shape", "box"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);

        if let Some(init_values) = &self.init_values {
            for init_value in init_values {
                let to_init = (&**init_value as *const dyn Node) as *const () as usize;
                if visited.contains(&to_init) {
                    continue;
                }

                stmts.push(Stmt::Edge(Edge {
                    ty: EdgeTy::Pair(
                        Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                        Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_init)), None)),
                    ),
                    attributes: vec![],
                }));

                init_value.visit(stmts, visited);
            }
        }
    }
}

impl GraphNode for ArrayAccess {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![
                attr!("label", {
                    format!("\"ArrayAccess: {} | Type: {}\"", self.name, self.typ)
                }),
                attr!("shape", "ellipse"),
            ],
        )));
        // Add to visited
        visited.insert(ptr);

        for index in &self.indices {
            let to_index = (&**index as *const dyn Node) as *const () as usize;
            if visited.contains(&to_index) {
                continue;
            }

            stmts.push(Stmt::Edge(Edge {
                ty: EdgeTy::Pair(
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", ptr)), None)),
                    Vertex::N(NodeId(Id::Plain(format!("\"{}\"", to_index)), None)),
                ),
                attributes: vec![],
            }));

            index.visit(stmts, visited);
        }
    }
}

impl GraphNode for Empty {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", "\"Empty\""), attr!("shape", "box")],
        )));
        // Add to visited
        visited.insert(ptr);
    }
}

impl GraphNode for Literal {
    fn visit(&self, stmts: &mut Vec<Stmt>, visited: &mut std::collections::HashSet<usize>) {
        let ptr = self as *const _ as usize;
        if visited.contains(&ptr) {
            return;
        }

        let label = match self {
            Literal::Int(val) => format!("\"Literal: Int({})\"", val),
            Literal::Float(val) => format!("\"Literal: Float({})\"", val),
            Literal::String(val) => format!("\"Literal: String({})\"", val),
        };

        stmts.push(Stmt::Node(graph::Node::new(
            graph::NodeId(Id::Plain(format!("\"{}\"", ptr)), None),
            vec![attr!("label", label), attr!("shape", "oval")],
        )));
        // Add to visited
        visited.insert(ptr);
    }
}

macro_rules! impl_graph_node_for_raw_node {
    ($($t:ty),*) => {
        $(
            impl GraphNode for $t {
                fn visit(
                    &self,
                    _stmts: &mut Vec<Stmt>,
                    _visited: &mut std::collections::HashSet<usize>,
                ) {
                    panic!(concat!(stringify!($t), " should not be visited in graph dump"));
                }
            }
        )*
    };
}

impl_graph_node_for_raw_node!(DeclAggr, RawDecl, RawDef, ArrayInitVal);

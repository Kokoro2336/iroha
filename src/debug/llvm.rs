/**
 * Dump customized IR into LLVM format for debugging.
 */
use crate::base::ir::*;
use crate::base::Pass;
use crate::base::Type;
use crate::frontend::ast;
use crate::utils::arena::{ArenaItem, IndexedArena};
use std::fmt::Write;

pub trait DumpLLVM {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error>;
}

pub struct DumpContext<'a> {
    pub program: &'a Program,
    pub function: Option<&'a Function>,
}

fn op_name_attr(op: &Op) -> Option<&str> {
    op.attrs.iter().find_map(|attr| match attr {
        Attr::Name(name) => Some(name.as_str()),
        _ => None,
    })
}

fn value_operand_name(id: usize, ctx: &DumpContext) -> String {
    if let Some(func) = ctx.function {
        let op = &func.dfg[id];
        if let Some(name) = op_name_attr(op) {
            return format!("%{}", name);
        }
    }
    format!("%{}", id)
}

fn global_operand_name(id: usize, ctx: &DumpContext) -> String {
    let op = &ctx.program.globals[id];
    if let Some(name) = op_name_attr(op) {
        return format!("@{}", name);
    }
    format!("@{}", id)
}

fn operand_type(operand: &Operand, ctx: &DumpContext, default: Type) -> Type {
    match operand {
        Operand::Value(id) => {
            if let Some(f) = ctx.function {
                f.dfg[*id].typ.clone()
            } else {
                default
            }
        }
        Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
        Operand::Int(_) => Type::Int,
        Operand::Float(_) => Type::Float,
        Operand::Bool(_) => Type::Bool,
        Operand::Param { typ, .. } => typ.clone(),
        _ => default,
    }
}

impl DumpLLVM for Type {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        match self {
            Type::Int => write!(s, "i32")?,
            Type::Float => write!(s, "float")?,
            Type::Bool => write!(s, "i1")?,
            Type::Void => write!(s, "void")?,
            Type::Pointer { base } => write!(s, "{}*", base.dump_to_llvm(ctx)?)?,
            Type::Array { dims, base } => {
                let mut current = base.dump_to_llvm(ctx)?;
                for dim in dims.iter().rev() {
                    current = format!("[{} x {}]", dim, current);
                }
                write!(s, "{}", current)?;
            }
            Type::Char => write!(s, "i8")?,
            _ => todo!("dump type {:?}", self),
        }
        Ok(s)
    }
}

impl DumpLLVM for Operand {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        match self {
            Operand::Value(id) => write!(s, "{}", value_operand_name(*id, ctx))?,
            Operand::Global(id) => write!(s, "{}", global_operand_name(*id, ctx))?,
            Operand::Int(val) => write!(s, "{}", val)?,
            Operand::Float(val) => write!(s, "{}", val)?,
            Operand::Bool(val) => write!(s, "{}", val)?,
            Operand::BB(id) => write!(s, "%bb_{}", id)?,
            Operand::Param { idx, .. } => write!(s, "%arg{}", idx)?,
            Operand::Func(id) => write!(s, "@{}", ctx.program.funcs[*id].name)?,
            Operand::Reg(reg) => write!(s, "{:?}", reg)?,
            Operand::Undefined => write!(s, "undef")?,
        }
        Ok(s)
    }
}

impl DumpLLVM for Op {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        match &self.data {
            OpData::GEP { base, indices } => {
                let ptr_ty = match base {
                    Operand::Value(id) => {
                        let mut t = Type::Pointer {
                            base: Box::new(Type::Int),
                        };
                        if let Some(f) = ctx.function {
                            t = f.dfg[*id].typ.clone();
                        }
                        t
                    }
                    Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                    _ => Type::Pointer {
                        base: Box::new(Type::Int),
                    },
                };

                let gep_base_ty = match &ptr_ty {
                    Type::Pointer { base } => base.as_ref().clone(),
                    _ => ptr_ty.clone(),
                };

                write!(
                    s,
                    "getelementptr inbounds {}, {} {}",
                    gep_base_ty.dump_to_llvm(ctx)?,
                    ptr_ty.dump_to_llvm(ctx)?,
                    base.dump_to_llvm(ctx)?
                )?;

                for index in indices {
                    write!(s, ", i32 {}", index.dump_to_llvm(ctx)?)?;
                }
            }
            OpData::Ret { value } => {
                if let Some(val) = value {
                    let typ = match val {
                        Operand::Value(id) => {
                            let mut t = Type::Int;
                            if let Some(f) = ctx.function {
                                t = f.dfg[*id].typ.clone();
                            }
                            t
                        }
                        Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                        Operand::Int(_) => Type::Int,
                        Operand::Float(_) => Type::Float,
                        _ => Type::Int,
                    };
                    write!(
                        s,
                        "ret {} {}",
                        typ.dump_to_llvm(ctx)?,
                        val.dump_to_llvm(ctx)?
                    )?;
                } else {
                    write!(s, "ret void")?;
                }
            }
            OpData::Alloca(typ) => {
                write!(
                    s,
                    "alloca {}, align {}",
                    typ.dump_to_llvm(ctx)?,
                    typ.size_in_bytes()
                )?;
            }
            OpData::GlobalAlloca(_) => {
                let attrs: String = self
                    .attrs
                    .iter()
                    .map(|attr| format!("{}", attr))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(
                    s,
                    "global_alloca {} with attrs: {}",
                    self.typ.dump_to_llvm(ctx)?,
                    attrs
                )?;
            }
            OpData::Declare { name, typ } => {
                if let Type::Function {
                    return_type,
                    param_types,
                } = typ
                {
                    write!(s, "declare {} @{}(", return_type.dump_to_llvm(ctx)?, name)?;
                    for (i, param_ty) in param_types.iter().enumerate() {
                        write!(s, "{}", param_ty.dump_to_llvm(ctx)?)?;
                        if i < param_types.len() - 1 {
                            write!(s, ", ")?;
                        }
                    }
                    write!(s, ")")?;
                } else {
                    return Err(std::fmt::Error);
                }
            }
            OpData::Load { addr } => {
                let ptr_ty = match addr {
                    Operand::Value(id) => {
                        let mut t = Type::Pointer {
                            base: Box::new(Type::Int),
                        };
                        if let Some(f) = ctx.function {
                            t = f.dfg[*id].typ.clone();
                        }
                        t
                    }
                    Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                    _ => Type::Pointer {
                        base: Box::new(Type::Int),
                    },
                };

                write!(
                    s,
                    "load {}, {} {}",
                    self.typ.dump_to_llvm(ctx)?,
                    ptr_ty.dump_to_llvm(ctx)?,
                    addr.dump_to_llvm(ctx)?
                )?;
            }
            OpData::Store { addr, value } => {
                let val_ty = match value {
                    Operand::Value(id) => {
                        let mut t = Type::Int;
                        if let Some(f) = ctx.function {
                            t = f.dfg[*id].typ.clone();
                        }
                        t
                    }
                    Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                    Operand::Int(_) => Type::Int,
                    Operand::Float(_) => Type::Float,
                    Operand::Param { typ, .. } => typ.clone(),
                    _ => Type::Int,
                };
                let ptr_ty = match addr {
                    Operand::Value(id) => {
                        let mut t = Type::Pointer {
                            base: Box::new(Type::Int),
                        };
                        if let Some(f) = ctx.function {
                            t = f.dfg[*id].typ.clone();
                        }
                        t
                    }
                    Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                    _ => Type::Pointer {
                        base: Box::new(Type::Int),
                    },
                };

                write!(
                    s,
                    "store {} {}, {} {}",
                    val_ty.dump_to_llvm(ctx)?,
                    value.dump_to_llvm(ctx)?,
                    ptr_ty.dump_to_llvm(ctx)?,
                    addr.dump_to_llvm(ctx)?
                )?;
            }
            OpData::AddI { lhs, rhs } => write!(
                s,
                "add {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SubI { lhs, rhs } => write!(
                s,
                "sub {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::MulI { lhs, rhs } => write!(
                s,
                "mul {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::DivI { lhs, rhs } => write!(
                s,
                "sdiv {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::ModI { lhs, rhs } => write!(
                s,
                "srem {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::AddF { lhs, rhs } => write!(
                s,
                "fadd {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SubF { lhs, rhs } => write!(
                s,
                "fsub {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::MulF { lhs, rhs } => write!(
                s,
                "fmul {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::DivF { lhs, rhs } => write!(
                s,
                "fdiv {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,

            OpData::SEq { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Int);
                write!(
                    s,
                    "icmp eq {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::SNe { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Int);
                write!(
                    s,
                    "icmp ne {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::SLt { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Int);
                write!(
                    s,
                    "icmp slt {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::SGt { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Int);
                write!(
                    s,
                    "icmp sgt {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::SLe { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Int);
                write!(
                    s,
                    "icmp sle {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::SGe { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Int);
                write!(
                    s,
                    "icmp sge {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::OEq { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Float);
                write!(
                    s,
                    "fcmp oeq {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::ONe { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Float);
                write!(
                    s,
                    "fcmp one {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::OLt { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Float);
                write!(
                    s,
                    "fcmp olt {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::OGt { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Float);
                write!(
                    s,
                    "fcmp ogt {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::OLe { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Float);
                write!(
                    s,
                    "fcmp ole {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }
            OpData::OGe { lhs, rhs } => {
                let cmp_ty = operand_type(lhs, ctx, Type::Float);
                write!(
                    s,
                    "fcmp oge {} {}, {}",
                    cmp_ty.dump_to_llvm(ctx)?,
                    lhs.dump_to_llvm(ctx)?,
                    rhs.dump_to_llvm(ctx)?
                )?
            }

            OpData::Sitofp { value } => {
                let from_op_typ = match value {
                    Operand::Value(id) => {
                        let mut t = Type::Int;
                        if let Some(f) = ctx.function {
                            t = f.dfg[*id].typ.clone();
                        }
                        t
                    }
                    Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                    _ => Type::Int,
                };
                write!(
                    s,
                    "sitofp {} {} to {}",
                    from_op_typ.dump_to_llvm(ctx)?,
                    value.dump_to_llvm(ctx)?,
                    self.typ.dump_to_llvm(ctx)?
                )?
            }
            OpData::Fptosi { value } => {
                let from_op_typ = match value {
                    Operand::Value(id) => {
                        let mut t = Type::Float;
                        if let Some(f) = ctx.function {
                            t = f.dfg[*id].typ.clone();
                        }
                        t
                    }
                    Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                    _ => Type::Float,
                };

                write!(
                    s,
                    "fptosi {} {} to {}",
                    from_op_typ.dump_to_llvm(ctx)?,
                    value.dump_to_llvm(ctx)?,
                    self.typ.dump_to_llvm(ctx)?
                )?
            }
            OpData::Zext { value } => {
                let from_op_typ = match value {
                    Operand::Value(id) => {
                        let mut t = Type::Bool;
                        if let Some(f) = ctx.function {
                            t = f.dfg[*id].typ.clone();
                        }
                        t
                    }
                    Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                    Operand::Bool(_) => Type::Bool,
                    _ => Type::Bool,
                };

                write!(
                    s,
                    "zext {} {} to {}",
                    from_op_typ.dump_to_llvm(ctx)?,
                    value.dump_to_llvm(ctx)?,
                    self.typ.dump_to_llvm(ctx)?
                )?
            }
            OpData::Uitofp { value } => {
                let from_op_typ = match value {
                    Operand::Value(id) => {
                        let mut t = Type::Bool;
                        if let Some(f) = ctx.function {
                            t = f.dfg[*id].typ.clone();
                        }
                        t
                    }
                    Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                    Operand::Bool(_) => Type::Bool,
                    _ => Type::Bool,
                };

                write!(
                    s,
                    "uitofp {} {} to {}",
                    from_op_typ.dump_to_llvm(ctx)?,
                    value.dump_to_llvm(ctx)?,
                    self.typ.dump_to_llvm(ctx)?
                )?
            }

            OpData::Jump { target_bb } => write!(s, "br label {}", target_bb.dump_to_llvm(ctx)?)?,
            OpData::Br {
                cond,
                then_bb,
                else_bb,
            } => {
                let else_label = else_bb.dump_to_llvm(ctx)?; // Ensure else_bb is valid
                write!(
                    s,
                    "br i1 {}, label {}, label {}",
                    cond.dump_to_llvm(ctx)?,
                    then_bb.dump_to_llvm(ctx)?,
                    else_label
                )?
            }
            OpData::Call { func, args } => {
                let func_name = match func {
                    Operand::Func(id) => ctx.program.funcs[*id].name.clone(),
                    _ => "unknown".to_string(),
                };
                write!(s, "call {} @{}(", self.typ.dump_to_llvm(ctx)?, func_name)?;
                for (i, arg) in args.iter().enumerate() {
                    let arg_typ = match arg {
                        Operand::Value(id) => {
                            let mut t = Type::Int;
                            if let Some(f) = ctx.function {
                                t = f.dfg[*id].typ.clone();
                            }
                            t
                        }
                        Operand::Global(id) => ctx.program.globals[*id].typ.clone(),
                        Operand::Int(_) => Type::Int,
                        Operand::Float(_) => Type::Float,
                        _ => Type::Int,
                    };
                    write!(
                        s,
                        "{} {}",
                        arg_typ.dump_to_llvm(ctx)?,
                        arg.dump_to_llvm(ctx)?
                    )?;
                    if i < args.len() - 1 {
                        write!(s, ", ")?;
                    }
                }
                write!(s, ")")?;
            }
            OpData::Phi { incoming } => {
                write!(s, "phi {} ", self.typ.dump_to_llvm(ctx)?)?;
                for (i, phi_incoming) in incoming.iter().enumerate() {
                    if let PhiIncoming::Data { value: val, bb } = phi_incoming {
                        write!(
                            s,
                            "[ {}, {} ]",
                            val.dump_to_llvm(ctx)?,
                            bb.dump_to_llvm(ctx)?
                        )?;
                        if i < incoming.len() - 1 {
                            write!(s, ", ")?;
                        }
                    }
                }
            }
            OpData::Move { value, reg } => {
                write!(s, "# move {} to reg {:?}", value.dump_to_llvm(ctx)?, reg)?
            }
            OpData::And { lhs, rhs } => write!(
                s,
                "and {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Or { lhs, rhs } => write!(
                s,
                "or {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Xor { lhs, rhs } => write!(
                s,
                "xor {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Shl { lhs, rhs } => write!(
                s,
                "shl {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Shr { lhs, rhs } => write!(
                s,
                "lshr {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Sar { lhs, rhs } => write!(
                s,
                "ashr {} {}, {}",
                self.typ.dump_to_llvm(ctx)?,
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
        }
        Ok(s)
    }
}

impl DumpLLVM for BasicBlock {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        let dfg = match ctx.function {
            Some(f) => &f.dfg,
            None => return Ok(s),
        };
        for inst_operand in &self.cur {
            let inst_id = match inst_operand {
                Operand::Value(id) => *id,
                _ => continue,
            };
            let inst = &dfg[inst_id];
            if inst.typ == Type::Void {
                writeln!(s, "  {}", inst.dump_to_llvm(ctx)?)?;
            } else {
                writeln!(
                    s,
                    "  {} = {}",
                    value_operand_name(inst_id, ctx),
                    inst.dump_to_llvm(ctx)?
                )?;
            }
        }
        Ok(s)
    }
}

impl DumpLLVM for Function {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error> {
        let mut s = String::new();

        if self.is_external {
            for (_id, op) in self.dfg.get_all_items() {
                if let Some(op) = op {
                    if let OpData::Declare { .. } = &op.data {
                        return op.dump_to_llvm(ctx);
                    }
                }
            }
            return Ok(s);
        }

        let (ret_ty, param_types) = if let Type::Function {
            return_type,
            param_types,
        } = &self.typ
        {
            (return_type.clone(), param_types)
        } else {
            return Err(std::fmt::Error);
        };

        let mut args_str = String::new();
        for (i, ty) in param_types.iter().enumerate() {
            write!(args_str, "{} %arg{}", ty.dump_to_llvm(ctx)?, i)?;
            if i < param_types.len() - 1 {
                write!(args_str, ", ")?;
            }
        }

        writeln!(
            s,
            "define dso_local {} @{}({}) {{",
            ret_ty.dump_to_llvm(ctx)?,
            self.name,
            args_str
        )?;
        for (bb_id, bb) in self.cfg.get_all_items() {
            if let Some(bb) = bb {
                let bb_ctx = DumpContext {
                    program: ctx.program,
                    function: Some(self),
                };
                writeln!(s, "bb_{}:", bb_id)?;
                writeln!(s, "{}", bb.dump_to_llvm(&bb_ctx)?)?;
            }
        }
        writeln!(s, "}}")?;
        Ok(s)
    }
}

impl DumpLLVM for Program {
    fn dump_to_llvm(&self, _ctx: &DumpContext) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        let program_ctx = DumpContext {
            program: self,
            function: None,
        };

        for (_id, global_op) in self.globals.get_all_items() {
            if let Some(global_op) = global_op {
                if let OpData::Declare { .. } = &global_op.data {
                    writeln!(s, "{}", global_op.dump_to_llvm(&program_ctx)?)?;
                    continue;
                }

                let mut name = None;
                let mut global_array_attr = None;

                for attr in &global_op.attrs {
                    if let Attr::GlobalArray { .. } = attr {
                        global_array_attr = Some(attr);
                    }
                    if let Attr::Name(n) = attr {
                        name = Some(n);
                    }
                }

                if let Some(Attr::GlobalArray {
                    name,
                    mutable,
                    typ,
                    values,
                }) = global_array_attr
                {
                    fn format_initializer(
                        typ: &Type,
                        values: &[ast::Literal],
                        ctx: &DumpContext,
                    ) -> Result<String, std::fmt::Error> {
                        match typ {
                            Type::Array { base, dims } => {
                                if dims.is_empty() {
                                    return Ok("zeroinitializer".to_string());
                                }
                                let current_dim = dims[0] as usize;
                                if dims.len() == 1 {
                                    let mut s = String::new();
                                    write!(s, "[")?;
                                    for i in 0..current_dim {
                                        let v = &values[i];
                                        match v {
                                            ast::Literal::Int(x) => write!(s, "i32 {}", x)?,
                                            ast::Literal::Float(x) => write!(s, "float {}", x)?,
                                            _ => {}
                                        }
                                        if i < current_dim - 1 {
                                            write!(s, ", ")?;
                                        }
                                    }
                                    write!(s, "]")?;
                                    Ok(s)
                                } else {
                                    let mut s = String::new();
                                    write!(s, "[")?;
                                    let sub_array_size = values.len() / current_dim;
                                    let sub_type = Type::Array {
                                        base: base.clone(),
                                        dims: dims[1..].to_vec(),
                                    };
                                    for i in 0..current_dim {
                                        write!(
                                            s,
                                            "{} {}",
                                            sub_type.dump_to_llvm(ctx)?,
                                            format_initializer(
                                                &sub_type,
                                                &values
                                                    [i * sub_array_size..(i + 1) * sub_array_size],
                                                ctx
                                            )?
                                        )?;
                                        if i < current_dim - 1 {
                                            write!(s, ", ")?;
                                        }
                                    }
                                    write!(s, "]")?;
                                    Ok(s)
                                }
                            }
                            _ => {
                                // Scalar type
                                if let Some(v) = values.get(0) {
                                    match v {
                                        ast::Literal::Int(x) => Ok(x.to_string()),
                                        ast::Literal::Float(x) => Ok(x.to_string()),
                                        _ => Ok("zeroinitializer".to_string()),
                                    }
                                } else {
                                    Ok("zeroinitializer".to_string())
                                }
                            }
                        }
                    }

                    let initializer_str = if let Some(values) = values {
                        if !values.is_empty() {
                            format_initializer(typ, values, &program_ctx)?
                        } else {
                            "zeroinitializer".to_string()
                        }
                    } else {
                        "zeroinitializer".to_string()
                    };

                    writeln!(
                        s,
                        "@{} = dso_local {} {} {}, align 4",
                        name,
                        if *mutable { "global" } else { "constant" },
                        typ.dump_to_llvm(&program_ctx)?,
                        initializer_str
                    )?;
                } else if let Some(name) = name {
                    // Non-array global
                    let pointee_type = if let Type::Pointer { base } = &global_op.typ {
                        base.dump_to_llvm(&program_ctx)?
                    } else {
                        global_op.typ.dump_to_llvm(&program_ctx)?
                    };
                    writeln!(
                        s,
                        "@{} = dso_local global {} zeroinitializer, align 4",
                        name, pointee_type
                    )?;
                }
            }
        }

        for (_, func) in self.funcs.get_all_items() {
            if let Some(func) = func {
                if func.is_external {
                    continue;
                }
                let func_ctx = DumpContext {
                    program: self,
                    function: Some(func),
                };
                writeln!(s, "{}", func.dump_to_llvm(&func_ctx)?)?;
            }
        }
        Ok(s)
    }
}

trait ArenaExt<T> {
    fn get_all_items(&self) -> Vec<(usize, Option<&T>)>;
}

impl<T> ArenaExt<T> for IndexedArena<T>
where
    T: std::fmt::Debug,
{
    fn get_all_items(&self) -> Vec<(usize, Option<&T>)> {
        self.storage
            .iter()
            .enumerate()
            .map(|(id, item)| {
                if let ArenaItem::Data(data) = item {
                    (id, Some(data))
                } else {
                    (id, None)
                }
            })
            .collect()
    }
}

pub struct DumpLLVMPass<'a> {
    program: &'a mut Program,
    filename: String,
}

impl<'a> DumpLLVMPass<'a> {
    pub fn new(program: &'a mut Program, filename: String) -> Self {
        Self { program, filename }
    }
}

impl Pass<()> for DumpLLVMPass<'_> {
    fn run(&mut self) {
        let ctx = DumpContext {
            program: &*self.program,
            function: None,
        };
        match self.program.dump_to_llvm(&ctx) {
            Ok(s) => {
                let dump_dir = std::path::Path::new("dump_llvm");
                if !dump_dir.exists() {
                    if let Err(e) = std::fs::create_dir_all(dump_dir) {
                        panic!("Error creating dump directory: {}", e);
                    }
                }
                let file_path = dump_dir.join(format!("{}.ll", self.filename));
                if let Err(e) = std::fs::write(file_path, s) {
                    panic!("Error writing LLVM dump: {}", e);
                }
            }
            Err(e) => panic!("Error dumping LLVM IR: {}", e),
        }
    }
}

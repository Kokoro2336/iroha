/**
 * Dump customized IR into LLVM format for debugging.
 */
use crate::base::ir::*;
use crate::base::Pass;
use crate::base::Type;
use crate::debug::info;
use crate::frontend::ast;
use crate::utils::arena::{ArenaItem, IndexedArena};
use std::fmt::Write;

pub trait DumpLlvm {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error>;
}

pub struct DumpContext<'a> {
    pub program: &'a Program,
    pub function: Option<&'a Function>,
}

impl DumpLlvm for Type {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        match self {
            Type::Int => write!(s, "i32")?,
            Type::Float => write!(s, "float")?,
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

impl DumpLlvm for Operand {
    fn dump_to_llvm(&self, ctx: &DumpContext) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        match self {
            Operand::Value(id) => write!(s, "%{}", id)?,
            Operand::Global(id) => write!(s, "@{}", id)?,
            Operand::Int(val) => write!(s, "{}", val)?,
            Operand::Float(val) => write!(s, "{}", val)?,
            Operand::BB(id) => write!(s, "%bb_{}", id)?,
            Operand::Func(id) => match ctx.program.funcs.get(*id) {
                Ok(Some(func)) => write!(s, "@{}", func.name)?,
                _ => write!(s, "@func_{}", id)?,
            },
            Operand::ParamId(id) => write!(s, "<param_idx = {}>", id)?,
            Operand::Index(id) => write!(s, "<index = {}>", id)?,
            Operand::Reg(reg) => write!(s, "<reg = {:?}>", reg)?,
        }
        Ok(s)
    }
}

impl DumpLlvm for Op {
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
                            if let Ok(Some(op)) = f.dfg.get(*id) {
                                t = op.typ.clone();
                            }
                        }
                        t
                    }
                    Operand::Global(id) => match ctx.program.globals.get(*id) {
                        Ok(Some(op)) => op.typ.clone(),
                        _ => Type::Pointer {
                            base: Box::new(Type::Int),
                        },
                    },
                    _ => Type::Pointer {
                        base: Box::new(Type::Int),
                    },
                };

                let elem_ty = if let Type::Pointer { base } = &ptr_ty {
                    *(base.clone())
                } else {
                    Type::Int
                };

                write!(
                    s,
                    "getelementptr inbounds {}, {} {}",
                    elem_ty.dump_to_llvm(ctx)?,
                    ptr_ty.dump_to_llvm(ctx)?,
                    base.dump_to_llvm(ctx)?
                )?;

                for index in indices {
                    write!(s, ", i32 {}", index.dump_to_llvm(ctx)?)?;
                }
            }
            OpData::Ret { value } => {
                if let Some(val) = value {
                    let ty = match val {
                        Operand::Value(id) => {
                            let mut t = Type::Int;
                            if let Some(f) = ctx.function {
                                if let Ok(Some(op)) = f.dfg.get(*id) {
                                    t = op.typ.clone();
                                }
                            }
                            t
                        }
                        Operand::Int(_) => Type::Int,
                        Operand::Float(_) => Type::Float,
                        _ => Type::Int,
                    };
                    write!(
                        s,
                        "ret {} {}",
                        ty.dump_to_llvm(ctx)?,
                        val.dump_to_llvm(ctx)?
                    )?;
                } else {
                    write!(s, "ret void")?;
                }
            }
            OpData::Alloca(_) => {
                if let Type::Pointer { base } = &self.typ {
                    write!(s, "alloca {}", base.dump_to_llvm(ctx)?)?;
                } else {
                    write!(s, "alloca <invalid_type>")?;
                }
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
                            if let Ok(Some(op)) = f.dfg.get(*id) {
                                t = op.typ.clone();
                            }
                        }
                        t
                    }
                    Operand::Global(id) => match ctx.program.globals.get(*id) {
                        Ok(Some(op)) => op.typ.clone(),
                        _ => Type::Pointer {
                            base: Box::new(Type::Int),
                        },
                    },
                    _ => Type::Pointer {
                        base: Box::new(Type::Int),
                    },
                };
                let ty = if let Type::Pointer { base } = &ptr_ty {
                    *base.clone()
                } else {
                    Type::Int
                };

                write!(
                    s,
                    "load {}, {} {}",
                    ty.dump_to_llvm(ctx)?,
                    ptr_ty.dump_to_llvm(ctx)?,
                    addr.dump_to_llvm(ctx)?
                )?;
            }
            OpData::Store { addr, value } => {
                let val_ty = match value {
                    Operand::Value(id) => {
                        let mut t = Type::Int;
                        if let Some(f) = ctx.function {
                            if let Ok(Some(op)) = f.dfg.get(*id) {
                                t = op.typ.clone();
                            }
                        }
                        t
                    }
                    Operand::Global(id) => match ctx.program.globals.get(*id) {
                        Ok(Some(op)) => op.typ.clone(),
                        _ => Type::Int,
                    },
                    Operand::Int(_) => Type::Int,
                    Operand::Float(_) => Type::Float,
                    _ => Type::Int,
                };
                let ptr_ty = match addr {
                    Operand::Value(id) => {
                        let mut t = Type::Pointer {
                            base: Box::new(Type::Int),
                        };
                        if let Some(f) = ctx.function {
                            if let Ok(Some(op)) = f.dfg.get(*id) {
                                t = op.typ.clone();
                            }
                        }
                        t
                    }
                    Operand::Global(id) => match ctx.program.globals.get(*id) {
                        Ok(Some(op)) => op.typ.clone(),
                        _ => Type::Pointer {
                            base: Box::new(Type::Int),
                        },
                    },
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
                "add i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SubI { lhs, rhs } => write!(
                s,
                "sub i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::MulI { lhs, rhs } => write!(
                s,
                "mul i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::DivI { lhs, rhs } => write!(
                s,
                "sdiv i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::ModI { lhs, rhs } => write!(
                s,
                "srem i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::AddF { lhs, rhs } => write!(
                s,
                "fadd float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SubF { lhs, rhs } => write!(
                s,
                "fsub float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::MulF { lhs, rhs } => write!(
                s,
                "fmul float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::DivF { lhs, rhs } => write!(
                s,
                "fdiv float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,

            OpData::SEq { lhs, rhs } => write!(
                s,
                "icmp eq i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SNe { lhs, rhs } => write!(
                s,
                "icmp ne i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SLt { lhs, rhs } => write!(
                s,
                "icmp slt i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SGt { lhs, rhs } => write!(
                s,
                "icmp sgt i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SLe { lhs, rhs } => write!(
                s,
                "icmp sle i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::SGe { lhs, rhs } => write!(
                s,
                "icmp sge i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::OEq { lhs, rhs } => write!(
                s,
                "fcmp oeq float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::ONe { lhs, rhs } => write!(
                s,
                "fcmp one float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::OLt { lhs, rhs } => write!(
                s,
                "fcmp olt float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::OGt { lhs, rhs } => write!(
                s,
                "fcmp ogt float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::OLe { lhs, rhs } => write!(
                s,
                "fcmp ole float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::OGe { lhs, rhs } => write!(
                s,
                "fcmp oge float {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,

            OpData::Sitofp { value } => {
                let from_op_typ = match value {
                    Operand::Value(id) => {
                        let mut t = Type::Int;
                        if let Some(f) = ctx.function {
                            if let Ok(Some(op)) = f.dfg.get(*id) {
                                t = op.typ.clone();
                            }
                        }
                        t
                    }
                    Operand::Global(id) => match ctx.program.globals.get(*id) {
                        Ok(Some(op)) => op.typ.clone(),
                        _ => Type::Int,
                    },
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
                            if let Ok(Some(op)) = f.dfg.get(*id) {
                                t = op.typ.clone();
                            }
                        }
                        t
                    }
                    Operand::Global(id) => match ctx.program.globals.get(*id) {
                        Ok(Some(op)) => op.typ.clone(),
                        _ => Type::Float,
                    },
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

            OpData::Jump { target_bb } => write!(s, "br label {}", target_bb.dump_to_llvm(ctx)?)?,
            OpData::Br {
                cond,
                then_bb,
                else_bb,
            } => {
                let else_label = match else_bb {
                    Some(bb) => bb.dump_to_llvm(ctx)?,
                    None => "bb_unknown".to_string(),
                };
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
                    Operand::Func(id) => match ctx.program.funcs.get(*id) {
                        Ok(Some(f)) => f.name.clone(),
                        _ => format!("func_{}", id),
                    },
                    _ => "unknown".to_string(),
                };
                // This is still a simplification, as we don't have full function type info.
                write!(s, "call {} @{}(", "i32", func_name)?;
                for (i, arg) in args.iter().enumerate() {
                    let arg_typ = match arg {
                        Operand::Value(id) => {
                            let mut t = Type::Int;
                            if let Some(f) = ctx.function {
                                if let Ok(Some(op)) = f.dfg.get(*id) {
                                    t = op.typ.clone();
                                }
                            }
                            t
                        }
                        Operand::Global(id) => match ctx.program.globals.get(*id) {
                            Ok(Some(op)) => op.typ.clone(),
                            _ => Type::Int,
                        },
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
                for (i, (val, bb)) in incoming.iter().enumerate() {
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
            OpData::GetArg(idx) => {
                let id = match idx {
                    Operand::ParamId(id) => *id,
                    _ => 0,
                };
                write!(s, "add {} %arg{}, 0", self.typ.dump_to_llvm(ctx)?, id)?;
            }
            OpData::Move { value, reg } => {
                write!(s, "# move {} to reg {:?}", value.dump_to_llvm(ctx)?, reg)?
            }
            OpData::And { lhs, rhs } => write!(
                s,
                "and i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Or { lhs, rhs } => write!(
                s,
                "or i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Xor { lhs, rhs } => write!(
                s,
                "xor i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Shl { lhs, rhs } => write!(
                s,
                "shl i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Shr { lhs, rhs } => write!(
                s,
                "lshr i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
            OpData::Sar { lhs, rhs } => write!(
                s,
                "ashr i32 {}, {}",
                lhs.dump_to_llvm(ctx)?,
                rhs.dump_to_llvm(ctx)?
            )?,
        }
        Ok(s)
    }
}

impl DumpLlvm for BasicBlock {
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
            if let Ok(Some(inst)) = dfg.get(inst_id) {
                if inst.typ == Type::Void {
                    writeln!(s, "  {}", inst.dump_to_llvm(ctx)?)?;
                } else {
                    writeln!(s, "  %{} = {}", inst_id, inst.dump_to_llvm(ctx)?)?;
                }
            }
        }
        Ok(s)
    }
}

impl DumpLlvm for Function {
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

        let ret_ty = if let Type::Function { return_type, .. } = &self.typ {
            return_type.clone()
        } else {
            return Err(std::fmt::Error);
        };

        let mut args_str = String::new();
        let mut get_arg_ops = vec![];
        for (_id, op) in self.dfg.get_all_items() {
            if let Some(op) = op {
                if let OpData::GetArg(Operand::ParamId(id)) = &op.data {
                    get_arg_ops.push((*id, op.typ.clone()));
                }
            }
        }
        get_arg_ops.sort_by_key(|a| a.0);
        for (i, (id, ty)) in get_arg_ops.iter().enumerate() {
            write!(args_str, "{} %arg{}", ty.dump_to_llvm(ctx)?, id)?;
            if i < get_arg_ops.len() - 1 {
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

impl DumpLlvm for Program {
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
                    let mut initializer_str = String::new();
                    if !values.is_empty() {
                        write!(initializer_str, "[")?;
                        for (i, v) in values.iter().enumerate() {
                            match v {
                                ast::Literal::Int(x) => write!(initializer_str, "i32 {}", x)?,
                                ast::Literal::Float(x) => write!(initializer_str, "float {}", x)?,
                                _ => {}
                            }
                            if i < values.len() - 1 {
                                write!(initializer_str, ", ")?;
                            }
                        }
                        write!(initializer_str, "]")?;
                    } else {
                        initializer_str = "zeroinitializer".to_string();
                    }

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

pub struct DumpLlvmPass {
    program: Program,
    filename: String,
}

impl DumpLlvmPass {
    pub fn new(program: Program, filename: String) -> Self {
        Self { program, filename }
    }
}

impl Pass<Program> for DumpLlvmPass {
    fn run(&mut self) -> std::result::Result<Program, String> {
        let ctx = DumpContext {
            program: &self.program,
            function: None,
        };
        match self.program.dump_to_llvm(&ctx) {
            Ok(s) => {
                let dump_dir = std::path::Path::new("dump_llvm");
                if !dump_dir.exists() {
                    std::fs::create_dir_all(dump_dir).map_err(|e| e.to_string())?;
                }
                let file_path = dump_dir.join(format!("{}.ll", self.filename));
                std::fs::write(file_path, s).map_err(|e| e.to_string())?;
            }
            Err(e) => info!("Error dumping LLVM IR: {}", e),
        }
        Ok(std::mem::take(&mut self.program))
    }
}

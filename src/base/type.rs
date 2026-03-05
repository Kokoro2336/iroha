use crate::backend::config::RISCV_BITS;

/// type of value
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Void,
    Float,
    Bool,
    Array {
        base: Box<Type>,
        dims: Vec<u32>,
    },
    Pointer {
        base: Box<Type>,
    },
    Function {
        return_type: Box<Type>,
        param_types: Vec<Type>,
    },
    // only occurs in SysY lib function
    Char, /*u8*/
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Float => write!(f, "float"),
            Type::Void => write!(f, "void"),
            Type::Bool => write!(f, "bool"),
            Type::Array { base, dims } => {
                write!(f, "{}", base)?;
                for dim in dims {
                    write!(f, "[{}]", dim)?;
                }
                Ok(())
            }
            Type::Pointer { base } => {
                write!(f, "{}*", base)
            }
            Type::Function {
                return_type,
                param_types,
            } => {
                write!(f, "fn(")?;
                for (i, param) in param_types.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i != param_types.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ") -> {}", return_type)
            }
            Type::Char => {
                write!(f, "char")
            }
        }
    }
}

impl Type {
    pub fn size_in_bytes(&self) -> u32 {
        match self {
            Type::Bool => 1,
            Type::Int => 4,
            Type::Float => 4,
            Type::Void => 0,
            Type::Array { base, dims } => base.size_in_bytes() * dims.iter().product::<u32>(),
            Type::Pointer { .. } => RISCV_BITS / 8,
            Type::Function { .. } => panic!("Function type has no size"),
            Type::Char => 1,
        }
    }
    pub fn is_scalar(&self) -> bool {
        matches!(self, Type::Int | Type::Float | Type::Char | Type::Bool)
    }
}

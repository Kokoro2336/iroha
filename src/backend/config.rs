pub const REG_IDLE: u32 = u32::MAX;
pub const STK_FRM_BASE_LENGTH: u32 = 16; // 16 bytes for minimum
pub const RISCV_BITS: u32 = 32;
pub const REG_PARAMS_MAX_NUM: u32 = 8;

#[derive(Clone, Debug)]
pub enum RVOp {
    Beqz,
    Bnez,
    J,
    Call,
    Ret,
    Lw,
    Sw,
    Add,
    Addi,
    Sub,
    Slt,
    Sgt,
    Seqz,
    Snez,
    Xor,
    Xori,
    Or,
    Ori,
    And,
    Andi,
    Sll,
    Srl,
    Sra,
    Mul,
    Div,
    Rem,
    Li,
    La,
    Mv,
}

impl std::fmt::Display for RVOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RVOp::Beqz => write!(f, "beqz"),
            RVOp::Bnez => write!(f, "bnez"),
            RVOp::J => write!(f, "j"),
            RVOp::Call => write!(f, "call"),
            RVOp::Ret => write!(f, "ret"),
            RVOp::Lw => write!(f, "lw"),
            RVOp::Sw => write!(f, "sw"),
            RVOp::Add => write!(f, "add"),
            RVOp::Addi => write!(f, "addi"),
            RVOp::Sub => write!(f, "sub"),
            RVOp::Slt => write!(f, "slt"),
            RVOp::Sgt => write!(f, "sgt"),
            RVOp::Seqz => write!(f, "seqz"),
            RVOp::Snez => write!(f, "snez"),
            RVOp::Xor => write!(f, "xor"),
            RVOp::Xori => write!(f, "xori"),
            RVOp::Or => write!(f, "or"),
            RVOp::Ori => write!(f, "ori"),
            RVOp::And => write!(f, "and"),
            RVOp::Andi => write!(f, "andi"),
            RVOp::Sll => write!(f, "sll"),
            RVOp::Srl => write!(f, "srl"),
            RVOp::Sra => write!(f, "sra"),
            RVOp::Mul => write!(f, "mul"),
            RVOp::Div => write!(f, "div"),
            RVOp::Rem => write!(f, "rem"),
            RVOp::Li => write!(f, "li"),
            RVOp::La => write!(f, "la"),
            RVOp::Mv => write!(f, "mv"),
        }
    }
}

#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Reg {
    Zero = 0, // hardwired zero
    Ra = 1,   // return address
    Sp = 2,   // stack pointer
    Gp = 3,   // global pointer
    Tp = 4,   // thread pointer
    T0 = 5,
    T1 = 6,
    T2 = 7, // temporaries
    S0 = 8, // fp
    S1 = 9, // saved registers / frame sc_var
    A0 = 10,
    A1 = 11,
    A2 = 12,
    A3 = 13,
    A4 = 14,
    A5 = 15,
    A6 = 16,
    A7 = 17, // FnDecl arguments / return values
    S2 = 18,
    S3 = 19,
    S4 = 20,
    S5 = 21,
    S6 = 22,
    S7 = 23,
    S8 = 24,
    S9 = 25,
    S10 = 26,
    S11 = 27, // saved registers
    T3 = 28,
    T4 = 29,
    T5 = 30,
    T6 = 31, // temporaries
}

impl Reg {
    pub fn is_temp(&self) -> bool {
        (*self as u8 >= Reg::T0 as u8 && *self as u8 <= Reg::T2 as u8)
            || (*self as u8 >= Reg::T3 as u8 && *self as u8 <= Reg::T6 as u8)
            || (*self as u8 >= Reg::A0 as u8 && *self as u8 <= Reg::A7 as u8)
    }
}

impl std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Reg::Zero => write!(f, "x0"),
            Reg::Ra => write!(f, "x1"),
            Reg::Sp => write!(f, "x2"),
            Reg::Gp => write!(f, "x3"),
            Reg::Tp => write!(f, "x4"),
            Reg::T0 => write!(f, "x5"),
            Reg::T1 => write!(f, "x6"),
            Reg::T2 => write!(f, "x7"),
            Reg::S0 => write!(f, "x8"),
            Reg::S1 => write!(f, "x9"),
            Reg::A0 => write!(f, "x10"),
            Reg::A1 => write!(f, "x11"),
            Reg::A2 => write!(f, "x12"),
            Reg::A3 => write!(f, "x13"),
            Reg::A4 => write!(f, "x14"),
            Reg::A5 => write!(f, "x15"),
            Reg::A6 => write!(f, "x16"),
            Reg::A7 => write!(f, "x17"),
            Reg::S2 => write!(f, "x18"),
            Reg::S3 => write!(f, "x19"),
            Reg::S4 => write!(f, "x20"),
            Reg::S5 => write!(f, "x21"),
            Reg::S6 => write!(f, "x22"),
            Reg::S7 => write!(f, "x23"),
            Reg::S8 => write!(f, "x24"),
            Reg::S9 => write!(f, "x25"),
            Reg::S10 => write!(f, "x26"),
            Reg::S11 => write!(f, "x27"),
            Reg::T3 => write!(f, "x28"),
            Reg::T4 => write!(f, "x29"),
            Reg::T5 => write!(f, "x30"),
            Reg::T6 => write!(f, "x31"),
        }
    }
}

impl Reg {
    /// Get numeric index (0..=31) for use as array index
    pub fn idx(self) -> usize {
        self as usize
    }
}

/// Definition of Lower IR (LIR) instructions.
use crate::ir::lir::Reg;

/// Instruction definition of Lower IR.
#[derive(Debug, Clone, Copy)]
pub enum Inst {
    // ==========================================
    // 1. Pseudo-instructions & Data Movement
    // ==========================================
    /// Load Immediate: Materializes a 32-bit constant.
    Li { rd: InstOperand, imm: InstOperand },
    /// Load Address: Materializes the absolute address of a global variable or array.
    La { rd: InstOperand, imm: InstOperand },
    /// Move: Register-to-register copy.
    /// Crucial for Phi elimination and register spilling/reloading.
    Mv { rd: InstOperand, rs: InstOperand },
    /// FP Move (Single): Copy between floating-point registers.
    FmvS { rd: InstOperand, rs: InstOperand },

    // ==========================================
    // 2. Integer Arithmetic & Logic
    // CRITICAL for SysY: SysY 'int' is strictly 32-bit.
    // If your target is RV64, you MUST use the 'w' (word) suffix for ALU ops
    // to ensure proper sign-extension and prevent silent overflow bugs.
    // ==========================================
    Addw {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    Subw {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    Mulw {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    Divw {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    Remw {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    }, // SysY +, -, *, /, % (32-bit math on 64-bit arch)
    Slliw {
        rd: InstOperand,
        rs1: InstOperand,
        imm: InstOperand,
    },
    Srliw {
        rd: InstOperand,
        rs1: InstOperand,
        imm: InstOperand,
    },
    Sraiw {
        rd: InstOperand,
        rs1: InstOperand,
        imm: InstOperand,
    }, // Shift by immediate (e.g., array index scaling: i * 4)
    Sllw {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    Srlw {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    Sraw {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    }, // Shift by register
    And {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    Or {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    Xor {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    }, // Bitwise/Logical operations
    Andi {
        rd: InstOperand,
        rs1: InstOperand,
        imm: InstOperand,
    },
    Ori {
        rd: InstOperand,
        rs1: InstOperand,
        imm: InstOperand,
    },
    Xori {
        rd: InstOperand,
        rs1: InstOperand,
        imm: InstOperand,
    }, // Bitwise/Logical with immediate

    // ==========================================
    // 3. Floating-Point Arithmetic (F-Extension)
    // ==========================================
    FaddS {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    FsubS {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    FmulS {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    FdivS {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    }, // Single-precision math
    FeqS {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    FltS {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    },
    FleS {
        rd: InstOperand,
        rs1: InstOperand,
        rs2: InstOperand,
    }, // FP comparisons (==, <, <=)

    /// Float to Int conversion.
    /// Matches SysY semantic: truncate/round towards zero (RTZ).
    FcvtWS { rd: InstOperand, rs: InstOperand },
    /// Int to Float conversion.
    FcvtSW { rd: InstOperand, rs: InstOperand },

    /// Move bit-pattern from Integer to FP register.
    /// Required by RISC-V ABI when passing float args in integer registers.
    FmvWX { rd: InstOperand, rs: InstOperand },
    /// Move bit-pattern from FP to Integer register.
    FmvXW { rd: InstOperand, rs: InstOperand },

    // ==========================================
    // 4. Memory Access
    // ==========================================
    Lw {
        rd: InstOperand,
        base: InstOperand,
        offset: InstOperand,
    },
    Sw {
        rs: InstOperand,
        base: InstOperand,
        offset: InstOperand,
    }, // Load/Store 32-bit word (SysY int variable/array element)
    Flw {
        rd: InstOperand,
        base: InstOperand,
        offset: InstOperand,
    },
    Fsw {
        rs: InstOperand,
        base: InstOperand,
        offset: InstOperand,
    }, // Load/Store 32-bit float (SysY float variable/array element)

    /// Load/Store 64-bit doubleword.
    /// ONLY used for Pointers (e.g., array base addresses) or Stack Frame management in RV64.
    Ld {
        rd: InstOperand,
        base: InstOperand,
        offset: InstOperand,
    },
    Sd {
        rs: InstOperand,
        base: InstOperand,
        offset: InstOperand,
    },

    // ==========================================
    // 5. Control Flow
    // ==========================================
    /// Unconditional jump (translates 'break', 'continue', or block merges).
    J { offset: InstOperand },
    /// Function call. Use this pseudo-instruction and let the assembler handle ra/auipc/jalr.
    Call { target: InstOperand },
    /// Return. Pseudo for 'jalr x0, 0(ra)'.
    Ret,
    Beq {
        rs1: InstOperand,
        rs2: InstOperand,
        offset: InstOperand,
    },
    Bne {
        rs1: InstOperand,
        rs2: InstOperand,
        offset: InstOperand,
    }, // Branch if Equal / Not Equal
    Blt {
        rs1: InstOperand,
        rs2: InstOperand,
        offset: InstOperand,
    },
    Bge {
        rs1: InstOperand,
        rs2: InstOperand,
        offset: InstOperand,
    }, // Branch if Less Than / Greater or Equal (Signed - SysY default)
    Bltu {
        rs1: InstOperand,
        rs2: InstOperand,
        offset: InstOperand,
    },
    Bgeu {
        rs1: InstOperand,
        rs2: InstOperand,
        offset: InstOperand,
    }, // Branch Unsigned (Used strictly for pointer/address bound checks)
}

impl std::fmt::Display for Inst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Inst::Li { rd, imm } => write!(f, "li {rd}, {imm}"),
            Inst::La { rd, imm } => write!(f, "la {rd}, {imm}"),
            Inst::Mv { rd, rs } => write!(f, "mv {rd}, {rs}"),
            Inst::FmvS { rd, rs } => write!(f, "fmv.s {rd}, {rs}"),

            Inst::Addw { rd, rs1, rs2 } => write!(f, "addw {rd}, {rs1}, {rs2}"),
            Inst::Subw { rd, rs1, rs2 } => write!(f, "subw {rd}, {rs1}, {rs2}"),
            Inst::Mulw { rd, rs1, rs2 } => write!(f, "mulw {rd}, {rs1}, {rs2}"),
            Inst::Divw { rd, rs1, rs2 } => write!(f, "divw {rd}, {rs1}, {rs2}"),
            Inst::Remw { rd, rs1, rs2 } => write!(f, "remw {rd}, {rs1}, {rs2}"),
            Inst::Slliw { rd, rs1, imm } => write!(f, "slliw {rd}, {rs1}, {imm}"),
            Inst::Srliw { rd, rs1, imm } => write!(f, "srliw {rd}, {rs1}, {imm}"),
            Inst::Sraiw { rd, rs1, imm } => write!(f, "sraiw {rd}, {rs1}, {imm}"),
            Inst::Sllw { rd, rs1, rs2 } => write!(f, "sllw {rd}, {rs1}, {rs2}"),
            Inst::Srlw { rd, rs1, rs2 } => write!(f, "srlw {rd}, {rs1}, {rs2}"),
            Inst::Sraw { rd, rs1, rs2 } => write!(f, "sraw {rd}, {rs1}, {rs2}"),
            Inst::And { rd, rs1, rs2 } => write!(f, "and {rd}, {rs1}, {rs2}"),
            Inst::Or { rd, rs1, rs2 } => write!(f, "or {rd}, {rs1}, {rs2}"),
            Inst::Xor { rd, rs1, rs2 } => write!(f, "xor {rd}, {rs1}, {rs2}"),
            Inst::Andi { rd, rs1, imm } => write!(f, "andi {rd}, {rs1}, {imm}"),
            Inst::Ori { rd, rs1, imm } => write!(f, "ori {rd}, {rs1}, {imm}"),
            Inst::Xori { rd, rs1, imm } => write!(f, "xori {rd}, {rs1}, {imm}"),

            Inst::FaddS { rd, rs1, rs2 } => write!(f, "fadd.s {rd}, {rs1}, {rs2}"),
            Inst::FsubS { rd, rs1, rs2 } => write!(f, "fsub.s {rd}, {rs1}, {rs2}"),
            Inst::FmulS { rd, rs1, rs2 } => write!(f, "fmul.s {rd}, {rs1}, {rs2}"),
            Inst::FdivS { rd, rs1, rs2 } => write!(f, "fdiv.s {rd}, {rs1}, {rs2}"),
            Inst::FeqS { rd, rs1, rs2 } => write!(f, "feq.s {rd}, {rs1}, {rs2}"),
            Inst::FltS { rd, rs1, rs2 } => write!(f, "flt.s {rd}, {rs1}, {rs2}"),
            Inst::FleS { rd, rs1, rs2 } => write!(f, "fle.s {rd}, {rs1}, {rs2}"),
            Inst::FcvtWS { rd, rs } => write!(f, "fcvt.w.s {rd}, {rs}"),
            Inst::FcvtSW { rd, rs } => write!(f, "fcvt.s.w {rd}, {rs}"),
            Inst::FmvWX { rd, rs } => write!(f, "fmv.w.x {rd}, {rs}"),
            Inst::FmvXW { rd, rs } => write!(f, "fmv.x.w {rd}, {rs}"),

            Inst::Lw { rd, base, offset } => write!(f, "lw {rd}, {offset}({base})"),
            Inst::Sw { rs, base, offset } => write!(f, "sw {rs}, {offset}({base})"),
            Inst::Flw { rd, base, offset } => write!(f, "flw {rd}, {offset}({base})"),
            Inst::Fsw { rs, base, offset } => write!(f, "fsw {rs}, {offset}({base})"),
            Inst::Ld { rd, base, offset } => write!(f, "ld {rd}, {offset}({base})"),
            Inst::Sd { rs, base, offset } => write!(f, "sd {rs}, {offset}({base})"),

            Inst::J { offset } => write!(f, "j {offset}"),
            Inst::Call { target } => write!(f, "call {target}"),
            Inst::Ret => write!(f, "ret"),
            Inst::Beq { rs1, rs2, offset } => write!(f, "beq {rs1}, {rs2}, {offset}"),
            Inst::Bne { rs1, rs2, offset } => write!(f, "bne {rs1}, {rs2}, {offset}"),
            Inst::Blt { rs1, rs2, offset } => write!(f, "blt {rs1}, {rs2}, {offset}"),
            Inst::Bge { rs1, rs2, offset } => write!(f, "bge {rs1}, {rs2}, {offset}"),
            Inst::Bltu { rs1, rs2, offset } => write!(f, "bltu {rs1}, {rs2}, {offset}"),
            Inst::Bgeu { rs1, rs2, offset } => write!(f, "bgeu {rs1}, {rs2}, {offset}"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum InstOperand {
    Virt(usize),
    Phys(Reg),
    IntImm(i32),
    FloatImm(f32),
}

impl std::fmt::Display for InstOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstOperand::Virt(id) => write!(f, "v{id}"),
            InstOperand::Phys(reg) => write!(f, "{reg}"),
            InstOperand::IntImm(v) => write!(f, "{v}"),
            InstOperand::FloatImm(v) => write!(f, "{v}"),
        }
    }
}

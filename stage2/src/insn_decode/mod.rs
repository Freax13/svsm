// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2024 Intel Corporation.
//
// Author: Chuanxiao Dong <chuanxiao.dong@intel.com>

mod decode;
mod insn;
mod opcode;

pub use decode::{DecodedInsnCtx, InsnMachineCtx};
pub use insn::{DecodedInsn, Immediate, Instruction, Operand, Register, SegRegister};

/// An error that can occur during instruction decoding.
#[derive(Copy, Clone, Debug)]
pub enum InsnError {
    /// Error while decoding the displacement bytes.
    DecodeDisp,
    /// Error while decoding the immediate bytes.
    DecodeImm,
    /// Error while decoding the Mem-Offset bytes.
    DecodeMOffset,
    /// Error while decoding the ModR/M byte.
    DecodeModRM,
    /// Error while decoding the OpCode bytes.
    DecodeOpCode,
    /// Error while decoding the SIB byte.
    DecodeSib,
    /// No OpCodeDesc generated while decoding.
    NoOpCodeDesc,
    /// Error while peeking an instruction byte.
    InsnPeek,
    /// The instruction decoding is not invalid.
    InvalidDecode,
    /// Invalid RegCode for decoding Register.
    InvalidRegister,
    /// The decoded instruction is not supported.
    UnSupportedInsn,
    /// Error while translating linear address.
    TranslateLinearAddr,
    /// Error while handling MMIO read operation.
    HandleMmioRead,
    /// Error while handling MMIO write operation.
    HandleMmioWrite,
}

impl From<InsnError> for crate::error::SvsmError {
    fn from(e: InsnError) -> Self {
        Self::Insn(e)
    }
}

// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2023 SUSE LLC
//
// Author: Carlos López <carlos.lopez@suse.com>

//! High level error typing for the public SVSM APIs.
//!
//! This module contains the generic [`SvsmError`] type, which may be returned
//! from any public API in this codebase to signal an error during SVSM
//! operation. Each variant of the type may give more specific information
//! about the source of the error.
//!
//! As a general rule, functions private to a given module may directly return
//! leaf error types, which are contained in [`SvsmError`] variants. Public
//! functions should return an [`SvsmError`] containing a leaf error type,
//! usually the one corresponding to that module. Each module should provide
//! a way to convert a leaf error into a SvsmError via the [`From`] trait.

use crate::fw_cfg::FwCfgError;
use crate::mm::alloc::AllocError;
use crate::sev::ghcb::GhcbError;
use crate::sev::msr_protocol::GhcbMsrError;
use crate::sev::SevSnpError;
use elf::ElfError;

/// A generic error during SVSM operation.
#[derive(Clone, Copy, Debug)]
pub enum SvsmError {
    /// Errors related to platform initialization.
    PlatformInit,
    /// Errors during ELF parsing and loading.
    Elf(ElfError),
    /// Errors related to GHCB
    Ghcb(GhcbError),
    /// Errors related to MSR protocol
    GhcbMsr(GhcbMsrError),
    /// Errors related to SEV-SNP operations, like PVALIDATE or RMPUPDATE
    SevSnp(SevSnpError),
    /// Errors related to TDX operations
    Tdx,
    /// Generic errors related to memory management
    Mem,
    /// Errors related to the memory allocator
    Alloc(AllocError),
    /// Error reported when convert a usize to Bytes
    InvalidBytes,
    /// Errors related to firmware parsing
    Firmware,
    /// Errors related to console operation
    Console,
    /// Errors related to firmware configuration contents
    FwCfg(FwCfgError),
    /// Errors related to ACPI parsing.
    Acpi,
}

impl From<ElfError> for SvsmError {
    fn from(err: ElfError) -> Self {
        Self::Elf(err)
    }
}

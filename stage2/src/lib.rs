// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Nicolai Stange <nstange@suse.de>

#![no_std]

pub mod acpi;
pub mod address;
pub mod config;
pub mod console;
pub mod cpu;
pub mod crypto;
pub mod debug;
pub mod error;
pub mod fs;
pub mod fw_cfg;
pub mod fw_meta;
pub mod greq;
pub mod igvm_params;
pub mod insn_decode;
pub mod io;
pub mod kernel_region;
pub mod locking;
pub mod mm;
pub mod platform;
pub mod protocols;
pub mod requests;
pub mod serial;
pub mod sev;
pub mod string;
pub mod svsm_console;
pub mod svsm_paging;
pub mod syscall;
pub mod task;
pub mod types;
pub mod utils;
#[cfg(all(feature = "mstpm", not(test)))]
pub mod vtpm;

// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use core::arch::asm;

pub fn read_cr2() -> usize {
    let ret: usize;
    unsafe {
        asm!("mov %cr2, %rax",
             out("rax") ret,
             options(att_syntax));
    }
    ret
}

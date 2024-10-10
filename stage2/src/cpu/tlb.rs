// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use core::arch::asm;

//const INVLPGB_VALID_VA: u64 = 1u64 << 0;
//const INVLPGB_VALID_PCID: u64 = 1u64 << 1;
const INVLPGB_VALID_ASID: u64 = 1u64 << 2;
const INVLPGB_VALID_GLOBAL: u64 = 1u64 << 3;

#[inline]
fn do_invlpgb(rax: u64, rcx: u64, rdx: u64) {
    unsafe {
        asm!(".byte 0x0f, 0x01, 0xfe",
             in("rax") rax,
             in("rcx") rcx,
             in("rdx") rdx,
             options(att_syntax));
    }
}

#[inline]
fn do_tlbsync() {
    unsafe {
        asm!(".byte 0x0f, 0x01, 0xff", options(att_syntax));
    }
}

pub fn flush_tlb_global() {
    let rax: u64 = INVLPGB_VALID_ASID | INVLPGB_VALID_GLOBAL;
    do_invlpgb(rax, 0, 0);
}

pub fn flush_tlb_global_sync() {
    flush_tlb_global();
    do_tlbsync();
}

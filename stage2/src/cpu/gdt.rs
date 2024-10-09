// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::address::VirtAddr;
use crate::types::{SVSM_CS, SVSM_DS};
use core::arch::asm;

#[repr(C, packed(2))]
#[derive(Clone, Copy, Debug, Default)]
struct GDTDesc {
    size: u16,
    addr: VirtAddr,
}

#[derive(Copy, Clone, Debug, Default)]
pub struct GDTEntry(u64);

impl GDTEntry {
    pub const fn from_raw(entry: u64) -> Self {
        Self(entry)
    }

    pub const fn null() -> Self {
        Self(0u64)
    }

    pub const fn code_64_kernel() -> Self {
        Self(0x00af9a000000ffffu64)
    }

    pub const fn data_64_kernel() -> Self {
        Self(0x00cf92000000ffffu64)
    }

    pub const fn code_64_user() -> Self {
        Self(0x00affb000000ffffu64)
    }

    pub const fn data_64_user() -> Self {
        Self(0x00cff2000000ffffu64)
    }
}

const GDT_SIZE: u16 = 8;

#[derive(Copy, Clone, Debug, Default)]
pub struct GDT {
    entries: [GDTEntry; GDT_SIZE as usize],
}

impl GDT {
    pub const fn new() -> Self {
        Self {
            entries: [
                GDTEntry::null(),
                GDTEntry::code_64_kernel(),
                GDTEntry::data_64_kernel(),
                GDTEntry::code_64_user(),
                GDTEntry::data_64_user(),
                GDTEntry::null(),
                GDTEntry::null(),
                GDTEntry::null(),
            ],
        }
    }

    /// Load a GDT. Its lifetime must be static so that its entries are
    /// always available to the CPU.
    pub fn load(&'static self) {
        let gdt_desc = self.descriptor();
        unsafe {
            asm!(r#" /* Load GDT */
                 lgdt   (%rax)

                 /* Reload data segments */
                 movw   %cx, %ds
                 movw   %cx, %es
                 movw   %cx, %fs
                 movw   %cx, %gs
                 movw   %cx, %ss

                 /* Reload code segment */
                 pushq  %rdx
                 leaq   1f(%rip), %rax
                 pushq  %rax
                 lretq
            1:
                 "#,
                in("rax") &gdt_desc,
                in("rdx") SVSM_CS,
                in("rcx") SVSM_DS,
                options(att_syntax));
        }
    }

    fn descriptor(&self) -> GDTDesc {
        GDTDesc {
            size: (GDT_SIZE * 8) - 1,
            addr: VirtAddr::from(self.entries.as_ptr()),
        }
    }
}

pub static GDT: GDT = GDT::new();

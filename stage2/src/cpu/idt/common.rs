// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::address::{Address, VirtAddr};
use crate::cpu::registers::{X86GeneralRegs, X86InterruptFrame};
use crate::locking::{RWLock, WriteLockGuard};
use crate::types::SVSM_CS;
use core::arch::{asm, global_asm};

pub const DF_VECTOR: usize = 8;
pub const HV_VECTOR: usize = 28;

bitflags::bitflags! {
    /// Page fault error code flags.
    #[derive(Clone, Copy, Debug, PartialEq)]
    pub struct PageFaultError :u32 {
        const P     = 1 << 0;
        const W     = 1 << 1;
        const U     = 1 << 2;
        const R     = 1 << 3;
        const I     = 1 << 4;
    }
}

#[repr(C, packed)]
#[derive(Default, Debug, Clone, Copy)]
pub struct X86ExceptionContext {
    pub regs: X86GeneralRegs,
    pub error_code: usize,
    pub frame: X86InterruptFrame,
}

#[derive(Copy, Clone, Default, Debug)]
#[repr(C, packed)]
pub struct IdtEntry {
    low: u64,
    high: u64,
}

const IDT_TARGET_MASK_1: u64 = 0x0000_0000_0000_ffff;
const IDT_TARGET_MASK_2: u64 = 0x0000_0000_ffff_0000;
const IDT_TARGET_MASK_3: u64 = 0xffff_ffff_0000_0000;

const IDT_TARGET_MASK_1_SHIFT: u64 = 0;
const IDT_TARGET_MASK_2_SHIFT: u64 = 48 - 16;
const IDT_TARGET_MASK_3_SHIFT: u64 = 32;

const IDT_TYPE_MASK: u8 = 0x0f;
const IDT_TYPE_SHIFT: u64 = 40;
const IDT_TYPE_CALL: u8 = 0x0c;
const IDT_TYPE_INT: u8 = 0x0e;
const IDT_TYPE_TRAP: u8 = 0x0f;

fn idt_type_mask(t: u8) -> u64 {
    ((t & IDT_TYPE_MASK) as u64) << IDT_TYPE_SHIFT
}

const IDT_DPL_MASK: u8 = 0x03;
const IDT_DPL_SHIFT: u64 = 45;

fn idt_dpl_mask(dpl: u8) -> u64 {
    ((dpl & IDT_DPL_MASK) as u64) << IDT_DPL_SHIFT
}

const IDT_PRESENT_MASK: u64 = 0x1u64 << 47;
const IDT_CS_SHIFT: u64 = 16;

const IDT_IST_MASK: u64 = 0x7;
const IDT_IST_SHIFT: u64 = 32;

impl IdtEntry {
    fn create(target: VirtAddr, cs: u16, desc_type: u8, dpl: u8, ist: u8) -> Self {
        let vaddr = target.bits() as u64;
        let cs_mask = (cs as u64) << IDT_CS_SHIFT;
        let ist_mask = ((ist as u64) & IDT_IST_MASK) << IDT_IST_SHIFT;
        let low = (vaddr & IDT_TARGET_MASK_1) << IDT_TARGET_MASK_1_SHIFT
            | (vaddr & IDT_TARGET_MASK_2) << IDT_TARGET_MASK_2_SHIFT
            | idt_type_mask(desc_type)
            | IDT_PRESENT_MASK
            | idt_dpl_mask(dpl)
            | cs_mask
            | ist_mask;
        let high = (vaddr & IDT_TARGET_MASK_3) >> IDT_TARGET_MASK_3_SHIFT;

        IdtEntry { low, high }
    }

    pub fn raw_entry(target: VirtAddr) -> Self {
        IdtEntry::create(target, SVSM_CS, IDT_TYPE_INT, 0, 0)
    }

    pub fn entry(handler: unsafe extern "C" fn()) -> Self {
        let target = VirtAddr::from(handler as *const ());
        IdtEntry::create(target, SVSM_CS, IDT_TYPE_INT, 0, 0)
    }

    pub fn user_entry(handler: unsafe extern "C" fn()) -> Self {
        let target = VirtAddr::from(handler as *const ());
        IdtEntry::create(target, SVSM_CS, IDT_TYPE_INT, 3, 0)
    }

    pub fn ist_entry(handler: unsafe extern "C" fn(), ist: u8) -> Self {
        let target = VirtAddr::from(handler as *const ());
        IdtEntry::create(target, SVSM_CS, IDT_TYPE_INT, 0, ist)
    }

    pub fn trap_entry(handler: unsafe extern "C" fn()) -> Self {
        let target = VirtAddr::from(handler as *const ());
        IdtEntry::create(target, SVSM_CS, IDT_TYPE_TRAP, 0, 0)
    }

    pub fn call_entry(handler: unsafe extern "C" fn()) -> Self {
        let target = VirtAddr::from(handler as *const ());
        IdtEntry::create(target, SVSM_CS, IDT_TYPE_CALL, 3, 0)
    }

    pub const fn no_handler() -> Self {
        IdtEntry { low: 0, high: 0 }
    }
}

const IDT_ENTRIES: usize = 256;

#[repr(C, packed)]
#[derive(Default, Clone, Copy, Debug)]
struct IdtDesc {
    size: u16,
    address: VirtAddr,
}

#[derive(Copy, Clone, Debug)]
pub struct IDT {
    entries: [IdtEntry; IDT_ENTRIES],
}

impl IDT {
    pub const fn new() -> Self {
        IDT {
            entries: [IdtEntry::no_handler(); IDT_ENTRIES],
        }
    }

    pub fn init(&mut self, handler_array: *const u8, size: usize) -> &mut Self {
        // Set IDT handlers
        let handlers = VirtAddr::from(handler_array);

        for idx in 0..size {
            self.set_entry(idx, IdtEntry::raw_entry(handlers + (32 * idx)));
        }

        self
    }

    pub fn set_entry(&mut self, idx: usize, entry: IdtEntry) -> &mut Self {
        self.entries[idx] = entry;

        self
    }
}

impl Default for IDT {
    fn default() -> Self {
        Self::new()
    }
}

impl WriteLockGuard<'static, IDT> {
    /// Load an IDT. Its lifetime must be static so that its entries are
    /// always available to the CPU.
    pub fn load(&self) {
        let desc: IdtDesc = IdtDesc {
            size: (IDT_ENTRIES * 16) as u16,
            address: VirtAddr::from(self.entries.as_ptr()),
        };

        unsafe {
            asm!("lidt (%rax)", in("rax") &desc, options(att_syntax));
        }
    }
}

static IDT: RWLock<IDT> = RWLock::new(IDT::new());

pub fn idt_mut() -> WriteLockGuard<'static, IDT> {
    IDT.lock_write()
}

global_asm!(
    r#"
        /* Needed by the stack unwinder to recognize exception frames. */
        .globl generic_idt_handler_return
    generic_idt_handler_return:

        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %r11
        popq    %r10
        popq    %r9
        popq    %r8
        popq    %rbp
        popq    %rdi
        popq    %rsi
        popq    %rdx
        popq    %rcx
        popq    %rbx
        popq    %rax

        addq    $8, %rsp /* Skip error code */

        iretq
        "#,
    options(att_syntax)
);

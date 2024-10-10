// SPDX-License-Identifier: MIT
//
// Copyright (c) 2024 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use core::arch::asm;

/// Unconditionally disable IRQs
///
/// # Safety
///
/// Callers need to take care of re-enabling IRQs.
#[inline(always)]
pub unsafe fn raw_irqs_disable() {
    asm!("cli", options(att_syntax, preserves_flags, nomem));
}

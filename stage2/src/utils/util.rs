// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use core::arch::asm;
use core::ops::{BitAnd, Sub};

pub fn is_aligned<T>(addr: T, align: T) -> bool
where
    T: Sub<Output = T> + BitAnd<Output = T> + PartialEq + From<u32>,
{
    (addr & (align - T::from(1))) == T::from(0)
}

pub fn halt() {
    unsafe {
        asm!("hlt", options(att_syntax));
    }
}

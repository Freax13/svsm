// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::locking::{RWLock, ReadLockGuard, WriteLockGuard};
use cpuarch::gdt::GDT;

static GDT: RWLock<GDT> = RWLock::new(GDT::new());

pub fn gdt() -> ReadLockGuard<'static, GDT> {
    GDT.lock_read()
}

pub fn gdt_mut() -> WriteLockGuard<'static, GDT> {
    GDT.lock_write()
}

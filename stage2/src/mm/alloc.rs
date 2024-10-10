// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::address::{Address, VirtAddr};
use crate::error::SvsmError;
use crate::locking::SpinLock;
use crate::types::PAGE_SIZE;
use core::alloc::Layout;

struct BumpAllocatorState {
    start: VirtAddr,
    current: VirtAddr,
    end: VirtAddr,
}

impl BumpAllocatorState {
    const DEFAULT: Self = Self {
        start: VirtAddr::null(),
        current: VirtAddr::null(),
        end: VirtAddr::null(),
    };
}

static STATE: SpinLock<BumpAllocatorState> = SpinLock::new(BumpAllocatorState::DEFAULT);

/// Initializes the root memory region with the specified virtual start and end
/// addresses.
pub fn root_mem_init(vstart: VirtAddr, vend: VirtAddr) {
    let mut guard = STATE.lock();
    guard.start = vstart;
    guard.current = vstart;
    guard.end = vend;
}

pub fn allocate(layout: Layout) -> Result<VirtAddr, SvsmError> {
    let mut guard = STATE.lock();
    let current = guard.current.align_up(layout.align());
    let new_current = current.const_add(layout.size());
    if new_current > guard.end {
        return Err(SvsmError::Mem);
    }
    guard.current = new_current;
    Ok(current)
}

pub fn allocate_zeroed(layout: Layout) -> Result<VirtAddr, SvsmError> {
    let addr = allocate(layout)?;
    unsafe {
        core::ptr::write_bytes(addr.as_mut_ptr::<u8>(), 0, layout.size());
    }
    Ok(addr)
}

pub fn allocate_page_zeroed() -> Result<VirtAddr, SvsmError> {
    allocate_zeroed(Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap())
}

pub fn free_page(addr: VirtAddr) {
    // For a bump allocator, freeing is a no-op.
    let _ = addr;
}

/// Prints memory information.
pub fn print_memory_info() {
    let guard = STATE.lock();
    let total_mem = guard.end - guard.start;
    let free_mem = guard.end - guard.current;
    drop(guard);

    log::info!(
        "Total memory: {}KiB free memory: {}KiB",
        total_mem / 1024,
        free_mem / 1024
    );
}

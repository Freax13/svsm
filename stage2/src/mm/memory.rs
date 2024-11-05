// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

extern crate alloc;

use crate::address::{Address, PhysAddr};
use crate::cpu::percpu::PERCPU_VMSAS;
use crate::locking::RWLock;
use crate::utils::MemoryRegion;
use alloc::vec::Vec;

use super::pagetable::LAUNCH_VMSA_ADDR;

/// Global memory map containing various memory regions.
static MEMORY_MAP: RWLock<Vec<MemoryRegion<PhysAddr>>> = RWLock::new(Vec::new());

/// Returns `true` if the provided physical address `paddr` is valid, i.e.
/// it is within the configured memory regions, otherwise returns `false`.
pub fn valid_phys_address(paddr: PhysAddr) -> bool {
    let page_addr = paddr.page_align();

    if PERCPU_VMSAS.exists(page_addr) {
        return false;
    }
    if page_addr == LAUNCH_VMSA_ADDR {
        return false;
    }

    MEMORY_MAP
        .lock_read()
        .iter()
        .any(|region| region.contains(paddr))
}

/// The starting address of the ISA range.
const ISA_RANGE_START: PhysAddr = PhysAddr::new(0xa0000);

/// The ending address of the ISA range.
const ISA_RANGE_END: PhysAddr = PhysAddr::new(0x100000);

/// Returns `true` if the provided physical address `paddr` is writable,
/// otherwise returns `false`.
pub fn writable_phys_addr(paddr: PhysAddr) -> bool {
    // The ISA range is not writable
    if paddr >= ISA_RANGE_START && paddr < ISA_RANGE_END {
        return false;
    }

    valid_phys_address(paddr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg_attr(test_in_svsm, ignore = "Offline testing")]
    fn test_valid_phys_address() {
        let start = PhysAddr::new(0x1000);
        let end = PhysAddr::new(0x2000);
        let region = MemoryRegion::from_addresses(start, end);

        MEMORY_MAP.lock_write().push(region);

        // Inside the region
        assert!(valid_phys_address(PhysAddr::new(0x1500)));
        // Outside the region
        assert!(!valid_phys_address(PhysAddr::new(0x3000)));
    }
}

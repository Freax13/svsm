// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::address::{PhysAddr, VirtAddr};
use crate::utils::immut_after_init::ImmutAfterInitCell;

#[cfg(target_os = "none")]
use crate::mm::pagetable::PageTable;

#[derive(Debug, Copy, Clone)]
#[allow(dead_code)]
pub struct FixedAddressMappingRange {
    virt_start: VirtAddr,
    virt_end: VirtAddr,
    phys_start: PhysAddr,
}

impl FixedAddressMappingRange {
    pub fn new(virt_start: VirtAddr, virt_end: VirtAddr, phys_start: PhysAddr) -> Self {
        Self {
            virt_start,
            virt_end,
            phys_start,
        }
    }

    #[cfg(target_os = "none")]
    fn phys_to_virt(&self, paddr: PhysAddr) -> Option<VirtAddr> {
        if paddr < self.phys_start {
            None
        } else {
            let size: usize = self.virt_end - self.virt_start;
            if paddr >= self.phys_start + size {
                None
            } else {
                let offset: usize = paddr - self.phys_start;
                Some(self.virt_start + offset)
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
#[cfg_attr(not(target_os = "none"), allow(dead_code))]
pub struct FixedAddressMapping {
    kernel_mapping: FixedAddressMappingRange,
    heap_mapping: Option<FixedAddressMappingRange>,
}

static FIXED_MAPPING: ImmutAfterInitCell<FixedAddressMapping> = ImmutAfterInitCell::uninit();

pub fn init_kernel_mapping_info(
    kernel_mapping: FixedAddressMappingRange,
    heap_mapping: Option<FixedAddressMappingRange>,
) {
    let mapping = FixedAddressMapping {
        kernel_mapping,
        heap_mapping,
    };
    FIXED_MAPPING
        .init(&mapping)
        .expect("Already initialized fixed mapping info");
}

#[cfg(target_os = "none")]
pub fn virt_to_phys(vaddr: VirtAddr) -> PhysAddr {
    match PageTable::virt_to_phys(vaddr) {
        Some(paddr) => paddr,
        None => {
            panic!("Invalid virtual address {:#018x}", vaddr);
        }
    }
}

#[cfg(target_os = "none")]
pub fn phys_to_virt(paddr: PhysAddr) -> VirtAddr {
    if let Some(addr) = FIXED_MAPPING.kernel_mapping.phys_to_virt(paddr) {
        return addr;
    }
    if let Some(ref mapping) = FIXED_MAPPING.heap_mapping {
        if let Some(addr) = mapping.phys_to_virt(paddr) {
            return addr;
        }
    }

    panic!("Invalid physical address {:#018x}", paddr);
}

#[cfg(not(target_os = "none"))]
pub fn virt_to_phys(vaddr: VirtAddr) -> PhysAddr {
    use crate::address::Address;
    PhysAddr::from(vaddr.bits())
}

#[cfg(not(target_os = "none"))]
pub fn phys_to_virt(paddr: PhysAddr) -> VirtAddr {
    use crate::address::Address;
    VirtAddr::from(paddr.bits())
}

const fn virt_from_idx(idx: usize) -> VirtAddr {
    VirtAddr::new(idx << ((3 * 9) + 12))
}

/// Page table self-map level 3 index
pub const PGTABLE_LVL3_IDX_PTE_SELFMAP: usize = 493;

pub const SVSM_PTE_BASE: VirtAddr = virt_from_idx(PGTABLE_LVL3_IDX_PTE_SELFMAP);

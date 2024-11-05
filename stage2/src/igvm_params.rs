// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Jon Lange (jlange@microsoft.com)

use crate::address::{PhysAddr, VirtAddr};
use crate::error::SvsmError;
use crate::mm::PAGE_SIZE;
use crate::utils::MemoryRegion;

use bootlib::igvm_params::{IgvmGuestContext, IgvmParamBlock, IgvmParamPage};
use core::mem::size_of;
use igvm_defs::{IgvmEnvironmentInfo, IGVM_VHS_MEMORY_MAP_ENTRY};

const IGVM_MEMORY_ENTRIES_PER_PAGE: usize = PAGE_SIZE / size_of::<IGVM_VHS_MEMORY_MAP_ENTRY>();

#[derive(Clone, Debug)]
#[repr(C, align(64))]
pub struct IgvmMemoryMap {
    memory_map: [IGVM_VHS_MEMORY_MAP_ENTRY; IGVM_MEMORY_ENTRIES_PER_PAGE],
}

#[derive(Clone, Debug)]
pub struct IgvmParams<'a> {
    igvm_param_block: &'a IgvmParamBlock,
    igvm_param_page: &'a IgvmParamPage,
    igvm_memory_map: &'a IgvmMemoryMap,
    igvm_guest_context: Option<&'a IgvmGuestContext>,
}

impl IgvmParams<'_> {
    pub fn new(addr: VirtAddr) -> Result<Self, SvsmError> {
        let param_block = Self::try_aligned_ref::<IgvmParamBlock>(addr)?;
        let param_page_address = addr + param_block.param_page_offset as usize;
        let param_page = Self::try_aligned_ref::<IgvmParamPage>(param_page_address)?;
        let memory_map_address = addr + param_block.memory_map_offset as usize;
        let memory_map = Self::try_aligned_ref::<IgvmMemoryMap>(memory_map_address)?;
        let guest_context = if param_block.guest_context_offset != 0 {
            let offset = usize::try_from(param_block.guest_context_offset).unwrap();
            Some(Self::try_aligned_ref::<IgvmGuestContext>(addr + offset)?)
        } else {
            None
        };

        Ok(Self {
            igvm_param_block: param_block,
            igvm_param_page: param_page,
            igvm_memory_map: memory_map,
            igvm_guest_context: guest_context,
        })
    }

    fn try_aligned_ref<'a, T>(addr: VirtAddr) -> Result<&'a T, SvsmError> {
        // SAFETY: we trust the caller to provide an address pointing to valid
        // memory which is not mutably aliased.
        unsafe { addr.aligned_ref::<T>().ok_or(SvsmError::Firmware) }
    }

    pub fn size(&self) -> usize {
        // Calculate the total size of the parameter area.  The
        // parameter area always begins at the kernel base
        // address.
        self.igvm_param_block.param_area_size.try_into().unwrap()
    }

    pub fn find_kernel_region(&self) -> Result<MemoryRegion<PhysAddr>, SvsmError> {
        let kernel_base = PhysAddr::from(self.igvm_param_block.kernel_base);
        let kernel_size: usize = self.igvm_param_block.kernel_size.try_into().unwrap();
        Ok(MemoryRegion::<PhysAddr>::new(kernel_base, kernel_size))
    }

    pub fn reserved_kernel_area_size(&self) -> usize {
        self.igvm_param_block
            .kernel_reserved_size
            .try_into()
            .unwrap()
    }

    pub fn page_state_change_required(&self) -> bool {
        let environment_info = IgvmEnvironmentInfo::from(self.igvm_param_page.environment_info);
        environment_info.memory_is_shared()
    }

    pub fn debug_serial_port(&self) -> u16 {
        self.igvm_param_block.debug_serial_port
    }

    pub fn use_alternate_injection(&self) -> bool {
        self.igvm_param_block.use_alternate_injection != 0
    }
}

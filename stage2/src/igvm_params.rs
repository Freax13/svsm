// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Jon Lange (jlange@microsoft.com)

use crate::address::{PhysAddr, VirtAddr};
use crate::error::SvsmError;
use crate::utils::MemoryRegion;

use bootlib::igvm_params::{IgvmParamBlock, IgvmParamPage};
use igvm_defs::IgvmEnvironmentInfo;

#[derive(Clone, Debug)]
pub struct IgvmParams<'a> {
    igvm_param_block: &'a IgvmParamBlock,
    igvm_param_page: &'a IgvmParamPage,
}

impl IgvmParams<'_> {
    pub fn new(addr: VirtAddr) -> Result<Self, SvsmError> {
        let param_block = Self::try_aligned_ref::<IgvmParamBlock>(addr)?;
        let param_page_address = addr + param_block.param_page_offset as usize;
        let param_page = Self::try_aligned_ref::<IgvmParamPage>(param_page_address)?;

        Ok(Self {
            igvm_param_block: param_block,
            igvm_param_page: param_page,
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

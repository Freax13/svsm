// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Jon Lange (jlange@microsoft.com)

use crate::address::PhysAddr;
use crate::error::SvsmError;
use crate::fw_cfg::FwCfg;
use crate::igvm_params::IgvmParams;
use crate::serial::SERIAL_PORT;
use crate::utils::MemoryRegion;

#[derive(Debug)]
pub enum SvsmConfig<'a> {
    FirmwareConfig(FwCfg<'a>),
    IgvmConfig(IgvmParams<'a>),
}

impl SvsmConfig<'_> {
    pub fn find_kernel_region(&self) -> Result<MemoryRegion<PhysAddr>, SvsmError> {
        match self {
            SvsmConfig::FirmwareConfig(fw_cfg) => fw_cfg.find_kernel_region(),
            SvsmConfig::IgvmConfig(igvm_params) => igvm_params.find_kernel_region(),
        }
    }
    pub fn page_state_change_required(&self) -> bool {
        match self {
            SvsmConfig::FirmwareConfig(_) => true,
            SvsmConfig::IgvmConfig(igvm_params) => igvm_params.page_state_change_required(),
        }
    }
    pub fn reserved_kernel_area_size(&self) -> usize {
        match self {
            SvsmConfig::FirmwareConfig(_) => 0,
            SvsmConfig::IgvmConfig(igvm_params) => igvm_params.reserved_kernel_area_size(),
        }
    }

    pub fn debug_serial_port(&self) -> u16 {
        match self {
            SvsmConfig::FirmwareConfig(_) => SERIAL_PORT,
            SvsmConfig::IgvmConfig(igvm_params) => igvm_params.debug_serial_port(),
        }
    }

    pub fn use_alternate_injection(&self) -> bool {
        match self {
            SvsmConfig::FirmwareConfig(_) => false,
            SvsmConfig::IgvmConfig(igvm_params) => igvm_params.use_alternate_injection(),
        }
    }
}

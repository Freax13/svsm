// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Jon Lange <jlange@microsoft.com>

use crate::address::{PhysAddr, VirtAddr};
use crate::error::SvsmError;
use crate::io::IOPort;
use crate::platform::native::NativePlatform;
use crate::platform::snp::SnpPlatform;
use crate::platform::tdp::TdpPlatform;
use crate::types::PageSize;
use crate::utils::MemoryRegion;

use bootlib::platform::SvsmPlatformType;

pub mod native;
pub mod snp;
pub mod tdp;

#[derive(Clone, Copy, Debug)]
pub struct PageEncryptionMasks {
    pub private_pte_mask: usize,
    pub shared_pte_mask: usize,
    pub addr_mask_width: u32,
    pub phys_addr_sizes: u32,
}

#[derive(Debug, Clone, Copy)]
pub enum PageStateChangeOp {
    Private,
    Shared,
    Psmash,
    Unsmash,
}

#[derive(Debug, Clone, Copy)]
pub enum PageValidateOp {
    Validate,
    Invalidate,
}

/// This defines a platform abstraction to permit the SVSM to run on different
/// underlying architectures.
pub trait SvsmPlatform {
    /// Performs basic early initialization of the runtime environment.
    fn env_setup(&mut self, debug_serial_port: u16, vtom: usize) -> Result<(), SvsmError>;

    /// Performs initialization of the platform runtime environment after
    /// the core system environment has been initialized.
    fn env_setup_late(&mut self, debug_serial_port: u16) -> Result<(), SvsmError>;

    /// Determines the paging encryption masks for the current architecture.
    fn get_page_encryption_masks(&self) -> PageEncryptionMasks;

    /// Establishes state required for guest/host communication.
    fn setup_guest_host_comm(&mut self, is_bsp: bool);

    /// Obtains a reference to an I/O port implemetation appropriate to the
    /// platform.
    fn get_io_port(&self) -> &'static dyn IOPort;

    /// Performs a page state change between private and shared states.
    fn page_state_change(
        &self,
        region: MemoryRegion<PhysAddr>,
        size: PageSize,
        op: PageStateChangeOp,
    ) -> Result<(), SvsmError>;

    /// Marks a virtual range of pages as valid or invalid for use as private
    /// pages.  Provided primarily for use in stage2 where validation by
    /// physical address cannot e supported.
    fn validate_virtual_page_range(
        &self,
        region: MemoryRegion<VirtAddr>,
        op: PageValidateOp,
    ) -> Result<(), SvsmError>;
}

//FIXME - remove Copy trait
#[derive(Clone, Copy, Debug)]
pub enum SvsmPlatformCell {
    Snp(SnpPlatform),
    Tdp(TdpPlatform),
    Native(NativePlatform),
}

impl SvsmPlatformCell {
    pub fn new(platform_type: SvsmPlatformType) -> Self {
        match platform_type {
            SvsmPlatformType::Native => SvsmPlatformCell::Native(NativePlatform::new()),
            SvsmPlatformType::Snp => SvsmPlatformCell::Snp(SnpPlatform::new()),
            SvsmPlatformType::Tdp => SvsmPlatformCell::Tdp(TdpPlatform::new()),
        }
    }

    pub fn as_dyn_ref(&self) -> &dyn SvsmPlatform {
        match self {
            SvsmPlatformCell::Native(platform) => platform,
            SvsmPlatformCell::Snp(platform) => platform,
            SvsmPlatformCell::Tdp(platform) => platform,
        }
    }

    pub fn as_mut_dyn_ref(&mut self) -> &mut dyn SvsmPlatform {
        match self {
            SvsmPlatformCell::Native(platform) => platform,
            SvsmPlatformCell::Snp(platform) => platform,
            SvsmPlatformCell::Tdp(platform) => platform,
        }
    }
}

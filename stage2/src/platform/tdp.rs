// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (C) 2024 Intel Corporation
//
// Author: Peter Fang <peter.fang@intel.com>

use crate::console::init_svsm_console;
use crate::error::SvsmError;
use crate::io::IOPort;
use crate::mm::virt_to_frame;
use crate::platform::{PageEncryptionMasks, PageStateChangeOp, PageValidateOp, SvsmPlatform};
use crate::types::PageSize;
use crate::utils::immut_after_init::ImmutAfterInitCell;
use crate::utils::MemoryRegion;
use cpuarch::address::{PhysAddr, VirtAddr};
use cpuarch::cpuid::CpuidResult;
use tdx_tdcall::tdx::{
    td_accept_memory, tdvmcall_halt, tdvmcall_io_read_16, tdvmcall_io_read_32, tdvmcall_io_read_8,
    tdvmcall_io_write_16, tdvmcall_io_write_32, tdvmcall_io_write_8,
};

static GHCI_IO_DRIVER: GHCIIOPort = GHCIIOPort::new();
static VTOM: ImmutAfterInitCell<usize> = ImmutAfterInitCell::uninit();

#[derive(Clone, Copy, Debug)]
pub struct TdpPlatform {}

impl TdpPlatform {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for TdpPlatform {
    fn default() -> Self {
        Self::new()
    }
}

impl SvsmPlatform for TdpPlatform {
    fn halt() {
        tdvmcall_halt();
    }

    fn env_setup(&mut self, debug_serial_port: u16, vtom: usize) -> Result<(), SvsmError> {
        VTOM.init(&vtom).map_err(|_| SvsmError::PlatformInit)?;
        // Serial console device can be initialized immediately
        init_svsm_console(&GHCI_IO_DRIVER, debug_serial_port)
    }

    fn env_setup_late(&mut self, _debug_serial_port: u16) -> Result<(), SvsmError> {
        Ok(())
    }

    fn get_page_encryption_masks(&self) -> PageEncryptionMasks {
        // Find physical address size.
        let res = CpuidResult::get(0x80000008, 0);
        let vtom = *VTOM;
        PageEncryptionMasks {
            private_pte_mask: 0,
            shared_pte_mask: vtom,
            addr_mask_width: vtom.trailing_zeros(),
            phys_addr_sizes: res.eax,
        }
    }

    fn setup_guest_host_comm(&mut self, _is_bsp: bool) {}

    fn get_io_port(&self) -> &'static dyn IOPort {
        &GHCI_IO_DRIVER
    }

    fn page_state_change(
        &self,
        _region: MemoryRegion<PhysAddr>,
        _size: PageSize,
        _op: PageStateChangeOp,
    ) -> Result<(), SvsmError> {
        Err(SvsmError::Tdx)
    }

    fn validate_virtual_page_range(
        &self,
        region: MemoryRegion<VirtAddr>,
        op: PageValidateOp,
    ) -> Result<(), SvsmError> {
        match op {
            PageValidateOp::Validate => {
                let mut va = region.start();
                while va < region.end() {
                    let pa = virt_to_frame(va);
                    let sz = pa.end() - pa.address();
                    // td_accept_memory() will take care of alignment
                    td_accept_memory(pa.address().into(), sz.try_into().unwrap());
                    va = va + sz;
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct GHCIIOPort {}

impl GHCIIOPort {
    pub const fn new() -> Self {
        GHCIIOPort {}
    }
}

impl IOPort for GHCIIOPort {
    fn outb(&self, port: u16, value: u8) {
        tdvmcall_io_write_8(port, value);
    }

    fn inb(&self, port: u16) -> u8 {
        tdvmcall_io_read_8(port)
    }

    fn outw(&self, port: u16, value: u16) {
        tdvmcall_io_write_16(port, value);
    }

    fn inw(&self, port: u16) -> u16 {
        tdvmcall_io_read_16(port)
    }

    fn outl(&self, port: u16, value: u32) {
        tdvmcall_io_write_32(port, value);
    }

    fn inl(&self, port: u16) -> u32 {
        tdvmcall_io_read_32(port)
    }
}

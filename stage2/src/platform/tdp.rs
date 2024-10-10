// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (C) 2024 Intel Corporation
//
// Author: Peter Fang <peter.fang@intel.com>

use crate::address::{PhysAddr, VirtAddr};
use crate::console::init_console;
use crate::cpu::cpuid::CpuidResult;
use crate::error::SvsmError;
use crate::io::IOPort;
use crate::platform::{PageEncryptionMasks, PageStateChangeOp, PageValidateOp, SvsmPlatform};
use crate::serial::SerialPort;
use crate::svsm_console::SVSMIOPort;
use crate::types::PageSize;
use crate::utils::immut_after_init::ImmutAfterInitCell;
use crate::utils::MemoryRegion;

// FIXME - SVSMIOPort doesn't work on TDP, but the platform does not yet have
// an alternative available.
static CONSOLE_IO: SVSMIOPort = SVSMIOPort::new();
static CONSOLE_SERIAL: ImmutAfterInitCell<SerialPort<'_>> = ImmutAfterInitCell::uninit();

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
    fn env_setup(&mut self, _debug_serial_port: u16, vtom: usize) -> Result<(), SvsmError> {
        VTOM.init(&vtom).map_err(|_| SvsmError::PlatformInit)
    }

    fn env_setup_late(&mut self, debug_serial_port: u16) -> Result<(), SvsmError> {
        CONSOLE_SERIAL
            .init(&SerialPort::new(&CONSOLE_IO, debug_serial_port))
            .map_err(|_| SvsmError::Console)?;
        (*CONSOLE_SERIAL).init();
        init_console(&*CONSOLE_SERIAL).map_err(|_| SvsmError::Console)
    }

    fn get_page_encryption_masks(&self) -> PageEncryptionMasks {
        // Find physical address size.
        let res = CpuidResult::get(0x80000008, 0);
        let vtom = *VTOM;
        PageEncryptionMasks {
            private_pte_mask: 0,
            shared_pte_mask: vtom,
            addr_mask_width: vtom.trailing_zeros(),
            phys_addr_sizes: res.eax & 0xff,
        }
    }

    fn setup_guest_host_comm(&mut self, _is_bsp: bool) {}

    fn get_io_port(&self) -> &'static dyn IOPort {
        &CONSOLE_IO
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
        _region: MemoryRegion<VirtAddr>,
        _op: PageValidateOp,
    ) -> Result<(), SvsmError> {
        Err(SvsmError::Tdx)
    }
}

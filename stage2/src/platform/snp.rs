// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Jon Lange <jlange@microsoft.com>

use crate::address::{PhysAddr, VirtAddr};
use crate::console::init_console;
use crate::cpu::cpuid::cpuid_table;
use crate::cpu::percpu::{current_ghcb, register_ghcb, setup_ghcb};
use crate::error::SvsmError;
use crate::io::IOPort;
use crate::platform::{PageEncryptionMasks, PageStateChangeOp, PageValidateOp, SvsmPlatform};
use crate::serial::SerialPort;
use crate::sev::msr_protocol::verify_ghcb_version;
use crate::sev::status::vtom_enabled;
use crate::sev::{pvalidate_range, sev_status_init, sev_status_verify, PvalidateOp};
use crate::svsm_console::SVSMIOPort;
use crate::types::PageSize;
use crate::utils::immut_after_init::ImmutAfterInitCell;
use crate::utils::MemoryRegion;

#[cfg(debug_assertions)]
use crate::mm::virt_to_phys;

static CONSOLE_IO: SVSMIOPort = SVSMIOPort::new();
static CONSOLE_SERIAL: ImmutAfterInitCell<SerialPort<'_>> = ImmutAfterInitCell::uninit();

static VTOM: ImmutAfterInitCell<usize> = ImmutAfterInitCell::uninit();

impl From<PageValidateOp> for PvalidateOp {
    fn from(op: PageValidateOp) -> PvalidateOp {
        match op {
            PageValidateOp::Validate => PvalidateOp::Valid,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SnpPlatform {}

impl SnpPlatform {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for SnpPlatform {
    fn default() -> Self {
        Self::new()
    }
}

impl SvsmPlatform for SnpPlatform {
    fn env_setup(&mut self, _debug_serial_port: u16, vtom: usize) -> Result<(), SvsmError> {
        sev_status_init();
        VTOM.init(&vtom).map_err(|_| SvsmError::PlatformInit)?;
        Ok(())
    }

    fn env_setup_late(&mut self, debug_serial_port: u16) -> Result<(), SvsmError> {
        CONSOLE_SERIAL
            .init(&SerialPort::new(&CONSOLE_IO, debug_serial_port))
            .map_err(|_| SvsmError::Console)?;
        (*CONSOLE_SERIAL).init();
        init_console(&*CONSOLE_SERIAL).map_err(|_| SvsmError::Console)?;
        sev_status_verify();
        Ok(())
    }

    fn get_page_encryption_masks(&self) -> PageEncryptionMasks {
        // Find physical address size.
        let processor_capacity =
            cpuid_table(0x80000008).expect("Can not get physical address size from CPUID table");
        if vtom_enabled() {
            let vtom = *VTOM;
            PageEncryptionMasks {
                private_pte_mask: 0,
                shared_pte_mask: vtom,
                addr_mask_width: vtom.leading_zeros(),
                phys_addr_sizes: processor_capacity.eax,
            }
        } else {
            // Find C-bit position.
            let sev_capabilities =
                cpuid_table(0x8000001f).expect("Can not get C-Bit position from CPUID table");
            let c_bit = sev_capabilities.ebx & 0x3f;
            PageEncryptionMasks {
                private_pte_mask: 1 << c_bit,
                shared_pte_mask: 0,
                addr_mask_width: c_bit,
                phys_addr_sizes: processor_capacity.eax,
            }
        }
    }

    fn setup_guest_host_comm(&mut self, is_bsp: bool) {
        if is_bsp {
            verify_ghcb_version();
        }

        setup_ghcb().unwrap_or_else(|_| {
            if is_bsp {
                panic!("Failed to setup BSP GHCB");
            } else {
                panic!("Failed to setup AP GHCB");
            }
        });
        register_ghcb().expect("Failed to register GHCB");
    }

    fn get_io_port(&self) -> &'static dyn IOPort {
        &CONSOLE_IO
    }

    fn page_state_change(
        &self,
        region: MemoryRegion<PhysAddr>,
        size: PageSize,
        op: PageStateChangeOp,
    ) -> Result<(), SvsmError> {
        current_ghcb().page_state_change(region, size, op)
    }

    fn validate_virtual_page_range(
        &self,
        region: MemoryRegion<VirtAddr>,
        op: PageValidateOp,
    ) -> Result<(), SvsmError> {
        #[cfg(debug_assertions)]
        {
            // Ensure that it is possible to translate this virtual address to
            // a physical address.  This is not necessary for correctness
            // here, but since other platformss may rely on virtual-to-physical
            // translation, it is helpful to force a translation here for
            // debugging purposes just to help catch potential errors when
            // testing on SNP.
            for va in region.iter_pages(PageSize::Regular) {
                let _ = virt_to_phys(va);
            }
        }
        pvalidate_range(region, PvalidateOp::from(op))
    }
}

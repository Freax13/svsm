// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Jon Lange <jlange@microsoft.com>

use crate::address::{PhysAddr, VirtAddr};
use crate::console::init_svsm_console;
use crate::cpu::cpuid::{cpuid_table, CpuidResult};
use crate::cpu::percpu::{current_ghcb, PerCpu};
use crate::error::SvsmError;
use crate::io::IOPort;
use crate::platform::{PageEncryptionMasks, PageStateChangeOp, PageValidateOp, SvsmPlatform};
use crate::sev::ghcb::GHCBIOSize;
use crate::sev::msr_protocol::{request_termination_msr, verify_ghcb_version};
use crate::sev::status::{sev_restricted_injection, vtom_enabled};
use crate::sev::{
    init_hypervisor_ghcb_features, pvalidate_range, sev_status_init, sev_status_verify, PvalidateOp,
};
use crate::types::PageSize;
use crate::utils::immut_after_init::ImmutAfterInitCell;
use crate::utils::MemoryRegion;

#[cfg(debug_assertions)]
use crate::mm::virt_to_phys;

static GHCB_IO_DRIVER: GHCBIOPort = GHCBIOPort::new();

static VTOM: ImmutAfterInitCell<usize> = ImmutAfterInitCell::uninit();

impl From<PageValidateOp> for PvalidateOp {
    fn from(op: PageValidateOp) -> PvalidateOp {
        match op {
            PageValidateOp::Validate => PvalidateOp::Valid,
            PageValidateOp::Invalidate => PvalidateOp::Invalid,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SnpPlatform {
    can_use_interrupts: bool,
}

impl SnpPlatform {
    pub fn new() -> Self {
        Self {
            can_use_interrupts: false,
        }
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

        // Now that SEV status is initialized, determine whether this platform
        // supports the use of SVSM interrupts.  SVSM interrupts are supported
        // if this system uses restricted injection.
        if sev_restricted_injection() {
            self.can_use_interrupts = true;
        }

        Ok(())
    }

    fn env_setup_late(&mut self, debug_serial_port: u16) -> Result<(), SvsmError> {
        init_svsm_console(&GHCB_IO_DRIVER, debug_serial_port)?;
        sev_status_verify();
        init_hypervisor_ghcb_features()?;
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

    fn setup_guest_host_comm(&mut self, cpu: &PerCpu, is_bsp: bool) {
        if is_bsp {
            verify_ghcb_version();
        }

        cpu.setup_ghcb().unwrap_or_else(|_| {
            if is_bsp {
                panic!("Failed to setup BSP GHCB");
            } else {
                panic!("Failed to setup AP GHCB");
            }
        });
        cpu.register_ghcb().expect("Failed to register GHCB");
    }

    fn get_io_port(&self) -> &'static dyn IOPort {
        &GHCB_IO_DRIVER
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

#[derive(Clone, Copy, Debug, Default)]
pub struct GHCBIOPort {}

impl GHCBIOPort {
    pub const fn new() -> Self {
        GHCBIOPort {}
    }
}

impl IOPort for GHCBIOPort {
    fn outb(&self, port: u16, value: u8) {
        let ret = current_ghcb().ioio_out(port, GHCBIOSize::Size8, value as u64);
        if ret.is_err() {
            request_termination_msr();
        }
    }

    fn inb(&self, port: u16) -> u8 {
        let ret = current_ghcb().ioio_in(port, GHCBIOSize::Size8);
        match ret {
            Ok(v) => (v & 0xff) as u8,
            Err(_e) => request_termination_msr(),
        }
    }

    fn outw(&self, port: u16, value: u16) {
        let ret = current_ghcb().ioio_out(port, GHCBIOSize::Size16, value as u64);
        if ret.is_err() {
            request_termination_msr();
        }
    }

    fn inw(&self, port: u16) -> u16 {
        let ret = current_ghcb().ioio_in(port, GHCBIOSize::Size16);
        match ret {
            Ok(v) => (v & 0xffff) as u16,
            Err(_e) => request_termination_msr(),
        }
    }

    fn outl(&self, port: u16, value: u32) {
        let ret = current_ghcb().ioio_out(port, GHCBIOSize::Size32, value as u64);
        if ret.is_err() {
            request_termination_msr();
        }
    }

    fn inl(&self, port: u16) -> u32 {
        let ret = current_ghcb().ioio_in(port, GHCBIOSize::Size32);
        match ret {
            Ok(v) => (v & 0xffffffff) as u32,
            Err(_e) => request_termination_msr(),
        }
    }
}

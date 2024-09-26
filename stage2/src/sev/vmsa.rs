// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use super::utils::{rmp_adjust, RMPFlags};
use crate::address::{Address, PhysAddr, VirtAddr};
use crate::error::SvsmError;
use crate::mm::{virt_to_phys, PageBox};
use crate::types::{PageSize, PAGE_SIZE_2M};
use core::mem::{size_of, ManuallyDrop};
use core::ops::{Deref, DerefMut};
use core::ptr;

use cpuarch::vmsa::VMSA;

pub const VMPL_MAX: usize = 4;

/// An allocated page containing a VMSA structure.
#[derive(Debug)]
pub struct VmsaPage {
    page: PageBox<[VMSA; 2]>,
    idx: usize,
}

impl VmsaPage {
    /// Allocates a new VMSA for the given VPML.
    pub fn new(vmpl: RMPFlags) -> Result<Self, SvsmError> {
        assert!(vmpl.bits() < (VMPL_MAX as u64));

        let page = PageBox::try_new_zeroed()?;
        // Make sure the VMSA page is not 2M-aligned, as some hardware
        // generations can't handle this properly. To ensure this property, we
        // allocate 2 VMSAs and choose whichever is not 2M-aligned.
        let idx = if page.vaddr().is_aligned(PAGE_SIZE_2M) {
            1
        } else {
            0
        };

        let vaddr = page.vaddr() + idx * size_of::<VMSA>();
        rmp_adjust(vaddr, RMPFlags::VMSA | vmpl, PageSize::Regular)?;
        // SAFETY: all zeros is a valid representation for the VMSA.
        let page = unsafe { page.assume_init() };
        Ok(Self { page, idx })
    }

    /// Returns the virtual address fro this VMSA.
    #[inline]
    fn vaddr(&self) -> VirtAddr {
        let ptr: *const VMSA = ptr::from_ref(&self.page[self.idx]);
        VirtAddr::from(ptr)
    }

    /// Returns the physical address for this VMSA.
    #[inline]
    pub fn paddr(&self) -> PhysAddr {
        virt_to_phys(self.vaddr())
    }

    /// Leaks the allocation for this VMSA, ensuring it never gets freed.
    pub fn leak(self) -> &'static mut VMSA {
        let mut vmsa = ManuallyDrop::new(self);
        // SAFETY: `self.idx` is either 0 or 1, so this will never overflow
        let ptr = unsafe { ptr::from_mut(&mut vmsa).add(vmsa.idx) };
        // SAFETY: this pointer will never be freed because of ManuallyDrop,
        // so we can create a static mutable reference. We go through a raw
        // pointer to promote the lifetime to static.
        unsafe { &mut *ptr }
    }
}

impl Drop for VmsaPage {
    fn drop(&mut self) {
        rmp_adjust(
            self.vaddr(),
            RMPFlags::RWX | RMPFlags::VMPL0,
            PageSize::Regular,
        )
        .expect("Failed to RMPADJUST VMSA page");
    }
}

impl Deref for VmsaPage {
    type Target = VMSA;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.page[self.idx]
    }
}

impl DerefMut for VmsaPage {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.page[self.idx]
    }
}

// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this
// TODO: FIx this

extern crate alloc;

use crate::address::VirtAddr;
use crate::error::SvsmError;
use crate::locking::{LockGuard, SpinLock};
use crate::mm::pagetable::{PTEntryFlags, PageTable};
use crate::mm::{virt_to_phys, PageBox, SVSM_PERCPU_BASE};
use crate::sev::ghcb::{GhcbPage, GHCB};
use crate::types::PAGE_SIZE;
use alloc::vec::Vec;
use core::cell::{Cell, OnceCell, RefCell, RefMut, UnsafeCell};
use core::mem::size_of;
use core::ptr;

#[derive(Copy, Clone, Debug)]
pub struct PerCpuInfo {
    apic_id: u32,
    cpu_shared: &'static PerCpuShared,
}

impl PerCpuInfo {
    const fn new(apic_id: u32, cpu_shared: &'static PerCpuShared) -> Self {
        Self {
            apic_id,
            cpu_shared,
        }
    }
}

// PERCPU areas virtual addresses into shared memory
pub static PERCPU_AREAS: PerCpuAreas = PerCpuAreas::new();

// We use an UnsafeCell to allow for a static with interior
// mutability. Normally, we would need to guarantee synchronization
// on the backing datatype, but this is not needed because writes to
// the structure only occur at initialization, from CPU 0, and reads
// should only occur after all writes are done.
#[derive(Debug)]
pub struct PerCpuAreas {
    areas: UnsafeCell<Vec<PerCpuInfo>>,
}

unsafe impl Sync for PerCpuAreas {}

impl PerCpuAreas {
    const fn new() -> Self {
        Self {
            areas: UnsafeCell::new(Vec::new()),
        }
    }

    unsafe fn push(&self, info: PerCpuInfo) {
        let ptr = self.areas.get().as_mut().unwrap();
        ptr.push(info);
    }
}

#[derive(Debug)]
pub struct PerCpuShared {
    apic_id: u32,
}

impl PerCpuShared {
    fn new(apic_id: u32) -> Self {
        PerCpuShared { apic_id }
    }
}

const _: () = assert!(size_of::<PerCpu>() <= PAGE_SIZE);

/// CPU-local data.
///
/// This type is not [`Sync`], as its contents will only be accessed from the
/// local CPU, much like thread-local data in an std environment. The only
/// part of the struct that may be accessed from a different CPU is the
/// `shared` field, a reference to which will be stored in [`PERCPU_AREAS`].
#[derive(Debug)]
pub struct PerCpu {
    pgtbl: RefCell<Option<&'static mut PageTable>>,

    /// GHCB page for this CPU.
    ghcb: OnceCell<GhcbPage>,
}

impl PerCpu {
    /// Creates a new default [`PerCpu`] struct.
    fn new(apic_id: u32) -> Self {
        Self {
            pgtbl: RefCell::new(None),
            ghcb: OnceCell::new(),
        }
    }

    /// Creates a new default [`PerCpu`] struct, allocates it via the page
    /// allocator and adds it to the global per-cpu area list.
    pub fn alloc(apic_id: u32) -> Result<&'static Self, SvsmError> {
        let page = PageBox::try_new(Self::new(apic_id))?;
        let percpu = PageBox::leak(page);
        Ok(percpu)
    }

    /// Sets up the CPU-local GHCB page.
    pub fn setup_ghcb(&self) -> Result<(), SvsmError> {
        let page = GhcbPage::new()?;
        self.ghcb
            .set(page)
            .expect("Attempted to reinitialize the GHCB");
        Ok(())
    }

    fn ghcb(&self) -> Option<&GhcbPage> {
        self.ghcb.get()
    }

    pub fn set_pgtable(&self, pgtable: &'static mut PageTable) {
        *self.pgtbl.borrow_mut() = Some(pgtable);
    }

    pub fn get_pgtable(&self) -> RefMut<'_, PageTable> {
        RefMut::map(self.pgtbl.borrow_mut(), |pgtbl| {
            &mut **pgtbl.as_mut().unwrap()
        })
    }

    /// Registers an already set up GHCB page for this CPU.
    ///
    /// # Panics
    ///
    /// Panics if the GHCB for this CPU has not been set up via
    /// [`PerCpu::setup_ghcb()`].
    pub fn register_ghcb(&self) -> Result<(), SvsmError> {
        self.ghcb().unwrap().register()
    }

    pub fn map_self_stage2(&self) -> Result<(), SvsmError> {
        let vaddr = VirtAddr::from(ptr::from_ref(self));
        let paddr = virt_to_phys(vaddr);
        let flags = PTEntryFlags::data();
        self.get_pgtable().map_4k(SVSM_PERCPU_BASE, paddr, flags)
    }
}

pub fn this_cpu() -> &'static PerCpu {
    unsafe { &*SVSM_PERCPU_BASE.as_ptr::<PerCpu>() }
}

/// Gets the GHCB for this CPU.
///
/// # Panics
///
/// Panics if the GHCB for this CPU has not been set up via
/// [`PerCpu::setup_ghcb()`].
pub fn current_ghcb() -> &'static GHCB {
    this_cpu().ghcb().unwrap()
}

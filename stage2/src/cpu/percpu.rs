// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

extern crate alloc;

use crate::address::{PhysAddr, VirtAddr};
use crate::cpu::IrqState;
use crate::error::SvsmError;
use crate::locking::{LockGuard, SpinLock};
use crate::mm::pagetable::{PTEntryFlags, PageTable};
use crate::mm::virtualrange::VirtualRange;
use crate::mm::{virt_to_phys, PageBox, SVSM_PERCPU_BASE};
use crate::sev::ghcb::{GhcbPage, GHCB};
use crate::sev::hv_doorbell::HVDoorbell;
use crate::types::PAGE_SIZE;
use crate::utils::MemoryRegion;
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
struct IstStacks {
    double_fault_stack: Cell<Option<VirtAddr>>,
}

impl IstStacks {
    const fn new() -> Self {
        IstStacks {
            double_fault_stack: Cell::new(None),
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct GuestVmsaRef {
    caa: Option<PhysAddr>,
}

impl GuestVmsaRef {
    pub const fn new() -> Self {
        GuestVmsaRef { caa: None }
    }

    pub fn caa_phys(&self) -> Option<PhysAddr> {
        self.caa
    }
}

#[derive(Debug)]
pub struct PerCpuShared {
    apic_id: u32,
    guest_vmsa: SpinLock<GuestVmsaRef>,
}

impl PerCpuShared {
    fn new(apic_id: u32) -> Self {
        PerCpuShared {
            apic_id,
            guest_vmsa: SpinLock::new(GuestVmsaRef::new()),
        }
    }

    pub const fn apic_id(&self) -> u32 {
        self.apic_id
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
    /// Per-CPU storage that might be accessed from other CPUs.
    shared: PerCpuShared,

    /// PerCpu IRQ state tracking
    irq_state: IrqState,

    pgtbl: RefCell<Option<&'static mut PageTable>>,
    /// Address allocator for per-cpu 4k temporary mappings
    pub vrange_4k: RefCell<VirtualRange>,
    /// Address allocator for per-cpu 2m temporary mappings
    pub vrange_2m: RefCell<VirtualRange>,

    /// GHCB page for this CPU.
    ghcb: OnceCell<GhcbPage>,

    /// `#HV` doorbell page for this CPU.
    hv_doorbell: Cell<Option<&'static HVDoorbell>>,

    init_stack: Cell<Option<VirtAddr>>,
    ist: IstStacks,

    /// Stack boundaries of the currently running task.
    current_stack: Cell<MemoryRegion<VirtAddr>>,
}

impl PerCpu {
    /// Creates a new default [`PerCpu`] struct.
    fn new(apic_id: u32) -> Self {
        Self {
            pgtbl: RefCell::new(None),
            irq_state: IrqState::new(),

            vrange_4k: RefCell::new(VirtualRange::new()),
            vrange_2m: RefCell::new(VirtualRange::new()),

            shared: PerCpuShared::new(apic_id),
            ghcb: OnceCell::new(),
            hv_doorbell: Cell::new(None),
            init_stack: Cell::new(None),
            ist: IstStacks::new(),
            current_stack: Cell::new(MemoryRegion::new(VirtAddr::null(), 0)),
        }
    }

    /// Creates a new default [`PerCpu`] struct, allocates it via the page
    /// allocator and adds it to the global per-cpu area list.
    pub fn alloc(apic_id: u32) -> Result<&'static Self, SvsmError> {
        let page = PageBox::try_new(Self::new(apic_id))?;
        let percpu = PageBox::leak(page);
        unsafe { PERCPU_AREAS.push(PerCpuInfo::new(apic_id, &percpu.shared)) };
        Ok(percpu)
    }

    pub fn shared(&self) -> &PerCpuShared {
        &self.shared
    }

    /// Disables IRQs on the current CPU. Keeps track of the nesting level and
    /// the original IRQ state.
    ///
    /// # Safety
    ///
    /// Caller needs to make sure to match every `disable()` call with an
    /// `enable()` call.
    #[inline(always)]
    pub unsafe fn irqs_disable(&self) {
        self.irq_state.disable();
    }

    /// Reduces IRQ-disable nesting level on the current CPU and restores the
    /// original IRQ state when the level reaches 0.
    ///
    /// # Safety
    ///
    /// Caller needs to make sure to match every `disable()` call with an
    /// `enable()` call.
    #[inline(always)]
    pub unsafe fn irqs_enable(&self) {
        self.irq_state.enable();
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

    pub fn hv_doorbell(&self) -> Option<&'static HVDoorbell> {
        self.hv_doorbell.get()
    }

    pub fn get_top_of_stack(&self) -> VirtAddr {
        self.init_stack.get().unwrap()
    }

    pub fn get_top_of_df_stack(&self) -> VirtAddr {
        self.ist.double_fault_stack.get().unwrap()
    }

    pub fn get_current_stack(&self) -> MemoryRegion<VirtAddr> {
        self.current_stack.get()
    }

    pub fn get_apic_id(&self) -> u32 {
        self.shared().apic_id()
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

    pub fn guest_vmsa_ref(&self) -> LockGuard<'_, GuestVmsaRef> {
        self.shared().guest_vmsa.lock()
    }
}

pub fn this_cpu() -> &'static PerCpu {
    unsafe { &*SVSM_PERCPU_BASE.as_ptr::<PerCpu>() }
}

/// Disables IRQs on the current CPU. Keeps track of the nesting level and
/// the original IRQ state.
///
/// # Safety
///
/// Caller needs to make sure to match every `irqs_disable()` call with an
/// `irqs_enable()` call.
#[inline(always)]
pub unsafe fn irqs_disable() {
    this_cpu().irqs_disable();
}

/// Reduces IRQ-disable nesting level on the current CPU and restores the
/// original IRQ state when the level reaches 0.
///
/// # Safety
///
/// Caller needs to make sure to match every `irqs_disable()` call with an
/// `irqs_enable()` call.
#[inline(always)]
pub unsafe fn irqs_enable() {
    this_cpu().irqs_enable();
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

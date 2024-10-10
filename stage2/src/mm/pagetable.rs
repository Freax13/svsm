// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::address::{Address, PhysAddr, VirtAddr};
use crate::cpu::flush_tlb_global_sync;
use crate::error::SvsmError;
use crate::mm::alloc::allocate_page_zeroed;
use crate::mm::{phys_to_virt, virt_to_phys};
use crate::platform::SvsmPlatform;
use crate::types::{PageSize, PAGE_SIZE, PAGE_SIZE_2M};
use crate::utils::immut_after_init::{ImmutAfterInitCell, ImmutAfterInitResult};
use crate::utils::MemoryRegion;
use bitflags::bitflags;
use core::cmp;
use core::ops::{Index, IndexMut};

use super::SVSM_PTE_BASE;

/// Number of entries in a page table (4KB/8B).
const ENTRY_COUNT: usize = 512;

/// Mask for private page table entry.
static PRIVATE_PTE_MASK: ImmutAfterInitCell<usize> = ImmutAfterInitCell::new(0);

/// Mask for shared page table entry.
static SHARED_PTE_MASK: ImmutAfterInitCell<usize> = ImmutAfterInitCell::new(0);

/// Maximum physical address supported by the system.
static MAX_PHYS_ADDR: ImmutAfterInitCell<u64> = ImmutAfterInitCell::uninit();

/// Maximum physical address bits supported by the system.
static PHYS_ADDR_SIZE: ImmutAfterInitCell<u32> = ImmutAfterInitCell::uninit();

/// Feature mask for page table entry flags.
static FEATURE_MASK: ImmutAfterInitCell<PTEntryFlags> =
    ImmutAfterInitCell::new(PTEntryFlags::empty());

/// Re-initializes early paging settings.
pub fn paging_init_early(platform: &dyn SvsmPlatform) -> ImmutAfterInitResult<()> {
    init_encrypt_mask(platform)?;

    let mut feature_mask = PTEntryFlags::all();
    feature_mask.remove(PTEntryFlags::GLOBAL);
    FEATURE_MASK.reinit(&feature_mask)
}

/// Initializes the encrypt mask.
fn init_encrypt_mask(platform: &dyn SvsmPlatform) -> ImmutAfterInitResult<()> {
    let masks = platform.get_page_encryption_masks();

    PRIVATE_PTE_MASK.reinit(&masks.private_pte_mask)?;
    SHARED_PTE_MASK.reinit(&masks.shared_pte_mask)?;

    let guest_phys_addr_size = (masks.phys_addr_sizes >> 16) & 0xff;
    let host_phys_addr_size = masks.phys_addr_sizes & 0xff;
    let phys_addr_size = if guest_phys_addr_size == 0 {
        // When [GuestPhysAddrSize] is zero, refer to the PhysAddrSize field
        // for the maximum guest physical address size.
        // - APM3, E.4.7 Function 8000_0008h - Processor Capacity Parameters and Extended Feature Identification
        host_phys_addr_size
    } else {
        guest_phys_addr_size
    };

    PHYS_ADDR_SIZE.reinit(&phys_addr_size)?;

    // If the C-bit is a physical address bit however, the guest physical
    // address space is effectively reduced by 1 bit.
    // - APM2, 15.34.6 Page Table Support
    let effective_phys_addr_size = cmp::min(masks.addr_mask_width, phys_addr_size);

    let max_addr = 1 << effective_phys_addr_size;
    MAX_PHYS_ADDR.reinit(&max_addr)
}

/// Returns the private encrypt mask value.
fn private_pte_mask() -> usize {
    *PRIVATE_PTE_MASK
}

/// Returns the shared encrypt mask value.
fn shared_pte_mask() -> usize {
    *SHARED_PTE_MASK
}

/// Returns the exclusive end of the physical address space.
pub fn max_phys_addr() -> PhysAddr {
    PhysAddr::from(*MAX_PHYS_ADDR)
}

/// Returns the supported flags considering the feature mask.
fn supported_flags(flags: PTEntryFlags) -> PTEntryFlags {
    flags & *FEATURE_MASK
}

/// Set address as shared via mask.
fn make_shared_address(paddr: PhysAddr) -> PhysAddr {
    PhysAddr::from(paddr.bits() & !private_pte_mask() | shared_pte_mask())
}

/// Set address as private via mask.
fn make_private_address(paddr: PhysAddr) -> PhysAddr {
    PhysAddr::from(paddr.bits() & !shared_pte_mask() | private_pte_mask())
}

fn strip_confidentiality_bits(paddr: PhysAddr) -> PhysAddr {
    PhysAddr::from(paddr.bits() & !(shared_pte_mask() | private_pte_mask()))
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct PTEntryFlags: u64 {
        const PRESENT       = 1 << 0;
        const WRITABLE      = 1 << 1;
        const USER      = 1 << 2;
        const ACCESSED      = 1 << 5;
        const DIRTY     = 1 << 6;
        const HUGE      = 1 << 7;
        const GLOBAL        = 1 << 8;
        const NX        = 1 << 63;
    }
}

impl PTEntryFlags {
    pub fn data() -> Self {
        Self::PRESENT | Self::GLOBAL | Self::WRITABLE | Self::NX | Self::ACCESSED | Self::DIRTY
    }
}

/// Represents a page table entry.
#[repr(C)]
#[derive(Copy, Clone, Debug, Default)]
pub struct PTEntry(PhysAddr);

impl PTEntry {
    /// Check if the page table entry is clear (null).
    pub fn is_clear(&self) -> bool {
        self.0.is_null()
    }

    /// Clear the page table entry.
    pub fn clear(&mut self) {
        self.0 = PhysAddr::null();
    }

    /// Check if the page table entry is present.
    pub fn present(&self) -> bool {
        self.flags().contains(PTEntryFlags::PRESENT)
    }

    /// Check if the page table entry is huge.
    pub fn huge(&self) -> bool {
        self.flags().contains(PTEntryFlags::HUGE)
    }

    /// Check if the page table entry is writable.
    pub fn writable(&self) -> bool {
        self.flags().contains(PTEntryFlags::WRITABLE)
    }

    /// Check if the page table entry is NX (no-execute).
    pub fn nx(&self) -> bool {
        self.flags().contains(PTEntryFlags::NX)
    }

    /// Check if the page table entry is user-accessible.
    pub fn user(&self) -> bool {
        self.flags().contains(PTEntryFlags::USER)
    }

    /// Get the raw bits (`u64`) of the page table entry.
    pub fn raw(&self) -> u64 {
        self.0.bits() as u64
    }

    /// Get the flags of the page table entry.
    pub fn flags(&self) -> PTEntryFlags {
        PTEntryFlags::from_bits_truncate(self.0.bits() as u64)
    }

    /// Set the page table entry with the specified address and flags.
    pub fn set(&mut self, addr: PhysAddr, flags: PTEntryFlags) {
        let addr = addr.bits() as u64;
        assert_eq!(addr & !0x000f_ffff_ffff_f000, 0);
        self.0 = PhysAddr::from(addr | supported_flags(flags).bits());
    }

    /// Get the address from the page table entry, excluding the C bit.
    pub fn address(&self) -> PhysAddr {
        let addr = PhysAddr::from(self.0.bits() & 0x000f_ffff_ffff_f000);
        strip_confidentiality_bits(addr)
    }

    /// Read a page table entry from the specified virtual address.
    ///
    /// # Safety
    ///
    /// Reads from an arbitrary virtual address, making this essentially a
    /// raw pointer read.  The caller must be certain to calculate the correct
    /// address.
    pub unsafe fn read_pte(vaddr: VirtAddr) -> Self {
        *vaddr.as_ptr::<Self>()
    }
}

/// A pagetable page with multiple entries.
#[repr(C)]
#[derive(Debug)]
pub struct PTPage {
    entries: [PTEntry; ENTRY_COUNT],
}

impl PTPage {
    /// Allocates a zeroed pagetable page and returns a mutable reference to
    /// it, plus its physical address.
    ///
    /// # Errors
    ///
    /// Returns [`SvsmError`] if the page cannot be allocated.
    fn alloc() -> Result<(&'static mut Self, PhysAddr), SvsmError> {
        let vaddr = allocate_page_zeroed()?;
        let page: &mut Self = unsafe { &mut *vaddr.as_mut_ptr() };
        let paddr = virt_to_phys(vaddr);
        Ok((page, paddr))
    }

    /// Converts a pagetable entry to a mutable reference to a [`PTPage`],
    /// if the entry is present and not huge.
    fn from_entry(entry: PTEntry) -> Option<&'static mut Self> {
        let flags = entry.flags();
        if !flags.contains(PTEntryFlags::PRESENT) || flags.contains(PTEntryFlags::HUGE) {
            return None;
        }

        let address = phys_to_virt(entry.address());
        Some(unsafe { &mut *address.as_mut_ptr::<PTPage>() })
    }
}

impl Default for PTPage {
    fn default() -> Self {
        let entries = [PTEntry::default(); ENTRY_COUNT];
        PTPage { entries }
    }
}

/// Can be used to access page table entries by index.
impl Index<usize> for PTPage {
    type Output = PTEntry;

    fn index(&self, index: usize) -> &PTEntry {
        &self.entries[index]
    }
}

/// Can be used to modify page table entries by index.
impl IndexMut<usize> for PTPage {
    fn index_mut(&mut self, index: usize) -> &mut PTEntry {
        &mut self.entries[index]
    }
}

/// Mapping levels of page table entries.
#[derive(Debug)]
pub enum Mapping<'a> {
    Level3(&'a mut PTEntry),
    Level2(&'a mut PTEntry),
    Level1(&'a mut PTEntry),
    Level0(&'a mut PTEntry),
}

/// Page table structure containing a root page with multiple entries.
#[repr(C)]
#[derive(Default, Debug)]
pub struct PageTable {
    root: PTPage,
}

impl PageTable {
    /// Computes the index within a page table at the given level for a
    /// virtual address `vaddr`.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to compute the index for.
    ///
    /// # Returns
    /// The index within the page table.
    pub fn index<const L: usize>(vaddr: VirtAddr) -> usize {
        vaddr.to_pgtbl_idx::<L>()
        //vaddr.bits() >> (12 + L * 9) & 0x1ff
    }

    /// Walks a page table at level 0 to find a mapping.
    ///
    /// # Parameters
    /// - `page`: A mutable reference to the root page table.
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr_lvl0(page: &mut PTPage, vaddr: VirtAddr) -> Mapping<'_> {
        let idx = Self::index::<0>(vaddr);
        Mapping::Level0(&mut page[idx])
    }

    /// Walks a page table at level 1 to find a mapping.
    ///
    /// # Parameters
    /// - `page`: A mutable reference to the root page table.
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr_lvl1(page: &mut PTPage, vaddr: VirtAddr) -> Mapping<'_> {
        let idx = Self::index::<1>(vaddr);
        let entry = page[idx];
        match PTPage::from_entry(entry) {
            Some(page) => Self::walk_addr_lvl0(page, vaddr),
            None => Mapping::Level1(&mut page[idx]),
        }
    }

    /// Walks a page table at level 2 to find a mapping.
    ///
    /// # Parameters
    /// - `page`: A mutable reference to the root page table.
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr_lvl2(page: &mut PTPage, vaddr: VirtAddr) -> Mapping<'_> {
        let idx = Self::index::<2>(vaddr);
        let entry = page[idx];
        match PTPage::from_entry(entry) {
            Some(page) => Self::walk_addr_lvl1(page, vaddr),
            None => Mapping::Level2(&mut page[idx]),
        }
    }

    /// Walks the page table to find a mapping for a given virtual address.
    ///
    /// # Parameters
    /// - `page`: A mutable reference to the root page table.
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr_lvl3(page: &mut PTPage, vaddr: VirtAddr) -> Mapping<'_> {
        let idx = Self::index::<3>(vaddr);
        let entry = page[idx];
        match PTPage::from_entry(entry) {
            Some(page) => Self::walk_addr_lvl2(page, vaddr),
            None => Mapping::Level3(&mut page[idx]),
        }
    }

    /// Walk the virtual address and return the corresponding mapping.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to find a mapping for.
    ///
    /// # Returns
    /// A `Mapping` representing the found mapping.
    fn walk_addr(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        Self::walk_addr_lvl3(&mut self.root, vaddr)
    }

    /// Calculate the virtual address of a PTE in the self-map, which maps a
    /// specified virtual address.
    ///
    /// # Parameters
    /// - `vaddr': The virtual address whose PTE should be located.
    ///
    /// # Returns
    /// The virtual address of the PTE.
    fn get_pte_address(vaddr: VirtAddr) -> VirtAddr {
        SVSM_PTE_BASE + ((usize::from(vaddr) & 0x0000_FFFF_FFFF_F000) >> 9)
    }

    /// Perform a virtual to physical translation using the self-map.
    ///
    /// # Parameters
    /// - `vaddr': The virtual address to transalte.
    ///
    /// # Returns
    /// Some(PhysAddr) if the virtual address is valid.
    /// None if the virtual address is not valid.
    pub fn virt_to_phys(vaddr: VirtAddr) -> Option<PhysAddr> {
        // Calculate the virtual addresses of each level of the paging
        // hierarchy in the self-map.
        let pte_addr = Self::get_pte_address(vaddr);
        let pde_addr = Self::get_pte_address(pte_addr);
        let pdpe_addr = Self::get_pte_address(pde_addr);
        let pml4e_addr = Self::get_pte_address(pdpe_addr);

        // Check each entry in the paging hierarchy to determine whether this
        // address is mapped.  Because the hierarchy is read from the top
        // down using self-map addresses that were calculated correctly,
        // the reads are safe to perform.
        let pml4e = unsafe { PTEntry::read_pte(pml4e_addr) };
        if !pml4e.present() {
            return None;
        }

        // There is no need to check for a large page in the PML4E because
        // the architecture does not support the large bit at the top-level
        // entry.  If a large page is detected at a lower level of the
        // hierarchy, the low bits from the virtual address must be combined
        // with the physical address from the PDE/PDPE.
        let pdpe = unsafe { PTEntry::read_pte(pdpe_addr) };
        if !pdpe.present() {
            return None;
        }
        if pdpe.huge() {
            return Some(pdpe.address() + (usize::from(vaddr) & 0x3FFF_FFFF));
        }

        let pde = unsafe { PTEntry::read_pte(pde_addr) };
        if !pde.present() {
            return None;
        }
        if pde.huge() {
            return Some(pde.address() + (usize::from(vaddr) & 0x001F_FFFF));
        }

        let pte = unsafe { PTEntry::read_pte(pte_addr) };
        if pte.present() {
            Some(pte.address() + (usize::from(vaddr) & 0xFFF))
        } else {
            None
        }
    }

    fn alloc_pte_lvl3(entry: &mut PTEntry, vaddr: VirtAddr, size: PageSize) -> Mapping<'_> {
        let flags = entry.flags();

        if flags.contains(PTEntryFlags::PRESENT) {
            return Mapping::Level3(entry);
        }

        let Ok((page, paddr)) = PTPage::alloc() else {
            return Mapping::Level3(entry);
        };

        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        entry.set(make_private_address(paddr), flags);

        let idx = Self::index::<2>(vaddr);
        Self::alloc_pte_lvl2(&mut page[idx], vaddr, size)
    }

    fn alloc_pte_lvl2(entry: &mut PTEntry, vaddr: VirtAddr, size: PageSize) -> Mapping<'_> {
        let flags = entry.flags();

        if flags.contains(PTEntryFlags::PRESENT) {
            return Mapping::Level2(entry);
        }

        let Ok((page, paddr)) = PTPage::alloc() else {
            return Mapping::Level2(entry);
        };

        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        entry.set(make_private_address(paddr), flags);

        let idx = Self::index::<1>(vaddr);
        Self::alloc_pte_lvl1(&mut page[idx], vaddr, size)
    }

    fn alloc_pte_lvl1(entry: &mut PTEntry, vaddr: VirtAddr, size: PageSize) -> Mapping<'_> {
        let flags = entry.flags();

        if size == PageSize::Huge || flags.contains(PTEntryFlags::PRESENT) {
            return Mapping::Level1(entry);
        }

        let Ok((page, paddr)) = PTPage::alloc() else {
            return Mapping::Level1(entry);
        };

        let flags = PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::USER
            | PTEntryFlags::ACCESSED;
        entry.set(make_private_address(paddr), flags);

        let idx = Self::index::<0>(vaddr);
        Mapping::Level0(&mut page[idx])
    }

    /// Allocates a 4KB page table entry for a given virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address for which to allocate the PTE.
    ///
    /// # Returns
    /// A `Mapping` representing the allocated or existing PTE for the address.
    fn alloc_pte_4k(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        let m = self.walk_addr(vaddr);

        match m {
            Mapping::Level0(entry) => Mapping::Level0(entry),
            Mapping::Level1(entry) => Self::alloc_pte_lvl1(entry, vaddr, PageSize::Regular),
            Mapping::Level2(entry) => Self::alloc_pte_lvl2(entry, vaddr, PageSize::Regular),
            Mapping::Level3(entry) => Self::alloc_pte_lvl3(entry, vaddr, PageSize::Regular),
        }
    }

    /// Allocates a 2MB page table entry for a given virtual address.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address for which to allocate the PTE.
    ///
    /// # Returns
    /// A `Mapping` representing the allocated or existing PTE for the address.
    fn alloc_pte_2m(&mut self, vaddr: VirtAddr) -> Mapping<'_> {
        let m = self.walk_addr(vaddr);

        match m {
            Mapping::Level0(entry) => Mapping::Level0(entry),
            Mapping::Level1(entry) => Mapping::Level1(entry),
            Mapping::Level2(entry) => Self::alloc_pte_lvl2(entry, vaddr, PageSize::Huge),
            Mapping::Level3(entry) => Self::alloc_pte_lvl3(entry, vaddr, PageSize::Huge),
        }
    }

    /// Splits a 2MB page into 4KB pages.
    ///
    /// # Parameters
    /// - `entry`: The 2M page table entry to split.
    ///
    /// # Returns
    /// A result indicating success or an error [`SvsmError`] in failure.
    fn do_split_4k(entry: &mut PTEntry) -> Result<(), SvsmError> {
        let (page, paddr) = PTPage::alloc()?;
        let mut flags = entry.flags();

        assert!(flags.contains(PTEntryFlags::HUGE));

        let addr_2m = PhysAddr::from(entry.address().bits() & 0x000f_ffff_fff0_0000);

        flags.remove(PTEntryFlags::HUGE);

        // Prepare PTE leaf page
        for (i, e) in page.entries.iter_mut().enumerate() {
            let addr_4k = addr_2m + (i * PAGE_SIZE);
            e.clear();
            e.set(make_private_address(addr_4k), flags);
        }

        entry.set(make_private_address(paddr), flags);

        flush_tlb_global_sync();

        Ok(())
    }

    /// Splits a page into 4KB pages if it is part of a larger mapping.
    ///
    /// # Parameters
    /// - `mapping`: The mapping to split.
    ///
    /// # Returns
    /// A result indicating success or an error [`SvsmError`].
    fn split_4k(mapping: Mapping<'_>) -> Result<(), SvsmError> {
        match mapping {
            Mapping::Level0(_entry) => Ok(()),
            Mapping::Level1(entry) => Self::do_split_4k(entry),
            Mapping::Level2(_entry) => Err(SvsmError::Mem),
            Mapping::Level3(_entry) => Err(SvsmError::Mem),
        }
    }

    fn make_pte_shared(entry: &mut PTEntry) {
        let flags = entry.flags();
        let addr = entry.address();

        // entry.address() returned with c-bit clear already
        entry.set(make_shared_address(addr), flags);
    }

    fn make_pte_private(entry: &mut PTEntry) {
        let flags = entry.flags();
        let addr = entry.address();

        // entry.address() returned with c-bit clear already
        entry.set(make_private_address(addr), flags);
    }

    /// Sets the shared state for a 4KB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address of the page.
    ///
    /// # Returns
    /// A result indicating success or an error [`SvsmError`] if the
    /// operation fails.
    pub fn set_shared_4k(&mut self, vaddr: VirtAddr) -> Result<(), SvsmError> {
        let mapping = self.walk_addr(vaddr);
        Self::split_4k(mapping)?;

        if let Mapping::Level0(entry) = self.walk_addr(vaddr) {
            Self::make_pte_shared(entry);
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Sets the encryption state for a 4KB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address of the page.
    ///
    /// # Returns
    /// A result indicating success or an error [`SvsmError`].
    pub fn set_encrypted_4k(&mut self, vaddr: VirtAddr) -> Result<(), SvsmError> {
        let mapping = self.walk_addr(vaddr);
        Self::split_4k(mapping)?;

        if let Mapping::Level0(entry) = self.walk_addr(vaddr) {
            Self::make_pte_private(entry);
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Maps a 2MB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to map.
    /// - `paddr`: The physical address to map to.
    /// - `flags`: The flags to apply to the mapping.
    ///
    /// # Returns
    /// A result indicating success or failure ([`SvsmError`]).
    ///
    /// # Panics
    /// Panics if either `vaddr` or `paddr` is not aligned to a 2MB boundary.
    pub fn map_2m(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PTEntryFlags,
    ) -> Result<(), SvsmError> {
        assert!(vaddr.is_aligned(PAGE_SIZE_2M));
        assert!(paddr.is_aligned(PAGE_SIZE_2M));

        let mapping = self.alloc_pte_2m(vaddr);

        if let Mapping::Level1(entry) = mapping {
            entry.set(make_private_address(paddr), flags | PTEntryFlags::HUGE);
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Unmaps a 2MB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address of the mapping to unmap.
    ///
    /// # Panics
    /// Panics if `vaddr` is not aligned to a 2MB boundary.
    pub fn unmap_2m(&mut self, vaddr: VirtAddr) {
        assert!(vaddr.is_aligned(PAGE_SIZE_2M));

        let mapping = self.walk_addr(vaddr);

        match mapping {
            Mapping::Level0(_) => unreachable!(),
            Mapping::Level1(entry) => entry.clear(),
            Mapping::Level2(entry) => assert!(!entry.present()),
            Mapping::Level3(entry) => assert!(!entry.present()),
        }
    }

    /// Maps a 4KB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address to map.
    /// - `paddr`: The physical address to map to.
    /// - `flags`: The flags to apply to the mapping.
    ///
    /// # Returns
    /// A result indicating success or failure ([`SvsmError`]).
    pub fn map_4k(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PTEntryFlags,
    ) -> Result<(), SvsmError> {
        let mapping = self.alloc_pte_4k(vaddr);

        if let Mapping::Level0(entry) = mapping {
            entry.set(make_private_address(paddr), flags);
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Unmaps a 4KB page.
    ///
    /// # Parameters
    /// - `vaddr`: The virtual address of the mapping to unmap.
    pub fn unmap_4k(&mut self, vaddr: VirtAddr) {
        let mapping = self.walk_addr(vaddr);

        match mapping {
            Mapping::Level0(entry) => entry.clear(),
            Mapping::Level1(entry) => assert!(!entry.present()),
            Mapping::Level2(entry) => assert!(!entry.present()),
            Mapping::Level3(entry) => assert!(!entry.present()),
        }
    }

    /// Maps a memory region to physical memory with specified flags.
    ///
    /// # Parameters
    /// - `region`: The virtual memory region to map.
    /// - `phys`: The starting physical address to map to.
    /// - `flags`: The flags to apply to the page table entries.
    ///
    /// # Returns
    /// A result indicating success (`Ok`) or failure (`Err`).
    pub fn map_region(
        &mut self,
        region: MemoryRegion<VirtAddr>,
        phys: PhysAddr,
        flags: PTEntryFlags,
    ) -> Result<(), SvsmError> {
        let mut vaddr = region.start();
        let end = region.end();
        let mut paddr = phys;

        while vaddr < end {
            if vaddr.is_aligned(PAGE_SIZE_2M)
                && paddr.is_aligned(PAGE_SIZE_2M)
                && vaddr + PAGE_SIZE_2M <= end
                && self.map_2m(vaddr, paddr, flags).is_ok()
            {
                vaddr = vaddr + PAGE_SIZE_2M;
                paddr = paddr + PAGE_SIZE_2M;
                continue;
            }

            self.map_4k(vaddr, paddr, flags)?;
            vaddr = vaddr + PAGE_SIZE;
            paddr = paddr + PAGE_SIZE;
        }

        Ok(())
    }
}

bitflags! {
    /// Flags to represent how memory is accessed, e.g. write data to the
    /// memory or fetch code from the memory.
    #[derive(Clone, Copy, Debug)]
    pub struct MemAccessMode: u32 {
        const WRITE     = 1 << 0;
        const FETCH     = 1 << 1;
    }
}

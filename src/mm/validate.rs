// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::locking::SpinLock;
use crate::mm::alloc::{allocate_pages, get_order};
use crate::mm::virt_to_phys;
use crate::types::{PhysAddr, VirtAddr, PAGE_SIZE, PAGE_SIZE_2M};
use crate::utils::util::is_aligned;
use core::ptr;

static VALID_BITMAP: SpinLock<ValidBitmap> = SpinLock::new(ValidBitmap::new());

#[inline(always)]
fn bitmap_alloc_order(pbase: PhysAddr, pend: PhysAddr) -> usize {
    let mem_size = (pend - pbase) / (PAGE_SIZE * 8);
    get_order(mem_size)
}

pub fn init_valid_bitmap_ptr(pbase: PhysAddr, pend: PhysAddr, bitmap: *mut u64) {
    let mut vb_ref = VALID_BITMAP.lock();
    vb_ref.set_range(pbase, pend);
    vb_ref.set_bitmap(bitmap);
}

pub fn init_valid_bitmap_alloc(pbase: PhysAddr, pend: PhysAddr) -> Result<(), ()> {
    let order: usize = bitmap_alloc_order(pbase, pend);
    let bitmap_addr = allocate_pages(order)?;

    let mut vb_ref = VALID_BITMAP.lock();
    vb_ref.set_range(pbase, pend);
    vb_ref.set_bitmap(bitmap_addr as *mut u64);
    vb_ref.clear_all();

    Ok(())
}

pub fn migrate_valid_bitmap() -> Result<(), ()> {
    let order: usize = VALID_BITMAP.lock().alloc_order();
    let bitmap_addr = allocate_pages(order)?;

    // lock again here because allocator path also takes VALID_BITMAP.lock()
    let mut vb_ref = VALID_BITMAP.lock();
    vb_ref.migrate(bitmap_addr as *mut u64);
    Ok(())
}

pub fn validated_phys_addr(paddr: PhysAddr) -> bool {
    let vb_ref = VALID_BITMAP.lock();
    vb_ref.is_valid_4k(paddr)
}

pub fn valid_bitmap_set_valid_4k(paddr: PhysAddr) {
    let mut vb_ref = VALID_BITMAP.lock();
    vb_ref.set_valid_4k(paddr)
}

pub fn valid_bitmap_clear_valid_4k(paddr: PhysAddr) {
    let mut vb_ref = VALID_BITMAP.lock();
    vb_ref.clear_valid_4k(paddr)
}

pub fn valid_bitmap_set_valid_2m(paddr: PhysAddr) {
    let mut vb_ref = VALID_BITMAP.lock();
    vb_ref.set_valid_2m(paddr)
}

pub fn valid_bitmap_clear_valid_2m(paddr: PhysAddr) {
    let mut vb_ref = VALID_BITMAP.lock();
    vb_ref.clear_valid_2m(paddr)
}

pub fn valid_bitmap_addr() -> PhysAddr {
    let vb_ref = VALID_BITMAP.lock();
    vb_ref.bitmap_addr()
}

pub fn valid_bitmap_valid_addr(paddr: PhysAddr) -> bool {
    let vb_ref = VALID_BITMAP.lock();
    vb_ref.check_addr(paddr)
}

struct ValidBitmap {
    pbase: PhysAddr,
    pend: PhysAddr,
    bitmap: *mut u64,
}

impl ValidBitmap {
    pub const fn new() -> Self {
        ValidBitmap {
            pbase: 0,
            pend: 0,
            bitmap: ptr::null_mut(),
        }
    }

    pub fn set_range(&mut self, pbase: PhysAddr, pend: PhysAddr) {
        self.pbase = pbase;
        self.pend = pend;
    }

    pub fn set_bitmap(&mut self, bitmap: *mut u64) {
        self.bitmap = bitmap;
    }

    pub fn check_addr(&self, paddr: PhysAddr) -> bool {
        paddr >= self.pbase && paddr < self.pend
    }

    pub fn bitmap_addr(&self) -> PhysAddr {
        assert!(!self.bitmap.is_null());
        virt_to_phys(self.bitmap as VirtAddr)
    }

    #[inline(always)]
    fn index(&self, paddr: PhysAddr) -> (isize, usize) {
        let page_offset = (paddr - self.pbase) / PAGE_SIZE;
        let index: isize = (page_offset / 64).try_into().unwrap();
        let bit: usize = page_offset % 64;

        (index, bit)
    }

    pub fn clear_all(&mut self) {
        let (i, _) = self.index(self.pend - 1);
        let index: usize = i.try_into().unwrap();

        unsafe {
            ptr::write_bytes(self.bitmap, 0, index);
        }
    }

    pub fn alloc_order(&self) -> usize {
        bitmap_alloc_order(self.pbase, self.pend)
    }

    pub fn migrate(&mut self, new_bitmap: *mut u64) {
        let (count, _) = self.index(self.pend);

        unsafe {
            ptr::copy_nonoverlapping(self.bitmap, new_bitmap, count as usize);
        }
        self.bitmap = new_bitmap;
    }

    fn initialized(&self) -> bool {
        !self.bitmap.is_null()
    }

    pub fn set_valid_4k(&mut self, paddr: PhysAddr) {
        if !self.initialized() {
            return;
        }

        let (index, bit) = self.index(paddr);

        assert!(is_aligned(paddr, PAGE_SIZE));
        assert!(self.check_addr(paddr));

        unsafe {
            let mut val: u64 = ptr::read(self.bitmap.offset(index));
            val |= 1u64 << bit;
            ptr::write(self.bitmap.offset(index), val);
        }
    }

    pub fn clear_valid_4k(&mut self, paddr: PhysAddr) {
        if !self.initialized() {
            return;
        }

        let (index, bit) = self.index(paddr);

        assert!(is_aligned(paddr, PAGE_SIZE));
        assert!(self.check_addr(paddr));

        unsafe {
            let mut val: u64 = ptr::read(self.bitmap.offset(index));
            val &= !(1u64 << bit);
            ptr::write(self.bitmap.offset(index), val);
        }
    }

    fn set_2m(&mut self, paddr: PhysAddr, val: u64) {
        if !self.initialized() {
            return;
        }

        const NR_INDEX: isize = (PAGE_SIZE_2M / (PAGE_SIZE * 64)) as isize;
        let (index, _) = self.index(paddr);

        assert!(is_aligned(paddr, PAGE_SIZE_2M));
        assert!(self.check_addr(paddr));

        for i in 0..NR_INDEX {
            unsafe {
                ptr::write(self.bitmap.offset(index + i), val);
            }
        }
    }

    pub fn set_valid_2m(&mut self, paddr: PhysAddr) {
        self.set_2m(paddr, !0u64);
    }

    pub fn clear_valid_2m(&mut self, paddr: PhysAddr) {
        self.set_2m(paddr, 0u64);
    }

    pub fn is_valid_4k(&self, paddr: PhysAddr) -> bool {
        if !self.initialized() {
            return false;
        }

        let (index, bit) = self.index(paddr);

        assert!(self.check_addr(paddr));

        unsafe {
            let mask: u64 = 1u64 << bit;
            let val: u64 = ptr::read(self.bitmap.offset(index));

            (val & mask) == mask
        }
    }
}

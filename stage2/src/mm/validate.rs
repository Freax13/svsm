// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::address::{Address, PhysAddr, VirtAddr};
use crate::error::SvsmError;
use crate::locking::SpinLock;
use crate::mm::alloc::allocate_zeroed;
use crate::mm::virt_to_phys;
use crate::types::PAGE_SIZE;
use crate::utils::MemoryRegion;
use core::alloc::Layout;
use core::num::NonZeroUsize;

static VALID_BITMAP: SpinLock<Option<ValidBitmap>> = SpinLock::new(None);

fn bitmap_elems(region: MemoryRegion<PhysAddr>) -> NonZeroUsize {
    NonZeroUsize::new(
        region
            .len()
            .div_ceil(PAGE_SIZE)
            .div_ceil(u64::BITS as usize),
    )
    .unwrap()
}

pub fn init_valid_bitmap_alloc(region: MemoryRegion<PhysAddr>) -> Result<(), SvsmError> {
    let len = bitmap_elems(region);
    let layout = Layout::array::<u64>(len.get()).unwrap();
    let ptr = allocate_zeroed(layout)?;
    let bitmap = unsafe { core::slice::from_raw_parts_mut(ptr.as_mut_ptr(), len.get()) };
    *VALID_BITMAP.lock() = Some(ValidBitmap::new(region, bitmap));

    Ok(())
}

pub fn valid_bitmap_set_valid_4k(paddr: PhysAddr) {
    if let Some(vb) = VALID_BITMAP.lock().as_mut() {
        vb.set_valid_4k(paddr);
    }
}

pub fn valid_bitmap_clear_valid_4k(paddr: PhysAddr) {
    if let Some(vb) = VALID_BITMAP.lock().as_mut() {
        vb.clear_valid_4k(paddr);
    }
}

pub fn valid_bitmap_set_valid_range(paddr_begin: PhysAddr, paddr_end: PhysAddr) {
    if let Some(vb) = VALID_BITMAP.lock().as_mut() {
        vb.set_valid_range(paddr_begin, paddr_end);
    }
}

pub fn valid_bitmap_addr() -> PhysAddr {
    VALID_BITMAP.lock().as_ref().unwrap().bitmap_addr()
}

pub fn valid_bitmap_valid_addr(paddr: PhysAddr) -> bool {
    VALID_BITMAP
        .lock()
        .as_ref()
        .map(|vb| vb.check_addr(paddr))
        .unwrap_or(false)
}

#[derive(Debug)]
struct ValidBitmap {
    region: MemoryRegion<PhysAddr>,
    bitmap: &'static mut [u64],
}

impl ValidBitmap {
    fn new(region: MemoryRegion<PhysAddr>, bitmap: &'static mut [u64]) -> Self {
        Self { region, bitmap }
    }

    fn check_addr(&self, paddr: PhysAddr) -> bool {
        self.region.contains(paddr)
    }

    fn bitmap_addr(&self) -> PhysAddr {
        virt_to_phys(VirtAddr::from(self.bitmap.as_ptr()))
    }

    #[inline(always)]
    fn index(&self, paddr: PhysAddr) -> (usize, usize) {
        let page_offset = (paddr - self.region.start()) / PAGE_SIZE;
        let index = page_offset / 64;
        let bit = page_offset % 64;

        (index, bit)
    }

    fn set_valid_4k(&mut self, paddr: PhysAddr) {
        let (index, bit) = self.index(paddr);

        assert!(paddr.is_page_aligned());
        assert!(self.check_addr(paddr));

        self.bitmap[index] |= 1u64 << bit;
    }

    fn clear_valid_4k(&mut self, paddr: PhysAddr) {
        let (index, bit) = self.index(paddr);

        assert!(paddr.is_page_aligned());
        assert!(self.check_addr(paddr));

        self.bitmap[index] &= !(1u64 << bit);
    }

    fn modify_bitmap_word(&mut self, index: usize, mask: u64, new_val: u64) {
        let val = &mut self.bitmap[index];
        *val = (*val & !mask) | (new_val & mask);
    }

    fn set_range(&mut self, paddr_begin: PhysAddr, paddr_end: PhysAddr, new_val: bool) {
        // All ones.
        let mask = !0u64;
        // All ones if val == true, zero otherwise.
        let new_val = 0u64.wrapping_sub(new_val as u64);

        let (index_head, bit_head_begin) = self.index(paddr_begin);
        let (index_tail, bit_tail_end) = self.index(paddr_end);
        if index_head != index_tail {
            let mask_head = mask >> bit_head_begin << bit_head_begin;
            self.modify_bitmap_word(index_head, mask_head, new_val);

            self.bitmap[index_head + 1..index_tail].fill(new_val);

            if bit_tail_end != 0 {
                let mask_tail = mask << (64 - bit_tail_end) >> (64 - bit_tail_end);
                self.modify_bitmap_word(index_tail, mask_tail, new_val);
            }
        } else {
            let mask = mask >> bit_head_begin << bit_head_begin;
            let mask = mask << (64 - bit_tail_end) >> (64 - bit_tail_end);
            self.modify_bitmap_word(index_head, mask, new_val);
        }
    }

    fn set_valid_range(&mut self, paddr_begin: PhysAddr, paddr_end: PhysAddr) {
        self.set_range(paddr_begin, paddr_end, true);
    }
}

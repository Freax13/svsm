use core::alloc::{GlobalAlloc, Layout};
use super::locking::SpinLock;
use super::util::align_up;
use crate::heap_start;
use super::ALLOCATOR;
use core::ptr;

use crate::println;

pub struct Stage2Allocator {
	heap_start : usize,
	heap_end : usize,
	next : usize,
}

impl Stage2Allocator {

	pub const fn new() -> Self {
		Stage2Allocator {
			heap_start: 0,
			heap_end: 0,
			next: 0,
		}
	}

	pub unsafe fn init(&mut self, start: usize, end: usize) {
		self.heap_start	= start;
		self.next	= start;
		self.heap_end	= end;
	}
}


unsafe impl GlobalAlloc for SpinLock<Stage2Allocator> {
	unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
		let mut heap = self.lock();

		let alloc_start = align_up(heap.next, layout.align());
		let alloc_end   = match alloc_start.checked_add(layout.size()) {
			Some(end)	=> end,
			None		=> return ptr::null_mut(),
		};

		if alloc_end > heap.heap_end {
			ptr::null_mut()
		} else {
			heap.next = alloc_end;
			alloc_start as *mut u8
		}
	}

	unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
		// No de-allocation support yet
	}
}

pub fn init_heap() {
	unsafe {
		let start = (&heap_start as *const u8) as usize;
		let end:   usize = 638 * 1024;	// Stage2 memory ends at 640k
		ALLOCATOR.lock().init(start as usize, end);
	}
}

pub fn print_heap_info() {
	let heap = ALLOCATOR.lock();

	println!("HEAP: initialized from {:#05x} to {:#05x})", heap.heap_start, heap.heap_end);
	println!("HEAP: Total size: {}kb Free: {}kb",
		 (heap.heap_end - heap.heap_start) / 1024, (heap.heap_end - heap.next) / 1024);
}

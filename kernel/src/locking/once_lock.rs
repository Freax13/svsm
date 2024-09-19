// SPDX-License-Identifier: MIT OR Apache-2.0

use core::{
    cell::UnsafeCell,
    fmt::{self, Debug},
    mem::MaybeUninit,
    sync::atomic::{AtomicU8, Ordering},
};

/// No thread has attempted to initialize the value yet.
const UNINITIALIZED: u8 = 0;
/// A thread has starting to initialize the value, but has not yet completed
/// initialization done.
const INITIALIZING: u8 = 1;
/// The value has been fully initialized.
const INITIALIZED: u8 = 2;

/// A synchronization primitive which can nominally be written to only once.
///
/// Note that this data structure is named after the data structure in std with
/// the same name. None of the functions actually perform any locking.
pub struct OnceLock<T> {
    state: AtomicU8,
    value: UnsafeCell<MaybeUninit<T>>,
}

impl<T> OnceLock<T> {
    pub const fn new() -> Self {
        Self {
            state: AtomicU8::new(UNINITIALIZED),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    pub fn get(&self) -> Option<&T> {
        let state = self.state.load(Ordering::Acquire);
        if state == INITIALIZED {
            Some(unsafe {
                // SAFETY: We checked the state to make sure that the value has
                // been initialized.
                (*self.value.get()).assume_init_ref()
            })
        } else {
            None
        }
    }

    pub fn set(&self, val: T) -> Result<(), T> {
        // Try to acquire the rights to initialize the value.
        let res = self.state.compare_exchange(
            UNINITIALIZED,
            INITIALIZING,
            Ordering::Relaxed,
            Ordering::Relaxed,
        );

        if res.is_ok() {
            unsafe {
                // SAFETY: Only one thread can have it's compare-exchange
                // succeed, so that thread has unique ownership over the value.
                (*self.value.get()).write(val);
            }
            self.state.store(INITIALIZED, Ordering::Release);
            Ok(())
        } else {
            Err(val)
        }
    }
}

unsafe impl<T: Send> Send for OnceLock<T> {}
unsafe impl<T: Send + Sync> Sync for OnceLock<T> {}

impl<T> Default for OnceLock<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Debug for OnceLock<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("OnceLock").field(&self.get()).finish()
    }
}

impl<T> Drop for OnceLock<T> {
    fn drop(&mut self) {
        if *self.state.get_mut() == INITIALIZED {
            unsafe {
                // SAFETY: We checked the state to make sure that the value has
                // been initialized.
                self.value.get().drop_in_place();
            }
        }
    }
}

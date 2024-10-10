// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::error::SvsmError;
use crate::sev::ghcb::{GhcbPage, GHCB};
use core::cell::{Ref, RefCell};

static mut GHCB: RefCell<Option<GhcbPage>> = RefCell::new(None);

/// Sets up the CPU-local GHCB page.
pub fn setup_ghcb() -> Result<(), SvsmError> {
    let page = GhcbPage::new()?;
    let mut guard = unsafe {
        // FIXME: This is not safe.
        GHCB.borrow_mut()
    };
    assert!(guard.is_none(), "Attempted to reinitialize the GHCB");
    *guard = Some(page);
    Ok(())
}

/// Registers an already set up GHCB page for this CPU.
///
/// # Panics
///
/// Panics if the GHCB for this CPU has not been set up via [`setup_ghcb()`].
pub fn register_ghcb() -> Result<(), SvsmError> {
    current_ghcb().register()
}

/// Gets the GHCB for this CPU.
///
/// # Panics
///
/// Panics if the GHCB for this CPU has not been set up via [`setup_ghcb()`].
pub fn current_ghcb() -> Ref<'static, GHCB> {
    let guard = unsafe {
        // FIXME: This is not safe.
        GHCB.borrow()
    };
    Ref::map(guard, |a| &**a.as_ref().unwrap())
}

/// Release the GHCB.
///
/// # Safety
///
/// The caller must ensure that the GHCB is never used again.
pub unsafe fn shutdown_ghcb() {
    let mut guard = unsafe {
        // FIXME: This is not safe.
        GHCB.borrow_mut()
    };
    guard.take();
}

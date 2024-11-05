// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Authors: Joerg Roedel <jroedel@suse.de>

use crate::platform::SVSM_PLATFORM;

#[no_mangle]
pub extern "C" fn common_isr_handler(_vector: usize) {
    // Interrupt injection requests currently require no processing; they occur
    // simply to ensure an exit from the guest.

    // Treat any unhandled interrupt as a spurious interrupt.
    SVSM_PLATFORM.eoi();
}

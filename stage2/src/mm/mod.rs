// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

pub mod address_space;
pub mod alloc;
pub mod guestmem;
pub mod page_visibility;
mod pagebox;
pub mod pagetable;
pub mod validate;
pub mod virtualrange;
pub mod vm;

pub use address_space::*;
pub use guestmem::GuestPtr;
pub use pagebox::*;

pub use pagetable::PageTablePart;

pub use alloc::{allocate_file_page, PageRef};

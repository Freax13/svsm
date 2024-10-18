// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use core::num::NonZeroU8;

// IST offsets
pub const IST_DF: NonZeroU8 = unsafe { NonZeroU8::new_unchecked(1) };

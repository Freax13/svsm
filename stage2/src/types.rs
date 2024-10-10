// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::error::SvsmError;

pub const PAGE_SHIFT: usize = 12;
pub const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
pub const PAGE_SIZE_2M: usize = PAGE_SIZE * 512;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PageSize {
    Regular,
    Huge,
}

impl From<PageSize> for usize {
    fn from(psize: PageSize) -> Self {
        match psize {
            PageSize::Regular => PAGE_SIZE,
            PageSize::Huge => PAGE_SIZE_2M,
        }
    }
}

#[allow(clippy::identity_op)]
pub const SVSM_CS: u16 = 1 * 8;
pub const SVSM_DS: u16 = 2 * 8;

/// Length in byte which represents maximum 8 bytes(u64)
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub enum Bytes {
    #[default]
    Zero,
    One,
    Two,
    Four = 4,
    Eight = 8,
}

impl Bytes {
    pub fn mask(&self) -> u64 {
        match self {
            Bytes::Zero => 0,
            Bytes::One => (1 << 8) - 1,
            Bytes::Two => (1 << 16) - 1,
            Bytes::Four => (1 << 32) - 1,
            Bytes::Eight => u64::MAX,
        }
    }
}

impl TryFrom<usize> for Bytes {
    type Error = SvsmError;

    fn try_from(val: usize) -> Result<Bytes, Self::Error> {
        match val {
            0 => Ok(Bytes::Zero),
            1 => Ok(Bytes::One),
            2 => Ok(Bytes::Two),
            4 => Ok(Bytes::Four),
            8 => Ok(Bytes::Eight),
            _ => Err(SvsmError::InvalidBytes),
        }
    }
}

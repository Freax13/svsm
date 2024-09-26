// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::error::SvsmError;

use core::fmt;
use core::str::FromStr;

fn from_hex(c: char) -> Result<u8, SvsmError> {
    match c.to_digit(16) {
        Some(d) => Ok(d as u8),
        None => Err(SvsmError::Firmware),
    }
}

#[derive(Copy, Clone, Debug)]
struct Uuid {
    data: [u8; 16],
}

impl Uuid {
    pub const fn new() -> Self {
        Uuid { data: [0; 16] }
    }
}

impl TryFrom<&[u8]> for Uuid {
    type Error = ();
    fn try_from(mem: &[u8]) -> Result<Self, Self::Error> {
        let arr: &[u8; 16] = mem.try_into().map_err(|_| ())?;
        Ok(Self::from(arr))
    }
}

impl From<&[u8; 16]> for Uuid {
    fn from(mem: &[u8; 16]) -> Self {
        Self {
            data: [
                mem[3], mem[2], mem[1], mem[0], mem[5], mem[4], mem[7], mem[6], mem[8], mem[9],
                mem[10], mem[11], mem[12], mem[13], mem[14], mem[15],
            ],
        }
    }
}

impl FromStr for Uuid {
    type Err = SvsmError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut uuid = Uuid::new();
        let mut buf: u8 = 0;
        let mut index = 0;

        for c in s.chars() {
            if !c.is_ascii_hexdigit() {
                continue;
            }

            if (index % 2) == 0 {
                buf = from_hex(c)? << 4;
            } else {
                buf |= from_hex(c)?;
                let i = index / 2;
                if i >= 16 {
                    break;
                }
                uuid.data[i] = buf;
            }

            index += 1;
        }

        Ok(uuid)
    }
}

impl PartialEq for Uuid {
    fn eq(&self, other: &Self) -> bool {
        self.data.iter().zip(&other.data).all(|(a, b)| a == b)
    }
}

impl fmt::Display for Uuid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for i in 0..16 {
            write!(f, "{:02x}", self.data[i])?;
            if i == 3 || i == 5 || i == 7 || i == 9 {
                write!(f, "-")?;
            }
        }
        Ok(())
    }
}

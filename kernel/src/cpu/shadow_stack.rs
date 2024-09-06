// SPDX-License-Identifier: MIT OR Apache-2.0

use core::{arch::asm, num::NonZeroUsize};

use bitflags::bitflags;

use crate::{
    address::{Address, VirtAddr},
    cpu::{
        control_regs::{write_cr4, CR4Flags},
        percpu::this_cpu,
    },
    error::SvsmError,
    mm::PageBox,
};

use super::{control_regs::read_cr4, msr::read_msr};

pub const S_CET: u32 = 0x6a2;

pub const MODE_64BIT: usize = 1;

#[macro_export]
macro_rules! enable2 {
    ($bsp_percpu:ident) => {{
        use core::{arch::asm, num::NonZeroUsize};

        use bitflags::bitflags;

        use crate::{
            shadow_stack::{SCetFlags,S_CET, MODE_64BIT}
        };
        use svsm::address::Address;use svsm::cpu::control_regs::write_cr4;
        use svsm::cpu::control_regs::CR4Flags;
        use svsm::cpu::control_regs::read_cr4;

        let token_addr = $bsp_percpu.get_top_of_shadow_stack();

        // Enable CET in CR4.
        let mut cr4 = read_cr4();
        assert!(!cr4.contains(CR4Flags::CET), "CET is already enabled");
        cr4 |= CR4Flags::CET;
        write_cr4(cr4);

        // Read the return address to `svsm_start`. We need to put this address on
        // the new shadow stack. Note that `svsm_start` itself never returns, so we
        // don't need to put more return addresses on the shadow stack.
        let mut rip: usize;
        unsafe {
            asm!(
                "mov {}, [rbp + 8]",
                out(reg) rip,
            );
        };

        // Enable the shadow stack.
        unsafe {
            asm!(
                // Enable shadow stacks.
                "wrmsr",

                "wrssq [{token_addr}], {token_val}",
                // Load the shadow stack.
                "rstorssp [{token_addr}]",
                in("ecx") S_CET,
                in("edx") 0,
                in("eax") SCetFlags::SH_STK_EN.bits() | SCetFlags::WR_SHSTK_EN.bits(),
                token_addr = in(reg) token_addr.bits(),
                token_val = in(reg) token_addr.bits() + 8 + MODE_64BIT,
                options(nostack, readonly),
            );
        }
    }};
}

pub(crate) use enable2;

#[derive(Debug, Clone, Copy)]
pub enum ShadowStackToken {
    Restore,
    Supervisor,
}

/// Allocate a shadow stack and optionally place a return address and shadow
/// stack return token on it.
pub fn allocate_shadow_stack(
    token: Option<ShadowStackToken>,
    rip: Option<usize>,
) -> Result<VirtAddr, SvsmError> {
    let shadow_stack = PageBox::try_new_slice(0usize, NonZeroUsize::new(512).unwrap())?;
    let start_addr = shadow_stack.vaddr();
    let shadow_stack = PageBox::leak(shadow_stack);

    let chunk = shadow_stack.last_chunk_mut::<3>().unwrap();
    let token_addr = VirtAddr::from(&chunk[0] as *const _);

    // Optionally place a shadow stack token.
    if let Some(token) = token {
        let value = match token {
            ShadowStackToken::Restore => (token_addr + 8).bits() + MODE_64BIT,
            ShadowStackToken::Supervisor => token_addr.bits(),
        };
        chunk[0] = value;
    }

    // Optionally place a return address.
    if let Some(rip) = rip {
        chunk[1] = rip;
    }

    chunk[2] = (token_addr + 24).bits() + MODE_64BIT;

    this_cpu()
        .get_pgtable()
        .set_shadow_stack_4k(start_addr)
        .expect("Failed to remap shared page in page tables");

    Ok(token_addr)
}

pub fn read_s_cet() -> SCetFlags {
    SCetFlags::from_bits_retain(read_msr(S_CET))
}

bitflags! {
    pub struct SCetFlags: u64 {
        const SH_STK_EN = 1 << 0; // Enables the shadow stacks
        const WR_SHSTK_EN = 1 << 1; // Enables the WRSS instruction
    }
}

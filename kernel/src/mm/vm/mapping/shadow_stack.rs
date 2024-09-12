// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    address::{Address, PhysAddr, VirtAddr},
    cpu::shadow_stack,
    error::SvsmError,
    mm::{allocate_file_page_ref, pagetable::PTEntryFlags, vm::VirtualMapping, PageRef, PAGE_SIZE},
};

#[derive(Debug)]
pub enum ShadowStackInit {
    /// The initial shadow stack used by a CPU.
    ///
    /// This won't place any tokens on the shadow stack.
    Init,
    /// A shadow stack to be used during normal execution of a task.
    ///
    /// This will create a shadow stack with a shadow stack restore token.
    Normal {
        /// The address instruction that will be executed by the task.
        first_return: usize,
    },
    /// A shadow stack to be used for exception handling (either in PL0_SSP or
    /// in the ISST).
    ///
    /// This will create a shadow stack with a supervisor shadow stack token.
    Exception,
}

/// Mapping to be used as a kernel stack. This maps a stack including guard
/// pages at the top and bottom.
#[derive(Debug)]
pub struct VMKernelShadowStack {
    page: PageRef,
}

impl VMKernelShadowStack {
    /// Create a new [`VMKernelStack`] with the default size. This function
    /// will already allocate the backing pages for the stack.
    ///
    /// # Returns
    ///
    /// Initialized shadow stack & initial SSP value on success, Err(SvsmError::Mem) on error
    pub fn new(base: VirtAddr, init: ShadowStackInit) -> Result<(Self, VirtAddr), SvsmError> {
        let mut page = allocate_file_page_ref()?;
        let buffer = page.as_mut();

        // Initialize the shadow stack.
        let chunk = buffer.last_chunk_mut::<24>().unwrap();
        let ssp = match init {
            ShadowStackInit::Normal { first_return } => {
                let (token_bytes, rest) = chunk.split_at_mut(8);
                let (rip_bytes, _) = rest.split_at_mut(8);

                // Create a shadow stack restore token.
                let token_addr = base + PAGE_SIZE - 24;
                let token = (token_addr + 8).bits() + shadow_stack::MODE_64BIT;
                token_bytes.copy_from_slice(&token.to_ne_bytes());

                rip_bytes.copy_from_slice(&first_return.to_ne_bytes());

                token_addr
            }
            ShadowStackInit::Exception => {
                let (_, rest) = chunk.split_at_mut(8);
                let (token_bytes, _) = rest.split_at_mut(8);

                // Create a supervisor shadow stack token.
                let token_addr = base + PAGE_SIZE - 16;
                let token = token_addr.bits();
                token_bytes.copy_from_slice(&token.to_ne_bytes());

                token_addr
            }
            ShadowStackInit::Init => base + PAGE_SIZE - 8,
        };

        // Place a shadow stack restore token at the end of the shadow stack.
        // See the comment on CONTEXT_SWITCH_RESTORE_TOKEN for why this is
        // necessary.
        let token_bytes = buffer.last_chunk_mut::<8>().unwrap();
        let token_addr = base + PAGE_SIZE - 8;
        let token = (token_addr + 8).bits() + shadow_stack::MODE_64BIT;
        token_bytes.copy_from_slice(&token.to_ne_bytes());

        Ok((VMKernelShadowStack { page }, ssp))
    }
}

impl VirtualMapping for VMKernelShadowStack {
    fn mapping_size(&self) -> usize {
        PAGE_SIZE
    }

    fn map(&self, offset: usize) -> Option<PhysAddr> {
        assert_eq!(offset, 0);
        Some(self.page.phys_addr())
    }

    fn pt_flags(&self, _offset: usize) -> PTEntryFlags {
        // The CPU requires shadow stacks to be dirty and not writable.
        PTEntryFlags::NX | PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY
    }
}

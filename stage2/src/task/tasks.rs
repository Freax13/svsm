// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Roy Hopkins <rhopkins@suse.de>

extern crate alloc;

use alloc::collections::btree_map::BTreeMap;
use alloc::sync::Arc;
use core::fmt;

use crate::address::VirtAddr;
use crate::cpu::sse::sse_restore_context;
use crate::cpu::{irqs_enable, X86GeneralRegs};
use crate::error::SvsmError;
use crate::locking::{RWLock, SpinLock};
use crate::mm::pagetable::PageTable;
use crate::mm::vm::VMR;
use crate::mm::PageBox;
use crate::mm::{SVSM_PERTASK_BASE, SVSM_PERTASK_END, USER_MEM_END, USER_MEM_START};
use crate::syscall::{Obj, ObjError, ObjHandle};
use crate::utils::MemoryRegion;
use intrusive_collections::{intrusive_adapter, LinkedListAtomicLink};

#[derive(PartialEq, Debug, Copy, Clone, Default)]
pub enum TaskState {
    RUNNING,
    BLOCKED,
    #[default]
    TERMINATED,
}

#[derive(Clone, Copy, Debug)]
pub enum TaskError {
    // Attempt to close a non-terminated task
    NotTerminated,
    // A closed task could not be removed from the task list
    CloseFailed,
}

impl From<TaskError> for SvsmError {
    fn from(e: TaskError) -> Self {
        Self::Task(e)
    }
}

#[repr(C)]
#[derive(Default, Debug, Clone, Copy)]
pub struct TaskContext {
    pub rsp: u64,
    pub regs: X86GeneralRegs,
    pub flags: u64,
    pub ret_addr: u64,
}

#[repr(C)]
struct TaskSchedState {
    /// Whether this is an idle task
    idle_task: bool,

    /// Current state of the task
    state: TaskState,

    /// CPU this task is currently assigned to
    cpu: u32,
}

impl TaskSchedState {
    pub fn panic_on_idle(&mut self, msg: &str) -> &mut Self {
        if self.idle_task {
            panic!("{}", msg);
        }
        self
    }
}

pub struct Task {
    pub rsp: u64,

    /// XSave area
    pub xsa: PageBox<[u8]>,

    pub stack_bounds: MemoryRegion<VirtAddr>,

    /// Page table that is loaded when the task is scheduled
    pub page_table: SpinLock<PageBox<PageTable>>,

    /// Task virtual memory range for use at CPL 3 - None for kernel tasks
    vm_user_range: Option<VMR>,

    /// State relevant for scheduler
    sched_state: RWLock<TaskSchedState>,

    /// ID of the task
    id: u32,

    /// Link to global task list
    list_link: LinkedListAtomicLink,

    /// Link to scheduler run queue
    runlist_link: LinkedListAtomicLink,

    /// Objects shared among threads within the same process
    objs: Arc<RWLock<BTreeMap<ObjHandle, Arc<dyn Obj>>>>,
}

// SAFETY: Send + Sync is required for Arc<Task> to implement Send. All members
// of  `Task` are Send + Sync except for the intrusive_collection links, which
// are only Send. The only access to these is via the intrusive_adapter!
// generated code which does not use them concurrently across threads.
unsafe impl Sync for Task {}

pub type TaskPointer = Arc<Task>;

intrusive_adapter!(pub TaskRunListAdapter = TaskPointer: Task { runlist_link: LinkedListAtomicLink });
intrusive_adapter!(pub TaskListAdapter = TaskPointer: Task { list_link: LinkedListAtomicLink });

impl PartialEq for Task {
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self, other)
    }
}

impl fmt::Debug for Task {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Task")
            .field("rsp", &self.rsp)
            .field("state", &self.sched_state.lock_read().state)
            .field("id", &self.id)
            .finish()
    }
}

impl Task {
    pub fn stack_bounds(&self) -> MemoryRegion<VirtAddr> {
        self.stack_bounds
    }

    pub fn set_task_terminated(&self) {
        self.sched_state
            .lock_write()
            .panic_on_idle("Trying to terminate idle task")
            .state = TaskState::TERMINATED;
    }

    pub fn is_running(&self) -> bool {
        self.sched_state.lock_read().state == TaskState::RUNNING
    }

    pub fn is_terminated(&self) -> bool {
        self.sched_state.lock_read().state == TaskState::TERMINATED
    }

    pub fn is_idle_task(&self) -> bool {
        self.sched_state.lock_read().idle_task
    }

    pub fn update_cpu(&self, new_cpu: u32) -> u32 {
        let mut state = self.sched_state.lock_write();
        let old_cpu = state.cpu;
        state.cpu = new_cpu;
        old_cpu
    }

    pub fn fault(&self, vaddr: VirtAddr, write: bool) -> Result<(), SvsmError> {
        if vaddr >= USER_MEM_START && vaddr < USER_MEM_END && self.vm_user_range.is_some() {
            let vmr = self.vm_user_range.as_ref().unwrap();
            let mut pgtbl = self.page_table.lock();
            vmr.populate_addr(&mut pgtbl, vaddr);
            vmr.handle_page_fault(vaddr, write)?;
            Ok(())
        } else {
            Err(SvsmError::Mem)
        }
    }

    /// Adds an object to the current task.
    ///
    /// # Arguments
    ///
    /// * `obj` - The object to be added.
    ///
    /// # Returns
    ///
    /// * `Result<ObjHandle, SvsmError>` - Returns the object handle for the object
    ///   to be added if successful, or an `SvsmError` on failure.
    ///
    /// # Errors
    ///
    /// This function will return an error if allocating the object handle fails.
    pub fn add_obj(&self, obj: Arc<dyn Obj>) -> Result<ObjHandle, SvsmError> {
        let mut objs = self.objs.lock_write();
        let last_key = objs
            .keys()
            .last()
            .map_or(Some(0), |k| u32::from(*k).checked_add(1))
            .ok_or(SvsmError::from(ObjError::InvalidHandle))?;
        let id = ObjHandle::new(if last_key != objs.len() as u32 {
            objs.keys()
                .enumerate()
                .find(|(i, &key)| *i as u32 != u32::from(key))
                .unwrap()
                .0 as u32
        } else {
            last_key
        });

        objs.insert(id, obj);

        Ok(id)
    }

    /// Removes an object from the current task.
    ///
    /// # Arguments
    ///
    /// * `id` - The ObjHandle for the object to be removed.
    ///
    /// # Returns
    ///
    /// * `Result<Arc<dyn Obj>>, SvsmError>` - Returns the removed `Arc<dyn Obj>`
    ///   on success, or an `SvsmError` on failure.
    ///
    /// # Errors
    ///
    /// This function will return an error if the object handle id does not
    /// exist in the current task.
    pub fn remove_obj(&self, id: ObjHandle) -> Result<Arc<dyn Obj>, SvsmError> {
        self.objs
            .lock_write()
            .remove(&id)
            .ok_or(ObjError::NotFound.into())
    }

    /// Retrieves an object from the current task.
    ///
    /// # Arguments
    ///
    /// * `id` - The ObjHandle for the object to be retrieved.
    ///
    /// # Returns
    ///
    /// * `Result<Arc<dyn Obj>>, SvsmError>` - Returns the `Arc<dyn Obj>` on
    ///   success, or an `SvsmError` on failure.
    ///
    /// # Errors
    ///
    /// This function will return an error if the object handle id does not exist
    /// in the current task.
    pub fn get_obj(&self, id: ObjHandle) -> Result<Arc<dyn Obj>, SvsmError> {
        self.objs
            .lock_read()
            .get(&id)
            .cloned()
            .ok_or(ObjError::NotFound.into())
    }
}

pub fn is_task_fault(vaddr: VirtAddr) -> bool {
    (vaddr >= USER_MEM_START && vaddr < USER_MEM_END)
        || (vaddr >= SVSM_PERTASK_BASE && vaddr < SVSM_PERTASK_END)
}

/// Runs the first time a new task is scheduled, in the context of the new
/// task. Any first-time initialization and setup work for a new task that
/// needs to happen in its context must be done here.
#[no_mangle]
fn setup_new_task(xsa_addr: u64) {
    // Re-enable IRQs here, as they are still disabled from the
    // schedule()/sched_init() functions. After the context switch the IrqGuard
    // from the previous task is not dropped, which causes IRQs to stay
    // disabled in the new task.
    // This only needs to be done for the first time a task runs. Any
    // subsequent task switches will go through schedule() and there the guard
    // is dropped, re-enabling IRQs.

    // SAFETY: Safe because this matches the IrqGuard drop in
    // schedule()/schedule_init(). See description above.
    unsafe {
        irqs_enable();
        sse_restore_context(xsa_addr);
    }
}

#[cfg(test)]
mod tests {
    use core::arch::asm;
    use core::arch::global_asm;

    #[test]
    #[cfg_attr(not(test_in_svsm), ignore = "Can only be run inside guest")]
    fn test_media_and_x87_instructions() {
        let ret: u64;
        unsafe {
            asm!("call test_fpu", out("rax") ret, options(att_syntax));
        }

        assert_eq!(ret, 0);
    }

    global_asm!(
        r#"
    .text
    test_fpu:
        movq $0x3ff, %rax
        shl $52, %rax
        // rax contains 1 in Double Precison FP representation
        movd %rax, %xmm1
        movapd %xmm1, %xmm3

        movq $0x400, %rax
        shl $52, %rax
        // rax contains 2 in Double Precison FP representation
        movd %rax, %xmm2

        divsd %xmm2, %xmm3
        movq $0, %rax
        ret
        "#,
        options(att_syntax)
    );

    global_asm!(
        r#"
    .text
    check_fpu:
        movq $1, %rax
        movq $0x3ff, %rbx
        shl $52, %rbx
        // rbx contains 1 in Double Precison FP representation
        movd %rbx, %xmm4
        movapd %xmm4, %xmm6
        comisd %xmm4, %xmm1
        jnz 1f

        movq $0x400, %rbx
        shl $52, %rbx
        // rbx contains 2 in Double Precison FP representation
        movd %rbx, %xmm5
        comisd %xmm5, %xmm2
        jnz 1f

        divsd %xmm5, %xmm6
        comisd %xmm6, %xmm3
        jnz 1f
        movq $0, %rax
    1:
        ret
        "#,
        options(att_syntax)
    );

    global_asm!(
        r#"
    .text
    alter_fpu:
        movq $0x400, %rax
        shl $52, %rax
        // rax contains 2 in Double Precison FP representation
        movd %rax, %xmm1
        movapd %xmm1, %xmm3

        movq $0x3ff, %rax
        shl $52, %rax
        // rax contains 1 in Double Precison FP representation
        movd %rax, %xmm2
        divsd %xmm3, %xmm2
        movq $0, %rax
        ret
        "#,
        options(att_syntax)
    );
}

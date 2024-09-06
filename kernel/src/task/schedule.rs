// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Roy Hopkins <rhopkins@suse.de>

//! Round-Robin scheduler implementation for COCONUT-SVSM
//!
//! This module implements a round-robin scheduler for cooperative multi-tasking.
//! It works by assigning a single owner for each struct [`Task`]. The owner
//! depends on the state of the task:
//!
//! * [`RUNNING`] A task in running state is owned by the [`RunQueue`] and either
//!    stored in the `run_list` (when the task is not actively running) or in
//!    `current_task` when it is scheduled on the CPU.
//! * [`BLOCKED`] A task in this state is waiting for an event to become runnable
//!    again. It is owned by a wait object when in this state.
//! * [`TERMINATED`] The task is about to be destroyed and owned by the [`RunQueue`].
//!
//! The scheduler is cooperative. A task runs until it voluntarily calls the
//! [`schedule()`] function.
//!
//! Only when a task is in [`RUNNING`] or [`TERMINATED`] state it is assigned to a
//! specific CPU. Tasks in the [`BLOCKED`] state have no CPU assigned and will run
//! on the CPU where their event is triggered that makes them [`RUNNING`] again.
//!
//! [`RUNNING`]: super::tasks::TaskState::RUNNING
//! [`BLOCKED`]: super::tasks::TaskState::BLOCKED
//! [`TERMINATED`]: super::tasks::TaskState::TERMINATED

extern crate alloc;

use super::INITIAL_TASK_ID;
use super::{Task, TaskListAdapter, TaskPointer, TaskRunListAdapter};
use crate::address::Address;
use crate::cpu::msr::write_msr;
use crate::cpu::percpu::{irq_nesting_count, this_cpu};
use crate::cpu::IrqGuard;
use crate::error::SvsmError;
use crate::locking::SpinLock;
use alloc::sync::Arc;
use core::arch::{asm, global_asm};
use core::cell::OnceCell;
use core::ptr::null_mut;
use intrusive_collections::LinkedList;

/// A RunQueue implementation that uses an RBTree to efficiently sort the priority
/// of tasks within the queue.
#[derive(Debug, Default)]
pub struct RunQueue {
    /// Linked list with runable tasks
    run_list: LinkedList<TaskRunListAdapter>,

    /// Pointer to currently running task
    current_task: Option<TaskPointer>,

    /// Idle task - runs when there is no other runnable task
    idle_task: OnceCell<TaskPointer>,

    /// Temporary storage for tasks which are about to be terminated
    terminated_task: Option<TaskPointer>,
}

impl RunQueue {
    /// Create a new runqueue for an id. The id would normally be set
    /// to the APIC ID of the CPU that owns the runqueue and is used to
    /// determine the affinity of tasks.
    pub fn new() -> Self {
        Self {
            run_list: LinkedList::new(TaskRunListAdapter::new()),
            current_task: None,
            idle_task: OnceCell::new(),
            terminated_task: None,
        }
    }

    /// Find the next task to run, which is either the task at the front of the
    /// run_list or the idle task, if the run_list is empty.
    ///
    /// # Returns
    ///
    /// Pointer to next task to run
    ///
    /// # Panics
    ///
    /// Panics if there are no tasks to run and no idle task has been
    /// allocated via [`set_idle_task()`](Self::set_idle_task).
    fn get_next_task(&mut self) -> TaskPointer {
        self.run_list
            .pop_front()
            .unwrap_or_else(|| self.idle_task.get().unwrap().clone())
    }

    /// Update state before a task is scheduled out. Non-idle tasks in RUNNING
    /// state will be put at the end of the run_list. Terminated tasks will be
    /// stored in the terminated_task field of the RunQueue and be destroyed
    /// after the task-switch.
    fn handle_task(&mut self, task: TaskPointer) {
        if task.is_running() && !task.is_idle_task() {
            self.run_list.push_back(task);
        } else if task.is_terminated() {
            self.terminated_task = Some(task);
        }
    }

    /// Initialized the scheduler for this (RunQueue)[RunQueue]. This method is
    /// called on the very first scheduling event when there is no current task
    /// yet.
    ///
    /// # Returns
    ///
    /// [TaskPointer] to the first task to run
    pub fn schedule_init(&mut self) -> TaskPointer {
        let task = self.get_next_task();
        self.current_task = Some(task.clone());
        task
    }

    /// Prepares a task switch. The function checks if a task switch needs to
    /// be done and return pointers to the current and next task. It will
    /// also call `handle_task()` on the current task in case a task-switch
    /// is requested.
    ///
    /// # Returns
    ///
    /// `None` when no task-switch is needed.
    /// `Some` with current and next task in case a task-switch is required.
    ///
    /// # Panics
    ///
    /// Panics if there is no current task.
    pub fn schedule_prepare(&mut self) -> Option<(TaskPointer, TaskPointer)> {
        // Remove current and put it back into the RunQueue in case it is still
        // runnable. This is important to make sure the last runnable task
        // keeps running, even if it calls schedule()
        let current = self.current_task.take().unwrap();
        self.handle_task(current.clone());

        // Get next task and update current_task state
        let next = self.get_next_task();
        self.current_task = Some(next.clone());

        // Check if task switch is needed
        if current != next {
            Some((current, next))
        } else {
            None
        }
    }

    pub fn current_task_id(&self) -> u32 {
        self.current_task
            .as_ref()
            .map_or(INITIAL_TASK_ID, |t| t.get_task_id())
    }

    /// Sets the idle task for this RunQueue. This function sets a
    /// OnceCell at the end and can thus be only called once.
    ///
    /// # Returns
    ///
    /// Ok(()) on success, SvsmError on failure
    ///
    /// # Panics
    ///
    /// Panics if the idle task was already set.
    pub fn set_idle_task(&self, task: TaskPointer) {
        task.set_idle_task();

        // Add idle task to global task list
        TASKLIST.lock().list().push_front(task.clone());

        self.idle_task
            .set(task)
            .expect("Idle task already allocated");
    }

    /// Gets a pointer to the current task
    ///
    /// # Panics
    ///
    /// Panics if there is no current task.
    pub fn current_task(&self) -> TaskPointer {
        self.current_task.as_ref().unwrap().clone()
    }
}

/// Global task list
/// This contains every task regardless of affinity or run state.
#[derive(Debug, Default)]
pub struct TaskList {
    list: Option<LinkedList<TaskListAdapter>>,
}

impl TaskList {
    pub const fn new() -> Self {
        Self { list: None }
    }

    pub fn list(&mut self) -> &mut LinkedList<TaskListAdapter> {
        self.list
            .get_or_insert_with(|| LinkedList::new(TaskListAdapter::new()))
    }

    pub fn get_task(&self, id: u32) -> Option<TaskPointer> {
        let task_list = &self.list.as_ref()?;
        let mut cursor = task_list.front();
        while let Some(task) = cursor.get() {
            if task.get_task_id() == id {
                return cursor.clone_pointer();
            }
            cursor.move_next();
        }
        None
    }

    fn terminate(&mut self, task: TaskPointer) {
        // Set the task state as terminated. If the task being terminated is the
        // current task then the task context will still need to be in scope until
        // the next schedule() has completed. Schedule will keep a reference to this
        // task until some time after the context switch.
        task.set_task_terminated();
        let mut cursor = unsafe { self.list().cursor_mut_from_ptr(task.as_ref()) };
        cursor.remove();
    }
}

pub static TASKLIST: SpinLock<TaskList> = SpinLock::new(TaskList::new());

pub fn create_kernel_task(entry: extern "C" fn()) -> Result<TaskPointer, SvsmError> {
    let cpu = this_cpu();
    let task = Task::create(cpu, entry)?;
    TASKLIST.lock().list().push_back(task.clone());

    // Put task on the runqueue of this CPU
    cpu.runqueue().lock_write().handle_task(task.clone());

    schedule();

    Ok(task)
}

pub fn create_user_task(user_entry: usize) -> Result<TaskPointer, SvsmError> {
    let cpu = this_cpu();
    let task = Task::create_user(cpu, user_entry)?;
    TASKLIST.lock().list().push_back(task.clone());

    // Put task on the runqueue of this CPU
    cpu.runqueue().lock_write().handle_task(task.clone());

    Ok(task)
}

pub fn current_task() -> TaskPointer {
    this_cpu().current_task()
}

/// Check to see if the task scheduled on the current processor has the given id
pub fn is_current_task(id: u32) -> bool {
    match &this_cpu().runqueue().lock_read().current_task {
        Some(current_task) => current_task.get_task_id() == id,
        None => id == INITIAL_TASK_ID,
    }
}

/// Terminates the current task.
///
/// # Safety
///
/// This function must only be called after scheduling is initialized, otherwise it will panic.
pub unsafe fn current_task_terminated() {
    let cpu = this_cpu();
    let mut rq = cpu.runqueue().lock_write();
    let task_node = rq
        .current_task
        .as_mut()
        .expect("Task termination handler called when there is no current task");
    TASKLIST.lock().terminate(task_node.clone());
}

pub fn terminate() {
    // TODO: re-evaluate whether current_task_terminated() needs to be unsafe
    unsafe {
        current_task_terminated();
    }
    schedule();
}

// SAFETY: This function returns a raw pointer to a task. It is safe
// because this function is only used in the task switch code, which also only
// takes a single reference to the next and previous tasks. Also, this
// function works on an Arc, which ensures that only a single mutable reference
// can exist.
unsafe fn task_pointer(taskptr: TaskPointer) -> *const Task {
    Arc::as_ptr(&taskptr)
}

#[inline(always)]
unsafe fn switch_to(prev: *const Task, next: *const Task) {
    let cr3: u64 = unsafe { (*next).page_table.lock().cr3_value().bits() as u64 };

    // Switch to new task
    asm!(
        r#"
        call switch_context
        "#,
        in("rsi") prev as u64,
        in("rdi") next as u64,
        in("rdx") cr3,
        options(att_syntax));
}

/// Initializes the [RunQueue] on the current CPU. It will switch to the idle
/// task and initialize the current_task field of the RunQueue. After this
/// function has ran it is safe to call [`schedule()`] on the current CPU.
pub fn schedule_init() {
    unsafe {
        let guard = IrqGuard::new();
        let next = task_pointer(this_cpu().schedule_init());
        switch_to(null_mut(), next);
        drop(guard);
    }
}

fn preemption_checks() {
    assert!(irq_nesting_count() == 0);
}

/// Perform a task switch and hand the CPU over to the next task on the
/// run-list. In case the current task is terminated, it will be destroyed after
/// the switch to the next task.
pub fn schedule() {
    // check if preemption is safe
    preemption_checks();

    let guard = IrqGuard::new();

    let work = this_cpu().schedule_prepare();

    // !!! Runqueue lock must be release here !!!
    if let Some((current, next)) = work {
        // Update per-cpu mappings if needed
        let apic_id = this_cpu().get_apic_id();

        if next.update_cpu(apic_id) != apic_id {
            // Task has changed CPU, update per-cpu mappings
            let mut pt = next.page_table.lock();
            this_cpu().populate_page_table(&mut pt);
        }

        this_cpu().set_tss_rsp0(next.stack_bounds.end());
        write_msr(0x000006a4, next.exception_shadow_stack.bits() as u64);

        // Get task-pointers, consuming the Arcs and release their reference
        unsafe {
            let a = task_pointer(current);
            let b = task_pointer(next);

            // Switch tasks
            switch_to(a, b);
        }
    }

    drop(guard);

    // We're now in the context of the new task. If the previous task had terminated
    // then we can release it's reference here.
    let _ = this_cpu().runqueue().lock_write().terminated_task.take();
}

pub fn schedule_task(task: TaskPointer) {
    task.set_task_running();
    this_cpu().runqueue().lock_write().handle_task(task);
    schedule();
}

global_asm!(
    r#"
        .text

    switch_context:
        // Save the current context. The layout must match the TaskContext structure.
        pushfq
        pushq   %rax
        pushq   %rbx
        pushq   %rcx
        pushq   %rdx
        pushq   %rsi
        pushq   %rdi
        pushq   %rbp
        pushq   %r8
        pushq   %r9
        pushq   %r10
        pushq   %r11
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        pushq   %rsp

        // If `prev` is not null
        testq   %rsi, %rsi
        jz      1f

        // Save the current stack pointer
        movq    %rsp, (%rsi)

        // Save the current shadow stack pointer
        rdssp   %rax
        sub $8, %rax
        movq    %rax, 8(%rsi)

        // One interesting difference between the normal stack pointer and the
        // shadow stack pointer is how they can be switched: For the normal
        // stack pointer we just have to set RSP to a new value. This doesn't
        // work for SSP (the shadow stack pointer) because there's no way to
        // directly move a value into it. Instead we have use to the `rstorssp`
        // instruction. The key difference between this instruction and a
        // regular `mov` is that `rstorssp` expects a "shadow stack restore
        // token" to be at the top of the new stack (this is just a special
        // value that marks the top of a inactive shadow stack). This restore
        // shadow stack token can be written by executing `saveprevssp` after
        // switching to a new stack with `rstorssp`: `saveprevssp` atomically
        // pops the stack token of the new shadow stack and pushes it on the
        // previous shadow stack. This means that we have to execute both
        // `rstorssp` and `saveprevssp` every time we want to switch the shadow
        // stacks.
        // There's one major problem though: `saveprevssp` needs to access both
        // the previous and the new shadow stack, but we only map one shadow
        // stack into each task's page tables. If the page tables only have
        // access to one shadow stack, we can't execute `saveprevssp` and so we
        // we can't place a "shadow stack restore token" on the previous shadow
        // stack. If there's no "shadow stack restore token" on the previous
        // shadow stack that means we can't later restore this shadow stack.
        // We obviously want to do switch back to the shadow stack later though
        // so we need a work-around: We place a second "shadow stack restore
        // token" at a fixed address in both page tables. This allows us to do
        // the following:
        // 1. Switch to the shadow stack at the fixed address using `rstorssp`.
        // 2. Transfer the "shadow stack restore token" from the shadow stack 
        //    at the fixed address to the previous shadow stack by executing
        //    `saveprevssp`.
        // 3. Switch the page tables. This doesn't lead to problems with the
        //    shadow stack because is mapped into both page tables.
        // 4. Switch to the new shadow stack using `rstorssp`.
        // 5. Transfer the "shadow stack restore token" from the new shadow
        //    stack back to the shadow stacks at the fixed address by executing
        //    `saveprevssp`.
        // We just switched between two shadow stack tables in different page
        // tables :)
        // There's on remaining implementation detail: We talked about a
        // "shadow stack at a fixed address" and this might sound like it
        // requires us to map the same physical memory into both page tables,
        // but that's not actually the case: We just need some memory with the
        // correct flags in both page tables, the contents don't actually
        // matter because we only ever use it to store the "shadow stack
        // restore token". Notably because the "shadow stack restore token" is
        // popped off by the `saveprevssp` instruction before the page table
        // switch, the "shadow stack restore token" isn't even present during
        // page table switch and so the content at the address also doesn't
        // matter. All that we need is 8 bytes of available storage in both
        // page tables.
        // We use the last 8 bytes of the page containing the shadow stack.
        // This works because the shadow stack for each task is mapped at the
        // same location, so "the last 8 bytes of the page containing the
        // shadow stack" is fixed in practice.
        
        // Switch to a shadow stack that's valid in both page tables and move
        // the "shadow stack restore token" to the old shadow stack.
        or $0xfff, %rax
        sub $7, %rax
        rstorssp (%rax)
        saveprevssp

    1:
        // Switch to the new task state
        
        // Switch to the new task page tables
        mov     %rdx, %cr3

        // Switch to the new task shadow stack and move the "shadow stack
        // restore token" back.
        mov     8(%rdi), %rdx
        rstorssp (%rdx)
        saveprevssp

        // Switch to the new task stack
        movq    (%rdi), %rsp

        // We've already restored rsp
        addq        $8, %rsp

        // Restore the task context
        popq        %r15
        popq        %r14
        popq        %r13
        popq        %r12
        popq        %r11
        popq        %r10
        popq        %r9
        popq        %r8
        popq        %rbp
        popq        %rdi
        popq        %rsi
        popq        %rdx
        popq        %rcx
        popq        %rbx
        popq        %rax
        popfq

        ret
    "#,
    options(att_syntax)
);

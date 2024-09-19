// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

extern crate alloc;

use alloc::vec::Vec;
use core::iter::once;

use crate::acpi::tables::ACPICPUInfo;
use crate::cpu::percpu::{this_cpu, this_cpu_shared, PerCpu, PerCpuInfo, PERCPU_AREAS};
use crate::platform::SvsmPlatform;
use crate::platform::SVSM_PLATFORM;
use crate::requests::{request_loop, request_processing_main};
use crate::task::{create_kernel_task, schedule_init};
use crate::utils::immut_after_init::immut_after_init_set_multithreaded;

pub fn start_secondary_cpus(platform: &dyn SvsmPlatform, cpus: &[ACPICPUInfo]) {
    immut_after_init_set_multithreaded();

    // Allocate PerCpu structs for all APs.
    let per_cpus = cpus
        .iter()
        .filter(|c| c.apic_id != 0 && c.enabled)
        .map(|c| PerCpu::alloc(c.apic_id))
        .collect::<Result<Vec<_>, _>>()
        .expect("Failed to allocate PerCpus");

    // Collect all shared parts and make them globally available.
    let per_cpu_shareds = once(PerCpuInfo::new(0, this_cpu_shared()))
        .chain(
            per_cpus
                .iter()
                .copied()
                .map(|percpu| PerCpuInfo::new(percpu.get_apic_id(), percpu.shared())),
        )
        .collect();
    PERCPU_AREAS.set(per_cpu_shareds);

    // Launch the APs.
    for percpu in per_cpus.iter() {
        log::info!("Launching AP with APIC-ID {}", percpu.get_apic_id());

        let start_rip: u64 = (start_ap as *const u8) as u64;
        platform
            .start_cpu(percpu, start_rip)
            .expect("Failed to bring CPU online");

        let percpu_shared = percpu.shared();
        while !percpu_shared.is_online() {}
    }
    log::info!("Brought {} AP(s) online", per_cpus.len());
}

#[no_mangle]
fn start_ap() {
    this_cpu()
        .setup_on_cpu(SVSM_PLATFORM.as_dyn_ref())
        .expect("setup_on_cpu() failed");

    // Configure the #HV doorbell page as required.
    this_cpu()
        .configure_hv_doorbell()
        .expect("configure_hv_doorbell() failed");

    this_cpu()
        .setup_idle_task(ap_request_loop)
        .expect("Failed to allocated idle task for AP");

    // Send a life-sign
    log::info!("AP with APIC-ID {} is online", this_cpu().get_apic_id());

    // Set CPU online so that BSP can proceed
    this_cpu_shared().set_online();

    schedule_init();
}

#[no_mangle]
pub extern "C" fn ap_request_loop() {
    create_kernel_task(request_processing_main).expect("Failed to launch request processing task");
    request_loop();
    panic!("Returned from request_loop!");
}

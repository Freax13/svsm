// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::acpi::tables::ACPICPUInfo;
use crate::cpu::ghcb::current_ghcb;
use crate::cpu::percpu::{this_cpu_mut, PerCpu};
use crate::cpu::vmsa::init_svsm_vmsa;
use crate::requests::{request_loop, request_processing_main};
use crate::task::{create_kernel_task, schedule_init, TASK_FLAG_SHARE_PT};

fn start_cpu(apic_id: u32, vtom: u64) {
    unsafe {
        let start_rip: u64 = (start_ap as *const u8) as u64;
        let percpu = PerCpu::alloc(apic_id)
            .expect("Failed to allocate AP per-cpu data")
            .as_mut()
            .unwrap();

        percpu.setup().expect("Failed to setup AP per-cpu area");
        percpu
            .alloc_svsm_vmsa()
            .expect("Failed to allocate AP SVSM VMSA");

        let mut vmsa = percpu.get_svsm_vmsa().unwrap();
        init_svsm_vmsa(vmsa.vmsa(), vtom);
        percpu.prepare_svsm_vmsa(start_rip);

        let sev_features = vmsa.vmsa().sev_features;
        let vmsa_pa = vmsa.paddr;

        vmsa.vmsa().enable();
        current_ghcb()
            .ap_create(vmsa_pa, apic_id.into(), 0, sev_features)
            .expect("Failed to launch secondary CPU");
        loop {
            if percpu.is_online() {
                break;
            }
        }
    }
}

pub fn start_secondary_cpus(cpus: &[ACPICPUInfo], vtom: u64) {
    let mut count: usize = 0;
    for c in cpus.iter().filter(|c| c.apic_id != 0 && c.enabled) {
        log::info!("Launching AP with APIC-ID {}", c.apic_id);
        start_cpu(c.apic_id, vtom);
        count += 1;
    }
    log::info!("Brought {} AP(s) online", count);
}

#[no_mangle]
fn start_ap() {
    this_cpu_mut()
        .setup_on_cpu()
        .expect("setup_on_cpu() failed");

    this_cpu_mut()
        .setup_idle_task(ap_request_loop)
        .expect("Failed to allocated idle task for AP");

    // Send a life-sign
    log::info!("AP with APIC-ID {} is online", this_cpu_mut().get_apic_id());

    // Set CPU online so that BSP can proceed
    this_cpu_mut().set_online();

    schedule_init();
}

#[no_mangle]
pub extern "C" fn ap_request_loop() {
    create_kernel_task(request_processing_main, TASK_FLAG_SHARE_PT)
        .expect("Failed to launch request processing task");
    request_loop();
    panic!("Returned from request_loop!");
}
// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

fn main() {
    // Extra cfgs
    println!("cargo::rustc-check-cfg=cfg(fuzzing)");
    println!("cargo::rustc-check-cfg=cfg(test_in_svsm)");

    println!("cargo:rustc-link-arg=-nostdlib");
    println!("cargo:rustc-link-arg=--build-id=none");
    println!("cargo:rustc-link-arg=-Tstage2/src/stage2.lds");
    println!("cargo:rustc-link-arg=-no-pie");
    println!("cargo:rerun-if-changed=stage2/src/stage2.lds");
}

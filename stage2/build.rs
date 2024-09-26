// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

fn main() {
    println!("cargo:rustc-link-arg-bin=stage2=-nostdlib");
    println!("cargo:rustc-link-arg-bin=stage2=--build-id=none");
    println!("cargo:rustc-link-arg-bin=stage2=-Tstage2/src/stage2.lds");
    println!("cargo:rustc-link-arg-bin=stage2=-no-pie");
    println!("cargo:rerun-if-changed=stage2/src/stage2.lds");
}

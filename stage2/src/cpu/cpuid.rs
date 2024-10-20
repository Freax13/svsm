// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::utils::immut_after_init::ImmutAfterInitRef;
use cpuarch::snp_cpuid::SnpCpuidTable;

pub static CPUID_PAGE: ImmutAfterInitRef<'_, SnpCpuidTable> = ImmutAfterInitRef::uninit();

pub fn register_cpuid_table(table: &'static SnpCpuidTable) {
    CPUID_PAGE
        .init_from_ref(table)
        .expect("Could not initialize CPUID page");
}

// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

use crate::cpuid::CpuidResult;

const SNP_CPUID_MAX_COUNT: usize = 64;

#[derive(Copy, Clone, Default, Debug)]
#[repr(C, packed)]
pub struct SnpCpuidFn {
    pub eax_in: u32,
    pub ecx_in: u32,
    pub xcr0_in: u64,
    pub xss_in: u64,
    pub eax_out: u32,
    pub ebx_out: u32,
    pub ecx_out: u32,
    pub edx_out: u32,
    pub reserved_1: u64,
}

#[derive(Copy, Clone, Debug)]
#[repr(C, packed)]
pub struct SnpCpuidTable {
    pub count: u32,
    pub reserved_1: u32,
    pub reserved_2: u64,
    pub func: [SnpCpuidFn; SNP_CPUID_MAX_COUNT],
}

impl SnpCpuidTable {
    pub fn cpuid_table_raw(&self, eax: u32, ecx: u32, xcr0: u64, xss: u64) -> Option<CpuidResult> {
        let count: usize = self.count as usize;

        for i in 0..count {
            if eax == self.func[i].eax_in
                && ecx == self.func[i].ecx_in
                && xcr0 == self.func[i].xcr0_in
                && xss == self.func[i].xss_in
            {
                return Some(CpuidResult {
                    eax: self.func[i].eax_out,
                    ebx: self.func[i].ebx_out,
                    ecx: self.func[i].ecx_out,
                    edx: self.func[i].edx_out,
                });
            }
        }

        None
    }

    pub fn cpuid_table(&self, eax: u32) -> Option<CpuidResult> {
        self.cpuid_table_raw(eax, 0, 0, 0)
    }

    pub fn dump(&self) {
        let count = self.count as usize;

        log::trace!("CPUID Table entry count: {}", count);

        for i in 0..count {
            let eax_in = self.func[i].eax_in;
            let ecx_in = self.func[i].ecx_in;
            let xcr0_in = self.func[i].xcr0_in;
            let xss_in = self.func[i].xss_in;
            let eax_out = self.func[i].eax_out;
            let ebx_out = self.func[i].ebx_out;
            let ecx_out = self.func[i].ecx_out;
            let edx_out = self.func[i].edx_out;
            log::trace!("EAX_IN: {:#010x} ECX_IN: {:#010x} XCR0_IN: {:#010x} XSS_IN: {:#010x} EAX_OUT: {:#010x} EBX_OUT: {:#010x} ECX_OUT: {:#010x} EDX_OUT: {:#010x}",
                    eax_in, ecx_in, xcr0_in, xss_in, eax_out, ebx_out, ecx_out, edx_out);
        }
    }
}

impl Default for SnpCpuidTable {
    fn default() -> Self {
        SnpCpuidTable {
            count: Default::default(),
            reserved_1: Default::default(),
            reserved_2: Default::default(),
            func: [SnpCpuidFn::default(); SNP_CPUID_MAX_COUNT],
        }
    }
}

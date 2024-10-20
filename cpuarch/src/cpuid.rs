use core::arch::asm;

#[derive(Clone, Copy, Debug)]
pub struct CpuidResult {
    pub eax: u32,
    pub ebx: u32,
    pub ecx: u32,
    pub edx: u32,
}

impl CpuidResult {
    pub fn get(cpuid_fn: u32, cpuid_subfn: u32) -> Self {
        let mut result_eax: u32;
        let mut result_ebx: u32;
        let mut result_ecx: u32;
        let mut result_edx: u32;
        unsafe {
            asm!("push %rbx",
                 "cpuid",
                 "movl %ebx, %edi",
                 "pop %rbx",
                 in("eax") cpuid_fn,
                 in("ecx") cpuid_subfn,
                 lateout("eax") result_eax,
                 lateout("edi") result_ebx,
                 lateout("ecx") result_ecx,
                 lateout("edx") result_edx,
                 options(att_syntax));
        }
        Self {
            eax: result_eax,
            ebx: result_ebx,
            ecx: result_ecx,
            edx: result_edx,
        }
    }
}

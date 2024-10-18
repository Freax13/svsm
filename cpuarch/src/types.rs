pub const PAGE_SHIFT: usize = 12;
pub const PAGE_SHIFT_2M: usize = 21;
pub const PAGE_SHIFT_1G: usize = 30;
pub const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
pub const PAGE_SIZE_2M: usize = 1 << PAGE_SHIFT_2M;
pub const PAGE_SIZE_1G: usize = 1 << PAGE_SHIFT_1G;

#[allow(clippy::identity_op)]
pub const SVSM_CS: u16 = 1 * 8;
pub const SVSM_DS: u16 = 2 * 8;
pub const SVSM_USER_CS: u16 = 3 * 8;
pub const SVSM_USER_DS: u16 = 4 * 8;
pub const SVSM_TSS: u16 = 6 * 8;

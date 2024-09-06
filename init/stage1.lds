/* SPDX-License-Identifier: MIT OR Apache-2.0 */

/*
 * Copyright (c) 2022-2023 SUSE LLC
 *
 * Author: Joerg Roedel <jroedel@suse.de>
 */

OUTPUT_ARCH(i386:x86-64)

SECTIONS
{
	. = 0x800000;
	.text : { *(.text) *(.text.*) }
}

ENTRY(_start)

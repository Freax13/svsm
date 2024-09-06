.section .text

.globl _start
_start:
xor %rax, %rax
int $0x80

mov $1, %rax
int $0x80

#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

    li  a0, 0x80001000
    li  a1, 0x80002000
    li  a2, 0x00000800

    # void *memcpy(void* dest, const void* src, size_t n)
    # a0=dest, a1=src, a2=n
    #
    mv a3, a0 # Copy destination
loop:
    vsetvli t0, a2, e8,m8,ta,ma   # Vectors of 8b
    vle8.v  v0, (a1)              # Load bytes
    add     a1, a1, t0            # Bump pointer
    sub     a2, a2, t0            # Decrement count
    vse8.v  v0, (a3)              # Store bytes
    add     a3, a3, t0            # Bump pointer
    bnez    a2, loop              # Any more?

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"

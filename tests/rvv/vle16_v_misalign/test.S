#include "../template/vlsu_template.S"

    .text
	.align	1
	.globl	main
	.type	main, @function
main:

VLOAD_V(vle16.v, e16, E16_WIDTH, initial_data, 1*8)
VLOAD_V(vle16.v, e16, E16_WIDTH, initial_data, 2*8)
VLOAD_V(vle16.v, e16, E16_WIDTH, initial_data, 3*8)
VLOAD_V(vle16.v, e16, E16_WIDTH, initial_data, 4*8)
VLOAD_V(vle16.v, e16, E16_WIDTH, initial_data, 5*8)
VLOAD_V(vle16.v, e16, E16_WIDTH, initial_data, 6*8)
VLOAD_V(vle16.v, e16, E16_WIDTH, initial_data, 7*8)
VLOAD_V(vle16.v, e16, E16_WIDTH, initial_data, 8*8)

	li	a0, 0
	jr	ra

#include "../template/vlsu_data.S"

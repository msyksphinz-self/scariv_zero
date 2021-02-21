    .section    .text
_start:
    addi	x10, x0,  1
    addi	x11, x10, 2
    addi	x12, x11, 3
    addi	x13, x12, 4
    addi	x14, x13, 5
    addi	x15, x14, 6
    addi	x16, x15, 7
    addi	x17, x16, 8
    addi	x18, x17, 9
    addi	x19, x18, 10
    addi	x20, x19, 11
    addi	x21, x20, 12

#include "common_pkg.S"

    TEST_FINISH

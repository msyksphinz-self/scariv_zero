    .section    .text
_start:
    addi    x0, x0, 1
    addi    x10, x0, 2
    addi    x3, x10, 3


#include "common_pkg.S"

    TEST_FINISH

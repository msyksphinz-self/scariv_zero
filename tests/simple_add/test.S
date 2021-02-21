#define ADD(rd,rs1,rs2,val1,val2) \
    addi  rs1, x0, val1               ; \
    addi  rs2, x0, val2               ; \
    add rd, rs1, rs2            ; \

    .section    .text
_start:
    ADD(x3, x1, x2, 100, 200)
    ADD(x5, x4, x3, 300, 1324)
    ADD(x10, x11, x12, -30, 28)
    ADD(x15, x20, x21, 220, -10)
    ADD(x20, x21, x22, 0x202, 0x321)
    ADD(x25, x24, x23, -100, -200)
    ADD(x28, x27, x26, -100, 200)


#include "common_pkg.S"

    TEST_FINISH

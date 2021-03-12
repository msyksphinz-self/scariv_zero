    .section    .text
_start:
    addiw      x10, x0,  1
    addiw      x11, x10, 2
    addiw      x12, x11, 3
    addiw      x13, x12, 4
    addiw      x14, x13, 5
    addiw      x15, x14, 6
    addiw      x16, x15, 7
    addiw      x17, x16, 8

#include "common_pkg.S"

    TEST_FINISH

#define TEST_FINISH \
    li  x10, 1                ; \
    li  x11, 0x80001000       ; \
_finish_loop:       ; \
    sw  x10, 0(x11)       ; \
    j   _finish_loop

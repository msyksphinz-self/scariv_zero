    .section .data
    .align   8
initial_data:
    .dword 0x0003000200010000
    .dword 0x0007000600050004
    .dword 0x000b000a00090008
    .dword 0x000f000e000d000c
    .dword 0x0023001200110010
    .dword 0x0027001600150014
    .dword 0x002b001a00190018
    .dword 0x002f001e001d001c


    // dummy data for misalign
.dummy:
    .byte 0

misalign_data:
    .dword 0x0003000200010000
    .dword 0x0007000600050004
    .dword 0x000b000a00090008
    .dword 0x000f000e000d000c
    .dword 0x0023001200110010
    .dword 0x0027001600150014
    .dword 0x002b001a00190018
    .dword 0x002f001e001d001c

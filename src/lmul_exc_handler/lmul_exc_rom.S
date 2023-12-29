    .section    .text
    csrrw   sp, sscratch, sp
    la      sp, temp_data
    sd      x10,  0(sp)
    sd      x11,  8(sp)
    sd      x12, 16(sp)
    la      x10, vector_stack_data
    csrr    x11, vlenb
    vs1r.v v0 , (x10); add   x10, x10, x11
    vs1r.v v1 , (x10); add   x10, x10, x11
    vs1r.v v2 , (x10); add   x10, x10, x11
    vs1r.v v3 , (x10); add   x10, x10, x11
    vs1r.v v4 , (x10); add   x10, x10, x11
    vs1r.v v5 , (x10); add   x10, x10, x11
    vs1r.v v6 , (x10); add   x10, x10, x11
    vs1r.v v7 , (x10); add   x10, x10, x11
    vs1r.v v8 , (x10); add   x10, x10, x11
    vs1r.v v9 , (x10); add   x10, x10, x11
    vs1r.v v10, (x10); add   x10, x10, x11
    vs1r.v v11, (x10); add   x10, x10, x11
    vs1r.v v12, (x10); add   x10, x10, x11
    vs1r.v v13, (x10); add   x10, x10, x11
    vs1r.v v14, (x10); add   x10, x10, x11
    vs1r.v v15, (x10); add   x10, x10, x11
    vs1r.v v16, (x10); add   x10, x10, x11
    vs1r.v v17, (x10); add   x10, x10, x11
    vs1r.v v18, (x10); add   x10, x10, x11
    vs1r.v v19, (x10); add   x10, x10, x11
    vs1r.v v20, (x10); add   x10, x10, x11
    vs1r.v v21, (x10); add   x10, x10, x11
    vs1r.v v22, (x10); add   x10, x10, x11
    vs1r.v v23, (x10); add   x10, x10, x11
    vs1r.v v24, (x10); add   x10, x10, x11
    vs1r.v v25, (x10); add   x10, x10, x11
    vs1r.v v26, (x10); add   x10, x10, x11
    vs1r.v v27, (x10); add   x10, x10, x11
    vs1r.v v28, (x10); add   x10, x10, x11
    vs1r.v v29, (x10); add   x10, x10, x11
    vs1r.v v30, (x10); add   x10, x10, x11
    vs1r.v v31, (x10); add   x10, x10, x11

    csrr   x12, 0x00b  # vscratch
    srli   x12, x12, 20
    fence.i
    vsetvl x0, x0, x12

    la      x10, vector_stack_data
    vl1r.v v0 , (x10); add   x10, x10, x11
    vl1r.v v1 , (x10); add   x10, x10, x11
    vl1r.v v2 , (x10); add   x10, x10, x11
    vl1r.v v3 , (x10); add   x10, x10, x11
    vl1r.v v4 , (x10); add   x10, x10, x11
    vl1r.v v5 , (x10); add   x10, x10, x11
    vl1r.v v6 , (x10); add   x10, x10, x11
    vl1r.v v7 , (x10); add   x10, x10, x11
    vl1r.v v8 , (x10); add   x10, x10, x11
    vl1r.v v9 , (x10); add   x10, x10, x11
    vl1r.v v10, (x10); add   x10, x10, x11
    vl1r.v v11, (x10); add   x10, x10, x11
    vl1r.v v12, (x10); add   x10, x10, x11
    vl1r.v v13, (x10); add   x10, x10, x11
    vl1r.v v14, (x10); add   x10, x10, x11
    vl1r.v v15, (x10); add   x10, x10, x11
    vl1r.v v16, (x10); add   x10, x10, x11
    vl1r.v v17, (x10); add   x10, x10, x11
    vl1r.v v18, (x10); add   x10, x10, x11
    vl1r.v v19, (x10); add   x10, x10, x11
    vl1r.v v20, (x10); add   x10, x10, x11
    vl1r.v v21, (x10); add   x10, x10, x11
    vl1r.v v22, (x10); add   x10, x10, x11
    vl1r.v v23, (x10); add   x10, x10, x11
    vl1r.v v24, (x10); add   x10, x10, x11
    vl1r.v v25, (x10); add   x10, x10, x11
    vl1r.v v26, (x10); add   x10, x10, x11
    vl1r.v v27, (x10); add   x10, x10, x11
    vl1r.v v28, (x10); add   x10, x10, x11
    vl1r.v v29, (x10); add   x10, x10, x11
    vl1r.v v30, (x10); add   x10, x10, x11
    vl1r.v v31, (x10); add   x10, x10, x11

    ld      x10,  0(sp)
    ld      x11,  8(sp)
    ld      x12, 16(sp)
    csrrw   sp, sscratch, sp

    mret

    .section    .data
temp_data:
    .dword  0
    .dword  0

    .align   8
vector_stack_data:

    .global branch_count

branch_count:
    andi    a0, a0, 1
    beqz    a0, .cut_aa
    li      a0, 0
    j       .bb_check
.cut_aa:
    li      a0, 1

.bb_check:
    andi    a1, a1, 1
    beqz    a1, .cut_bb
    li      a1, 0
    j       .final_check
.cut_bb:
    li      a1, 1

.final_check:
    bne     a0, a1, .ret_true
    li      a0, 0
.ret_true:
    li      a0, 1
    ret

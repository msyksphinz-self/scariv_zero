// random assembly code generated by RISC-V torture test generator
// nseqs = 200
// memsize = 1024

#include "riscv_test.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

	j test_start

crash_backward:
	RVTEST_FAIL

test_start:

xreg_init:
	la x31, xreg_init_data
	ld x0, 0(x31)
	ld x1, 8(x31)
	ld x2, 16(x31)
	ld x3, 24(x31)
	ld x4, 32(x31)
	ld x5, 40(x31)
	ld x6, 48(x31)
	ld x7, 56(x31)
	ld x8, 64(x31)
	ld x9, 72(x31)
	ld x10, 80(x31)
	ld x11, 88(x31)
	ld x12, 96(x31)
	ld x13, 104(x31)
	ld x14, 112(x31)
	ld x15, 120(x31)
	ld x16, 128(x31)
	ld x17, 136(x31)
	ld x18, 144(x31)
	ld x19, 152(x31)
	ld x20, 160(x31)
	ld x21, 168(x31)
	ld x22, 176(x31)
	ld x23, 184(x31)
	ld x24, 192(x31)
	ld x25, 200(x31)
	ld x26, 208(x31)
	ld x27, 216(x31)
	ld x28, 224(x31)
	ld x29, 232(x31)
	ld x30, 240(x31)
	ld x31, 248(x31)

	j pseg_0

pseg_0:
	addi x5, x25, 0
	addi x19, x0, 429
	addi x22, x5, 0
	la x25, test_memory+2574
	addi x26, x0, 786
	la x27, test_memory+170
	mulw x1, x26, x26
	lbu x20, -1813(x25)
	addi x12, x0, -501
	lhu x6, -36(x27)
	la x29, test_memory-987
	remw x14, x26, x26
	addi x2, x0, -1129
	la x4, test_memory+1096
	addi x9, x0, -751
	la x1, test_memory+719
	rem x3, x28, x28
	la x28, test_memory-246
	sd x19, -247(x1)
	la x23, test_memory-105
	sw x0, 209(x23)
	sll x31, x9, x9
	addi x13, x0, 1803
	sb x7, 1275(x29)
	mulh x11, x2, x2
	sb x13, 1076(x28)
	la x5, test_memory-990
	la x25, test_memory+1864
	la x24, test_memory+766
	addi x15, x19, 805
	addi x30, x12, -483
	bge x19, x15, crash_backward
	addi x20, x0, 1838
	addi x17, x0, -1157
	lw x8, -232(x4)
	sh x22, 98(x24)
	addi x3, x0, 247
	addi x10, x0, -238
	lbu x22, 1991(x5)
	mulh x27, x0, x1
	la x21, test_memory+1588
	sb x15, -1054(x21)
	sub x18, x13, x10
	addi x16, x17, -457
	mulhu x6, x20, x20
	bltu x17, x16, crash_forward
	addi x7, x0, -372
	lw x14, -1028(x25)
	la x22, test_memory+1561
	addi x19, x0, 1145
	la x20, test_memory+1158
	la x30, test_memory-1500
	lwu x16, 2044(x30)
	la x1, test_memory-1445
	addi x4, x0, 1677
	la x12, test_memory+2100
	addi x28, x0, 1
	addi x13, x0, -162
	lb x23, -1083(x22)
	la x15, test_memory-540
	sll x28, x28, 63
	sw x16, -366(x20)
	addi x11, x0, 1248
	la x31, test_memory+2709
	addi x14, x19, 1462
	lh x10, 730(x15)
	div x26, x3, x7
	addi x21, x0, 9
	addi x9, x21, 302
	sh x9, -1687(x31)
	la x23, test_memory-658
	addi x27, x11, 253
	la x30, test_memory-1356
	add x18, x4, x13
	sd x16, 898(x23)
	la x24, test_memory+2581
	addi x5, x0, 1178
	addi x22, x5, 305
	or x25, x18, x14
	lb x29, -1084(x12)
	lwu x2, 1981(x1)
	sll x22, x30, x30
	addi x10, x20, 0
	addiw x23, x23, -1460
	sra x15, x27, x0
	addi x21, x0, 356
	lwu x16, 1516(x30)
	addi x18, x0, 1641
	addi x17, x0, -1
	sd x16, -2045(x24)
	la x27, test_memory+1726
	la x22, test_memory+1972
	addi x11, x0, 1002
	la x12, test_memory+2384
	addi x13, x10, 0
	addi x5, x0, 1664
	sltu x25, x21, x18
	ld x20, -1960(x12)
	sra x15, x26, x30
	addi x7, x0, 1
	sllw x4, x5, x5
	sd x18, -1206(x27)
	xor x17, x17, x28
	lhu x23, -1330(x22)
	sll x7, x7, 63
	and x8, x18, x17
	la x27, test_memory-418
	or x6, x8, x28
	addi x29, x0, -1608
	addi x18, x0, -388
	addi x14, x0, -620
	la x24, test_memory-768
	addi x12, x0, -1602
	mulh x19, x14, x14
	la x30, test_memory+106
	addi x2, x0, 589
	sw x2, 274(x30)
	mulw x9, x11, x29
	addi x21, x0, 737
	lhu x23, 1206(x24)
	addi x9, x0, -526
	addi x25, x2, 850
	add x11, x9, x9
	addi x19, x0, 0
	addi x26, x0, -1
	addi x4, x28, 888
	lhu x15, 930(x27)
	xor x26, x26, x7
	sllw x23, x27, x27
	la x14, test_memory+2534
	la x11, test_memory-1139
	sb x9, 1456(x11)
	addi x4, x0, 1
	addi x13, x0, 0
	sb x17, -2027(x14)
	divw x27, x14, x14
	srlw x1, x12, x21
	addi x5, x0, 664
	sll x4, x4, 63
	addi x6, x0, 1
	la x10, test_memory+1176
	addi x24, x0, -1
	sll x6, x6, 63
	addi x12, x0, -713
	addi x1, x0, 1
	sraw x16, x18, x18
	addi x28, x0, -1
	xor x28, x28, x6
	blt x25, x2, crash_backward
	and x17, x7, x28
	addi x20, x5, 469
	la x21, test_memory+190
	or x8, x13, x6
	xor x24, x24, x4
	divu x30, x28, x9
	and x31, x8, x26
	addi x23, x0, -981
	remuw x11, x12, x23
	or x3, x9, x7
	and x9, x25, x24
	ld x22, -472(x10)
	sll x1, x1, 63
	sw x7, -78(x21)
	addi x18, x0, 570
	la x2, test_memory+2450
	la x19, test_memory+1777
	addi x25, x0, 1417
	la x10, test_memory+1706
	addi x31, x0, 1
	or x15, x9, x4
	la x12, test_memory+1588
	addi x5, x0, 892
	addi x27, x0, -1
	lb x3, -1023(x12)
	or x11, x15, x1
	lbu x20, -779(x10)
	sll x31, x31, 63
	slt x16, x18, x25
	rem x10, x15, x4
	sra x28, x3, x13
	beq x9, x15, crash_backward
	la x6, test_memory+929
	la x17, test_memory-558
	addi x22, x0, 896
	addi x16, x0, 1
	sll x16, x16, 63
	sd x15, 1478(x17)
	sw x9, -897(x19)
	xor x27, x27, x1
	mulhu x21, x5, x22
	and x14, x13, x27
	lbu x20, -6(x6)
	divu x11, x6, x6
	la x8, test_memory-484
	la x22, test_memory-1255
	addi x25, x17, 1595
	la x4, test_memory+1132
	lwu x26, 828(x8)
	srai x21, x27, 7
	addi x12, x0, -1
	addi x28, x21, 0
	addi x15, x0, -112
	addi x9, x0, 1479
	lw x13, -1566(x2)
	addi x24, x28, 0
	addi x10, x0, -1714
	addi x20, x0, -1090
	mulw x8, x28, x25
	addi x21, x0, 589
	xor x12, x12, x16
	mulhsu x5, x9, x10
	and x3, x28, x12
	la x19, test_memory+2019
	mulh x2, x23, x23
	addi x6, x0, -2022
	addi x13, x0, -1243
	sd x27, 1983(x22)
	blt x28, x24, crash_backward
	addi x17, x15, -699
	or x29, x26, x1
	or x18, x3, x16
	la x2, test_memory+619
	lh x9, -531(x2)
	sw x15, -1271(x19)
	addi x23, x0, -1
	sw x20, -672(x4)
	la x22, test_memory-333
	mulhu x11, x20, x6
	addi x8, x0, 1403
	sll x5, x13, x8
	remuw x25, x21, x21
	bge x17, x15, crash_forward
	xor x23, x23, x31
	lb x10, 360(x22)
	and x7, x25, x23
	or x30, x28, x31
	bltu x30, x7, crash_backward
	addi x28, x0, -1459
	divw x26, x28, x28
	addi x31, x0, 162
	sraw x20, x6, x15
	la x4, test_memory-969
	addi x27, x0, 691
	addi x6, x0, -1562
	sub x22, x20, x20
	sllw x16, x15, x15
	srli x19, x25, 44
	la x1, test_memory-453
	sra x10, x31, x25
	addi x23, x0, -1533
	divw x9, x5, x5
	lb x17, 1536(x4)
	or x29, x31, x6
	la x10, test_memory-513
	addi x12, x0, -267
	sd x14, 1017(x10)
	addi x7, x0, 1
	sh x7, 1377(x1)
	la x16, test_memory-494
	xor x29, x4, x4
	lhu x19, 860(x16)
	addi x21, x12, -1075
	addi x17, x0, 1
	addi x11, x0, -455
	div x10, x28, x11
	la x2, test_memory-498
	sll x17, x17, 63
	la x1, test_memory-267
	sw x11, 659(x1)
	addi x3, x0, 184
	sll x28, x23, x23
	addi x4, x0, -1
	sll x7, x7, 63
	addi x14, x0, -895
	addi x5, x0, 1742
	lb x25, 724(x2)
	addi x22, x0, -1
	xor x22, x22, x7
	addi x26, x27, 1762
	and x20, x13, x22
	addi x8, x0, -507
	addi x24, x3, 1420
	bge x3, x24, crash_backward
	addi x30, x0, 31
	bltu x0, x0, crash_backward
	mulhsu x15, x14, x14
	bltu x26, x27, crash_forward
	remuw x18, x11, x8
	or x9, x25, x7
	addi x25, x0, 1044
	divw x13, x5, x30
	subw x21, x29, x11
	addi x14, x0, 405
	addi x16, x0, -1970
	bgeu x20, x9, crash_forward
	la x2, test_memory-547
	addi x23, x0, 957
	addi x26, x0, 26
	la x24, test_memory+2447
	la x7, test_memory+2616
	sw x14, -2011(x24)
	remw x12, x16, x16
	addi x8, x26, 827
	la x15, test_memory+230
	remuw x1, x25, x23
	la x28, test_memory-454
	addi x22, x0, -697
	addi x13, x0, 92
	ld x10, 634(x15)
	addi x21, x0, -1880
	addw x27, x22, x13
	addi x25, x0, 1
	addi x5, x21, -1804
	lh x20, -1776(x7)
	la x3, test_memory+1393
	lh x19, 1121(x2)
	xor x4, x4, x17
	sll x25, x25, 63
	lw x29, 1294(x28)
	and x31, x27, x4
	and x30, x7, x9
	addi x26, x0, -1
	sd x22, -553(x3)
	addi x16, x0, 1
	xor x26, x26, x25
	remw x11, x29, x29
	sll x16, x16, 63
	and x24, x15, x26
	or x8, x4, x25
	bgeu x24, x8, crash_backward
	addi x9, x0, -1
	xor x9, x9, x16
	remu x18, x14, x14
	and x1, x7, x9
	or x6, x31, x17
	beq x31, x6, crash_forward
	or x12, x16, x16
	addi x22, x0, -101
	la x19, test_memory+1342
	remw x31, x26, x0
	sd x12, -1326(x19)
	addi x13, x0, 1999
	addi x26, x0, -365
	la x21, test_memory+1701
	lbu x14, -848(x21)
	la x30, test_memory+120
	sb x8, 601(x30)
	remw x1, x13, x13
	sltiu x5, x11, 1565
	sltiu x16, x29, 1084
	addi x7, x12, 550
	mulw x10, x26, x26
	sra x17, x11, x11
	la x31, test_memory+1878
	addi x4, x0, 898
	sb x0, -1400(x31)
	remuw x2, x8, x24
	la x5, test_memory+1069
	srlw x1, x30, x30
	addi x29, x0, -377
	la x16, test_memory+1894
	la x28, test_memory+1117
	addi x14, x0, 1318
	addi x10, x0, 0
	lw x19, -229(x5)
	la x17, test_memory-569
	ori x18, x15, 1669
	sd x1, 649(x17)
	la x30, test_memory+2094
	addi x15, x0, -838
	sltu x7, x31, x31
	addi x21, x14, 1418
	addi x7, x24, 0
	addi x26, x0, 0
	remw x19, x27, x27
	addw x9, x22, x29
	sra x25, x15, x15
	addi x2, x7, 0
	addi x3, x0, -118
	addi x8, x3, -1528
	bltu x3, x8, crash_forward
	lb x23, -1077(x28)
	remw x1, x25, x2
	addi x12, x0, 1012
	addi x26, x0, 1710
	addi x27, x4, 1632
	addi x19, x0, 1560
	addi x5, x0, 265
	sb x29, -1823(x30)
	addi x18, x0, -276
	divu x28, x3, x29
	div x9, x5, x5
	bltu x27, x4, crash_backward
	lw x13, -1630(x16)
	addi x20, x12, 1226
	bgeu x12, x20, crash_backward
	addi x6, x0, 322
	la x8, test_memory-1740
	sll x3, x29, x29
	la x23, test_memory-736
	addi x11, x0, 501
	addw x10, x26, x19
	addi x4, x0, 1
	la x22, test_memory+2107
	lw x29, 1348(x23)
	srlw x24, x6, x11
	la x17, test_memory+1172
	lwu x25, 2032(x8)
	lbu x12, -1286(x22)
	and x27, x9, x2
	sd x24, -484(x17)
	sllw x30, x0, x24
	sll x4, x4, 63
	la x1, test_memory-206
	lb x13, 1077(x1)
	remu x16, x17, x6
	addi x14, x0, -1
	and x31, x5, x18
	addi x7, x0, -704
	addi x2, x0, -1022
	or x15, x7, x2
	xor x14, x14, x4
	and x9, x2, x14
	or x21, x9, x4
	bltu x21, x9, crash_backward
	sll x28, x15, x15
	addi x3, x0, -1236
	sll x16, x5, x11
	la x6, test_memory+406
	addi x25, x0, 0
	addi x10, x0, 0
	blt x25, x10, crash_forward
	addi x24, x0, -690
	addi x30, x0, -582
	lb x26, 561(x6)
	mulhsu x8, x30, x30
	divu x28, x24, x24
	addi x31, x0, -648
	addi x4, x31, -1894
	divuw x14, x3, x3
	bge x4, x31, crash_forward
	j reg_dump

reg_dump:
	la x1, loop_count
	lw x2, 0(x1)
	addi x3, x2, -1
	sw x3, 0(x1)
	bnez x2, pseg_0
	la x1, xreg_output_data
	sd x0, 0(x1)
	sd x2, 16(x1)
	sd x3, 24(x1)
	sd x4, 32(x1)
	sd x5, 40(x1)
	sd x7, 56(x1)
	sd x8, 64(x1)
	sd x9, 72(x1)
	sd x10, 80(x1)
	sd x11, 88(x1)
	sd x12, 96(x1)
	sd x13, 104(x1)
	sd x14, 112(x1)
	sd x15, 120(x1)
	sd x16, 128(x1)
	sd x18, 144(x1)
	sd x19, 152(x1)
	sd x20, 160(x1)
	sd x21, 168(x1)
	sd x24, 192(x1)
	sd x25, 200(x1)
	sd x26, 208(x1)
	sd x27, 216(x1)
	sd x28, 224(x1)
	sd x29, 232(x1)
	sd x30, 240(x1)
	sd x31, 248(x1)

	j test_end

crash_forward:
	RVTEST_FAIL

test_end:
	RVTEST_PASS

RVTEST_CODE_END


	.data

hidden_data:
	.align 8
xreg_init_data:
reg_x0_init:	.dword 0xffffffffffffffff
reg_x1_init:	.dword 0x0b703d556ca0a09e
reg_x2_init:	.dword 0xffffffffffffffff
reg_x3_init:	.dword 0xd53c3b2315baba32
reg_x4_init:	.dword 0x681e1b76d7c77cbb
reg_x5_init:	.dword 0xf248ab84158aeec6
reg_x6_init:	.dword 0x1c7dfc4405b64517
reg_x7_init:	.dword 0xffffffffffffffff
reg_x8_init:	.dword 0xe6b36d17fb7148a0
reg_x9_init:	.dword 0x4a4877fa23aa97a7
reg_x10_init:	.dword 0x0000000000000000
reg_x11_init:	.dword 0xffffffffffff8008
reg_x12_init:	.dword 0x9df28046437ee610
reg_x13_init:	.dword 0xfe3f89abe1d69e5e
reg_x14_init:	.dword 0x0000000000000000
reg_x15_init:	.dword 0x719924a0d9b3af35
reg_x16_init:	.dword 0x0000000000000006
reg_x17_init:	.dword 0x0000000000000008
reg_x18_init:	.dword 0x0f454f64ced07dba
reg_x19_init:	.dword 0xa3ed9b85c3462e44
reg_x20_init:	.dword 0x0800000000000008
reg_x21_init:	.dword 0xad3049188bfcb06c
reg_x22_init:	.dword 0x23e976c095a9cf64
reg_x23_init:	.dword 0xffffffffffffffff
reg_x24_init:	.dword 0x45060b31b06f45d1
reg_x25_init:	.dword 0x0000000000000000
reg_x26_init:	.dword 0x0000000000000000
reg_x27_init:	.dword 0xc09e8998d322c5d4
reg_x28_init:	.dword 0x62c242b0f08d1818
reg_x29_init:	.dword 0xd216be940ce518dc
reg_x30_init:	.dword 0xa94ebb7c1e8a162c
reg_x31_init:	.dword 0x0000000000000000

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0xb7d19da9a795950b
reg_x1_output:	.dword 0xf22790e46c8a0240
reg_x2_output:	.dword 0x09fd3afdd9dd7f69
reg_x3_output:	.dword 0xaf2c148e5b3aeb3e
reg_x4_output:	.dword 0x3e651ef522fdba1c
reg_x5_output:	.dword 0x547feadd20d8bda2
reg_x6_output:	.dword 0x05311a5f8e2602ed
reg_x7_output:	.dword 0x26e75f26cad39634
reg_x8_output:	.dword 0x8c28e2055dff7e8f
reg_x9_output:	.dword 0x1d9ad0d69b040325
reg_x10_output:	.dword 0x9d3150b1d3cfd324
reg_x11_output:	.dword 0x1fbb95a4d59a0c2b
reg_x12_output:	.dword 0xc79336955a54e705
reg_x13_output:	.dword 0x85f84b07443218f0
reg_x14_output:	.dword 0x130f49cacfd747c2
reg_x15_output:	.dword 0x9ca04ae5c0e759ac
reg_x16_output:	.dword 0x6fe80c35d64d7d67
reg_x17_output:	.dword 0x3a2d37957f919610
reg_x18_output:	.dword 0xe043ba932d4ace01
reg_x19_output:	.dword 0x4344d2fe65d68665
reg_x20_output:	.dword 0xf2d598ca3c183560
reg_x21_output:	.dword 0x46a4951d62951af5
reg_x22_output:	.dword 0xe5df2f8832fe951d
reg_x23_output:	.dword 0x0c8bb5b1ccb355a9
reg_x24_output:	.dword 0xd18f4f09e5b560de
reg_x25_output:	.dword 0xcd4f9d31b6bd99f3
reg_x26_output:	.dword 0xc2cdeb3b96594ad8
reg_x27_output:	.dword 0xbd11f0fe525096ee
reg_x28_output:	.dword 0x48e12501fc82b495
reg_x29_output:	.dword 0x264eaed6d2352fc2
reg_x30_output:	.dword 0xc24914d38f4be7f7
reg_x31_output:	.dword 0x8d6c0b9036a8064d

// Memory Blocks
	.align 8
test_memory:
	.dword 0xa4f52a9067935c7c, 0x63dd09047abc8bff
	.dword 0x1ccf368b61c68cc2, 0xf502f74a3e65bd05
	.dword 0x06c56fe7b046204d, 0x3109552734ace9a9
	.dword 0x773e0c2d093c6d88, 0x3dbac3c2e34131f7
	.dword 0x66743c1180cb9809, 0xaa0501a0161097a4
	.dword 0xa4e7a19bf308cf19, 0x61cd20c76945ca2b
	.dword 0x0b04936a648e7072, 0x1c146c4374141139
	.dword 0xb2bcc14ebcc7134a, 0xb881b0d3116cf94b
	.dword 0x852d0e1fbeafbf90, 0x9269dcd98751a694
	.dword 0x2ae6b2cdbbefd575, 0x21ae2b998c2bf223
	.dword 0x783efeb67f09692d, 0xb4754fa171b9b545
	.dword 0x516a4936ac4d16f6, 0xb3285081c0d6e727
	.dword 0x215be884fa689359, 0xc1730fc7e71970c0
	.dword 0xd3ae41bc43177baf, 0x6693a927f8fbdaed
	.dword 0x9a7346386ef22ae6, 0x644321f517823add
	.dword 0x05fef2228cce9685, 0xe9351bd7811700ae
	.dword 0x4bc2a04e29e377ec, 0xb1d37ebf61138c58
	.dword 0x53694743ec1e45e0, 0x7ab64e14da42acca
	.dword 0xdbd1f39bf820c247, 0xe3a71d33bce96d52
	.dword 0xf587138f4863202f, 0xbb02d716aac4d541
	.dword 0x332667c887440614, 0x4743cd53d1317dce
	.dword 0x6316ad837a9ff062, 0x62a94247b59c223a
	.dword 0xd62555d0a11db838, 0x6a90e29310a88e35
	.dword 0x2577de384ff6426e, 0x2469e1c6436e8e80
	.dword 0xece19e82b7d99ad9, 0xc470ae5b5602c7d2
	.dword 0xee681fd588f3ffcd, 0x61dd70e4917b97ff
	.dword 0xcdcd51030d39a1e2, 0xf81eca87f8006557
	.dword 0xd8982c1c15481bfb, 0xf05d86aa0d74004c
	.dword 0xc589a147db98e784, 0x591d33ea6930fb57
	.dword 0xb6f4dada6bb050fa, 0xe698d8505f591d1b
	.dword 0x234f2e9f4ba8b0b0, 0x84ba34c614a750c9
	.dword 0x37bd50774631ebcf, 0x4e7d4bc684c5b8c6
	.dword 0x46a89a25ae19819d, 0xbd791f554f1fc78b
	.dword 0x69c07c6b3aefa902, 0xa261da2f8b4282cd
	.dword 0x88796d5264a24248, 0x33e7d843e25b54dd
	.dword 0xe35be7c5a22ea122, 0x2f9a4261c9881050
	.dword 0x5e8b506a221772ef, 0x8fab3132eeb109e2
	.dword 0x6415d3a7fa5c453f, 0xd3de8b68d1d06c97
	.dword 0x061b9108ad847095, 0xdacc13359d182c23
	.dword 0x4aeca7c683276b6e, 0x0e305700b99a398b
	.dword 0x5722f8a02078c982, 0x688f7957622cde0b
	.dword 0xa4b5b0ec18fe6b49, 0x0728041ebd7f603a
	.dword 0x1f51f2f0acfba1c0, 0x70633b1160f1576b
	.dword 0xe7252f7672844a6c, 0x07d3a168ba015156
	.dword 0x88fb049553d7279f, 0xdca9a6d6d24dadf8
	.dword 0xa659b5d4c1cef8f9, 0xd191afb86c6cd5b7
	.dword 0x9f659176982e1831, 0x3c6dec8b34902dc8
	.dword 0xb404d71063809e15, 0x6c91b49cf1376ed5
	.dword 0xf742f357298d53cf, 0xde4b58076c7041d9
	.dword 0x208b253fb60df469, 0x4de49cda7f78474e
	.dword 0xdf3fe048b1eb8292, 0xda115b97ef55ec8a
	.dword 0x87b580136bc3b6a1, 0x2946eee4f35eb366
	.dword 0x41ec21337148c8da, 0x35ee6a7c84e7d020
	.dword 0xebcdb349aa5d1bf0, 0x5e0ecd6853c84182
	.dword 0x8f72985214e08bcb, 0x632ba36c2c21c743
	.dword 0x2340653a133d648b, 0xb1e7c9c321585aac
	.dword 0x9adb97b5441f45cb, 0x05c34b0e36760d7e
	.dword 0x861e554f5f9e7629, 0xf7468688e7b37312
	.dword 0x53d387c0b1ce6b06, 0x595c167eb9baf7c2
	.dword 0x1a16ea849446888a, 0x50be29ff3bbfca87
	.dword 0xab2fddab1c285dea, 0x8d7345cf0fe73ce3
	.dword 0xf4c611ecf096e1ed, 0xfda1a0a00c0dbd01
	.dword 0xbdac62008ac673ab, 0x21bf8e8339dece1a
	.dword 0xed6f6d2da505a398, 0xff9aaf9aeac9a319

.align 8
loop_count: .word 0x40

RVTEST_DATA_END

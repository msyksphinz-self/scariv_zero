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
	la x1, test_memory+1632
	xor x28, x28, x28
	addi x16, x0, -1835
	lhu x12, -1094(x1)
	la x31, test_memory+1612
	div x8, x27, x29
	addi x15, x0, -152
	la x26, test_memory+2079
	addi x5, x0, -638
	sh x24, -1567(x26)
	sb x7, -936(x31)
	addi x19, x15, -1403
	addi x28, x0, -367
	addi x30, x0, 1
	addi x21, x0, 0
	addi x20, x0, 0
	addi x13, x5, -2038
	mulh x4, x28, x28
	addi x24, x0, 271
	sll x30, x30, 63
	addi x23, x0, 359
	sub x22, x24, x24
	addi x25, x0, 1
	addi x9, x0, -1
	addi x11, x0, 618
	sll x25, x25, 63
	la x8, test_memory+1303
	addi x17, x0, -431
	la x31, test_memory-751
	add x29, x23, x23
	addi x4, x0, 1
	addi x28, x0, 1
	sll x28, x28, 63
	la x21, test_memory+684
	and x14, x11, x11
	addi x27, x0, -1
	addi x6, x17, -1948
	la x19, test_memory+2086
	sh x12, -1142(x19)
	sd x0, 1495(x31)
	xor x27, x27, x25
	lh x5, 262(x21)
	la x1, test_memory-235
	rem x2, x16, x16
	addi x24, x0, -1
	and x18, x22, x27
	sll x4, x4, 63
	bgeu x6, x17, crash_backward
	lhu x12, -329(x8)
	xor x9, x9, x30
	addi x15, x0, -1
	xor x15, x15, x4
	and x10, x6, x9
	sw x4, 1207(x1)
	or x3, x5, x30
	and x26, x14, x15
	xor x24, x24, x28
	slt x17, x10, x10
	la x8, test_memory+649
	or x22, x26, x4
	xor x14, x12, x1
	la x31, test_memory+48
	bgeu x26, x22, crash_backward
	lb x12, 725(x31)
	addi x23, x0, -1262
	and x13, x29, x24
	addi x26, x0, 1261
	addi x16, x0, 1607
	ld x29, 319(x8)
	addi x12, x26, 212
	or x20, x13, x28
	sraiw x6, x11, 5
	addi x17, x0, -1557
	srli x15, x9, 35
	addw x21, x16, x16
	addi x11, x0, -1632
	mulh x4, x23, x9
	mulhsu x3, x5, x18
	la x20, test_memory+728
	addi x3, x0, -550
	lh x13, -528(x20)
	addi x10, x0, -600
	mulhsu x24, x13, x20
	lui x30, 172981
	la x2, test_memory+1248
	addi x26, x0, -668
	srl x14, x17, x17
	la x21, test_memory+2090
	divu x12, x17, x31
	addi x28, x0, -2035
	addi x15, x28, -736
	sd x29, -1970(x21)
	or x7, x28, x25
	addi x4, x0, -1877
	divuw x9, x26, x26
	bgeu x18, x7, crash_forward
	addi x8, x10, -764
	la x31, test_memory-602
	lhu x16, -302(x2)
	divw x5, x23, x11
	blt x10, x8, crash_forward
	divw x1, x3, x4
	addi x12, x0, -640
	lb x22, 942(x31)
	la x19, test_memory-1003
	addi x13, x0, 1
	ori x20, x15, -923
	lbu x6, 1651(x19)
	addi x23, x0, 1225
	addi x24, x0, 1
	addi x4, x0, -1606
	sll x24, x24, 63
	divu x9, x23, x4
	addi x10, x0, -1
	xor x10, x10, x24
	sll x13, x13, 63
	addi x27, x0, -1
	divu x7, x12, x12
	and x5, x18, x10
	or x28, x5, x24
	beq x5, x28, crash_forward
	xor x27, x27, x13
	and x17, x6, x27
	la x12, test_memory+1757
	sll x21, x31, x31
	la x7, test_memory+529
	addi x5, x0, 1798
	or x15, x17, x13
	srl x4, x8, x16
	la x9, test_memory-266
	addi x11, x0, -683
	bge x15, x17, crash_forward
	remu x19, x5, x5
	la x31, test_memory+1191
	addi x8, x0, -567
	addi x22, x0, 12
	sra x2, x11, x11
	la x24, test_memory-1231
	sh x25, 1607(x24)
	lbu x25, 648(x9)
	addi x28, x0, 1732
	lb x3, 386(x7)
	sra x23, x2, x2
	mulhsu x30, x8, x8
	sh x8, -871(x31)
	addi x14, x0, 733
	sraw x26, x28, x14
	sb x22, -1095(x12)
	remu x6, x22, x22
	addi x22, x0, 1558
	slli x20, x26, 2
	addi x12, x0, 2006
	slti x6, x25, -1122
	addi x3, x0, -1386
	la x19, test_memory-749
	lui x11, 622991
	addi x16, x0, 1535
	sub x26, x13, x21
	addi x31, x0, -1793
	subw x29, x3, x31
	sub x17, x22, x22
	remw x23, x13, x8
	addi x25, x0, 2046
	la x24, test_memory-1550
	lb x27, 1036(x19)
	addi x18, x0, -1790
	sh x11, 1984(x24)
	mulhu x30, x12, x16
	mulhsu x21, x18, x18
	addi x2, x0, 280
	sub x15, x2, x2
	la x10, test_memory-265
	la x9, test_memory+2739
	addi x7, x0, -1499
	rem x13, x25, x7
	addi x3, x0, -812
	addi x6, x0, 566
	addi x11, x0, 1
	lb x8, -1791(x9)
	addi x1, x0, 1
	la x4, test_memory+98
	or x17, x17, x17
	sll x11, x11, 63
	addi x28, x0, -1
	sll x1, x1, 63
	addi x17, x0, 1171
	la x24, test_memory-194
	la x29, test_memory+1861
	sra x15, x27, x27
	xor x28, x28, x11
	la x18, test_memory+1178
	addi x16, x0, -1
	addi x8, x0, -366
	addi x25, x0, 1
	xor x16, x16, x1
	and x30, x20, x16
	xor x21, x24, x19
	la x22, test_memory+1897
	lwu x26, -993(x22)
	sh x13, 318(x4)
	sd x2, -650(x18)
	lbu x5, 687(x10)
	lh x14, -1327(x29)
	sraw x9, x17, x8
	or x7, x31, x1
	and x2, x6, x28
	la x27, test_memory-400
	la x8, test_memory-82
	subw x14, x22, x22
	addi x9, x0, 593
	addi x18, x0, -2
	lw x19, 246(x24)
	remuw x26, x29, x16
	or x31, x2, x11
	addi x10, x0, 1672
	sb x16, 454(x27)
	la x30, test_memory+602
	addi x22, x0, 822
	sll x25, x25, 63
	addi x17, x18, -564
	sra x21, x22, x22
	lh x1, 260(x8)
	sllw x12, x3, x6
	sllw x16, x9, x10
	ori x15, x4, 1527
	addi x9, x0, -195
	addi x6, x0, -671
	divuw x7, x6, x31
	addi x2, x6, -54
	mul x15, x12, x19
	addi x8, x0, 1242
	la x29, test_memory-1127
	addi x20, x0, -1
	bgeu x2, x6, crash_forward
	addi x2, x0, -10
	addw x24, x9, x8
	xor x20, x20, x25
	la x3, test_memory-557
	addi x11, x0, 1
	addi x15, x2, -1000
	la x5, test_memory+102
	xor x10, x4, x4
	and x13, x7, x20
	lbu x21, 807(x3)
	ld x1, 514(x5)
	addi x10, x0, 936
	addi x12, x17, -834
	xor x24, x17, x30
	addi x3, x0, 541
	la x9, test_memory+2457
	addi x17, x0, -754
	la x6, test_memory+765
	addi x7, x17, -3
	lwu x4, -286(x30)
	srlw x8, x16, x16
	lw x18, -461(x6)
	or x23, x13, x25
	sh x31, 1439(x29)
	bge x23, x13, crash_forward
	la x16, test_memory+629
	addi x1, x0, 1945
	sll x11, x11, 63
	divw x28, x29, x29
	la x2, test_memory+2351
	remw x19, x10, x10
	ld x22, -349(x16)
	ld x5, -1729(x9)
	div x21, x3, x1
	addi x4, x0, 1749
	addi x6, x0, 1
	addi x9, x0, 1308
	la x19, test_memory-1575
	addi x1, x0, 622
	lw x13, -1451(x2)
	add x8, x12, x22
	addi x20, x0, 1
	addi x30, x0, -195
	sll x6, x6, 63
	sll x12, x4, x4
	addi x26, x0, -1
	la x16, test_memory+260
	addi x5, x0, 1751
	xor x26, x26, x11
	and x14, x25, x26
	or x31, x26, x4
	addi x25, x0, -1
	sllw x3, x9, x1
	sh x5, 586(x16)
	sllw x17, x30, x30
	la x21, test_memory-660
	lwu x22, 688(x21)
	sw x12, 1811(x19)
	xor x25, x25, x6
	sll x20, x20, 63
	or x27, x14, x11
	addi x23, x0, -1
	add x10, x5, x5
	bge x27, x14, crash_backward
	xor x23, x23, x20
	and x28, x11, x25
	and x29, x18, x23
	la x15, test_memory+1018
	or x18, x17, x20
	or x24, x28, x6
	lhu x7, -634(x15)
	bltu x24, x28, crash_backward
	or x22, x25, x25
	la x10, test_memory+717
	addi x30, x11, 0
	addi x7, x30, 0
	addi x13, x0, -19
	addi x17, x0, 1206
	la x16, test_memory+1899
	addi x27, x17, 1358
	sltu x26, x13, x13
	lh x15, -957(x16)
	bltu x30, x7, crash_forward
	addi x2, x0, 1
	addi x14, x0, 1
	sll x2, x2, 63
	la x4, test_memory+247
	la x5, test_memory+375
	sll x14, x14, 63
	la x9, test_memory-789
	addi x3, x0, -1
	lb x1, -143(x5)
	addi x8, x0, -1
	sb x24, -196(x4)
	lb x12, -662(x10)
	sh x25, 1423(x9)
	xor x8, x8, x14
	and x31, x20, x8
	xor x3, x3, x2
	or x21, x31, x14
	la x10, test_memory+2644
	mulh x1, x13, x13
	lwu x7, -1988(x10)
	la x27, test_memory+45
	la x28, test_memory-119
	addi x6, x0, -217
	addi x12, x18, 0
	srai x20, x29, 50
	addi x24, x0, 384
	addi x16, x0, 1435
	addi x29, x16, 1817
	addi x13, x0, -1298
	addi x5, x0, 388
	remu x25, x13, x13
	addi x4, x0, -1434
	addi x17, x12, 0
	la x9, test_memory-1172
	sltu x22, x6, x24
	addi x26, x4, -2019
	lbu x18, 1695(x9)
	beq x4, x26, crash_backward
	bgeu x16, x29, crash_backward
	lhu x15, 509(x28)
	div x30, x5, x5
	and x19, x2, x3
	or x11, x23, x2
	lh x23, 537(x27)
	bge x11, x19, crash_forward
	addi x6, x0, 300
	addi x2, x0, 1
	addi x14, x0, 870
	la x28, test_memory+1058
	and x1, x14, x14
	addi x30, x0, -965
	la x29, test_memory+1164
	ld x12, -114(x28)
	la x3, test_memory-294
	addi x25, x6, 162
	addi x23, x0, -270
	sll x2, x2, 63
	or x8, x30, x23
	addi x11, x0, 1
	la x21, test_memory-733
	add x20, x26, x5
	lh x7, 296(x3)
	mul x5, x16, x6
	addi x22, x0, 416
	addi x17, x6, 0
	addi x16, x17, 0
	sll x11, x11, 63
	addi x30, x0, -1478
	sltu x1, x18, x18
	addi x4, x21, 0
	sll x5, x22, x22
	addi x24, x4, 0
	lb x10, -641(x29)
	mul x25, x25, x25
	bltu x4, x24, crash_forward
	la x8, test_memory+2132
	addi x20, x22, 452
	la x28, test_memory+2119
	div x6, x23, x18
	sltiu x14, x8, -968
	or x3, x30, x30
	remw x12, x5, x24
	lwu x23, -1856(x8)
	addi x4, x0, 1
	sub x5, x20, x20
	sll x4, x4, 63
	lwu x19, 1081(x21)
	addi x16, x0, 1
	addi x15, x22, 623
	addi x25, x0, -1
	andi x1, x9, -188
	xor x25, x25, x4
	sraw x17, x20, x20
	mulhsu x7, x27, x15
	sll x16, x16, 63
	addi x10, x0, -1
	addi x9, x0, -1
	mulw x29, x24, x24
	xor x10, x10, x16
	and x24, x13, x10
	sb x14, -1519(x28)
	or x14, x1, x16
	rem x22, x0, x0
	xor x9, x9, x11
	add x8, x13, x13
	and x31, x3, x9
	la x22, test_memory-494
	or x18, x31, x11
	lh x3, 1372(x22)
	addi x29, x0, 581
	addi x13, x0, -1
	xor x13, x13, x2
	addi x21, x0, 1
	sll x21, x21, 63
	addi x12, x0, 1
	addi x16, x0, 182
	and x27, x20, x13
	and x20, x20, x25
	addi x1, x0, 1594
	and x14, x18, x18
	or x26, x3, x2
	or x6, x20, x4
	sltu x7, x3, x3
	and x18, x16, x16
	srlw x19, x29, x1
	la x9, test_memory+1911
	lw x8, -939(x9)
	addi x31, x0, -1037
	sll x12, x12, 63
	addi x15, x0, -1
	addi x17, x0, -1
	and x22, x31, x31
	la x11, test_memory+418
	xor x15, x15, x12
	and x30, x14, x15
	or x28, x30, x12
	xor x17, x17, x21
	la x24, test_memory-1069
	lhu x10, 52(x11)
	sw x10, 1533(x24)
	and x5, x2, x17
	or x23, x5, x21
	beq x5, x23, crash_forward
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
	sd x6, 48(x1)
	sd x7, 56(x1)
	sd x8, 64(x1)
	sd x10, 80(x1)
	sd x12, 96(x1)
	sd x13, 104(x1)
	sd x14, 112(x1)
	sd x15, 120(x1)
	sd x16, 128(x1)
	sd x17, 136(x1)
	sd x18, 144(x1)
	sd x19, 152(x1)
	sd x20, 160(x1)
	sd x21, 168(x1)
	sd x22, 176(x1)
	sd x23, 184(x1)
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
reg_x0_init:	.dword 0xffffffffffff8004
reg_x1_init:	.dword 0x0800000000000005
reg_x2_init:	.dword 0x7dd05bffed194e56
reg_x3_init:	.dword 0x25ca6c0d3adaa95d
reg_x4_init:	.dword 0x24ad819765af4cd8
reg_x5_init:	.dword 0xffffffff80000008
reg_x6_init:	.dword 0x01971c322854cce2
reg_x7_init:	.dword 0x224e6746fb0b3441
reg_x8_init:	.dword 0x1503a1eefc3d1b18
reg_x9_init:	.dword 0x0000000000000000
reg_x10_init:	.dword 0xaf02a39fb5b36fa1
reg_x11_init:	.dword 0x732317968fe8eb0c
reg_x12_init:	.dword 0xffffffffffff8008
reg_x13_init:	.dword 0xf01a4cc621790b4f
reg_x14_init:	.dword 0x0000000000000000
reg_x15_init:	.dword 0x0800000000000007
reg_x16_init:	.dword 0x0000000000000004
reg_x17_init:	.dword 0x0000000000000000
reg_x18_init:	.dword 0x7f20e8cc4a2d1082
reg_x19_init:	.dword 0xffffffff80000007
reg_x20_init:	.dword 0x9493c4d115a68ac9
reg_x21_init:	.dword 0xffffffff80000007
reg_x22_init:	.dword 0xffffffff80000008
reg_x23_init:	.dword 0x0000000000000000
reg_x24_init:	.dword 0xdd9e54db7b075115
reg_x25_init:	.dword 0xb8e21b730ee96821
reg_x26_init:	.dword 0x76077a657051e5c2
reg_x27_init:	.dword 0xffffffff80000008
reg_x28_init:	.dword 0x0800000000000004
reg_x29_init:	.dword 0xffffffff80000001
reg_x30_init:	.dword 0xf4a2a3f6ef045e02
reg_x31_init:	.dword 0xffffffffffffff82

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0xc45c6dcd60823f58
reg_x1_output:	.dword 0x620e66d549fe73c3
reg_x2_output:	.dword 0x8305fd7e84c3006c
reg_x3_output:	.dword 0xfa42c949e72427d6
reg_x4_output:	.dword 0xd0cecd38cb6578ea
reg_x5_output:	.dword 0x7396d035f4d8732a
reg_x6_output:	.dword 0x2676822f9e838b98
reg_x7_output:	.dword 0xb8e2d317b460947a
reg_x8_output:	.dword 0x3ac989279f6ead28
reg_x9_output:	.dword 0xeb20a61b59b7d47c
reg_x10_output:	.dword 0xbc07173ce87e4fa9
reg_x11_output:	.dword 0x81c99279f4ec2077
reg_x12_output:	.dword 0xb79ff2df6995113f
reg_x13_output:	.dword 0x7d70f11eac113a19
reg_x14_output:	.dword 0xb32a491d2c3da216
reg_x15_output:	.dword 0xf39b4b8d97969086
reg_x16_output:	.dword 0x1467132684db9593
reg_x17_output:	.dword 0xd06c2700daf916b4
reg_x18_output:	.dword 0xd8f9d00c957b92cc
reg_x19_output:	.dword 0xd7c2ddd3298baaf5
reg_x20_output:	.dword 0x013b96cc7f91983a
reg_x21_output:	.dword 0x46012b208fa5e3d5
reg_x22_output:	.dword 0xf09ec48a9bab46ad
reg_x23_output:	.dword 0x673c4caced325625
reg_x24_output:	.dword 0x61a8cb20a407677f
reg_x25_output:	.dword 0xac43df063c92a857
reg_x26_output:	.dword 0x27dbe3db0063220c
reg_x27_output:	.dword 0x2df7d7e54961070c
reg_x28_output:	.dword 0x9f42aa7b11609461
reg_x29_output:	.dword 0xd31942da72fbceeb
reg_x30_output:	.dword 0x63ebe4822ff1c332
reg_x31_output:	.dword 0xf157a42728417fb4

// Memory Blocks
	.align 8
test_memory:
	.dword 0x4bc4f8b1fc6e1511, 0xf21725ebf1b04c94
	.dword 0xf725daccf0a7ccdd, 0x4c89f382ae7dddba
	.dword 0xf8496fa303ba3778, 0xbb79672c85711729
	.dword 0x2c19ad4a94a080bc, 0x8bc1eded6c90f8d0
	.dword 0x8766fbaffd3063ae, 0xf34ec5b3e058ebd7
	.dword 0x3716994ed11329f4, 0xad90f9bccd54113b
	.dword 0x684c083e470aae84, 0x643f413a0306659c
	.dword 0x8b4dc76ef577579e, 0x57e2a4300e23ce55
	.dword 0x1925dc3570ef3bfb, 0x158e0a9eaf8263cd
	.dword 0x4502f0087c05e746, 0xfc5d19e57e368d0c
	.dword 0x07670684056771cb, 0xb8390462a31cc091
	.dword 0x567d0fb6d460df6e, 0x5e282f601bfdfe61
	.dword 0x64beda9b571af9dd, 0x5b57d32d01b95763
	.dword 0x69a92be0d86c1a09, 0x295cf989e8ae15eb
	.dword 0xcfd3fcf0787894d1, 0x9a1c7e4872475b94
	.dword 0xf4a1272b92a0bf00, 0x529ff62f73434852
	.dword 0xc013ff7aefb6bc79, 0xa017a020e95cfec6
	.dword 0xd388a603dc658eb0, 0x83a7c47f2da219d4
	.dword 0x7c2a0e394c56165c, 0x92a226ca04316772
	.dword 0xd6720316e235fc6a, 0xefb26d8d17a9fcc3
	.dword 0x02eeabac7e8fb634, 0x288ea47a236ef763
	.dword 0x163d53d8caa218f2, 0x892b3cd32d558004
	.dword 0xb6e27d58b4593070, 0x7b84300b2a97e239
	.dword 0x8fa37d0094714d01, 0xb80328abce41cd91
	.dword 0xcc8628488ae87cb3, 0x68a4d57ae5f713e8
	.dword 0x77df5709bf71e3c3, 0x5e7dcad9063778f8
	.dword 0x74213d8796e1a853, 0x2861966a9e576736
	.dword 0xfaa6e2b37abf655a, 0x3074e8fd378e9ddb
	.dword 0x77ca36a9a09858db, 0x1f9dfaa34efb2c40
	.dword 0x95668d7ee289c159, 0x1f548d2129884e6e
	.dword 0x8ec18241750f1e89, 0x4e85308c478dfef5
	.dword 0x0ff086364ea74949, 0xe351ae2fe5f751fc
	.dword 0xf771a067d79e96d1, 0x2bb2bdb3c10aed99
	.dword 0x27122161d27b7b27, 0x789d687c22d23363
	.dword 0x01a64f3af36e5ed8, 0x2c90bf4e11d0ef44
	.dword 0x59c14dd2d5fc9be4, 0xbd96c6372d889f93
	.dword 0x12ccc75ba729d5f9, 0xb60dbaaeba5faa61
	.dword 0xedd4191c1ee221e4, 0x3d3d17fb6f361412
	.dword 0x564f0870289ab044, 0xb30bfdd279768b2f
	.dword 0x2d744412b845ef80, 0x9764dd42aa0bdd7b
	.dword 0xbc5c359fc91358fa, 0x982c8fd4f3902a43
	.dword 0x12c0e754e6425d84, 0xe6713cef018c65fa
	.dword 0x21b0021916d32512, 0x2ed7b17a3ef40304
	.dword 0x135027beba5715b1, 0xf8940dc3b871d3d2
	.dword 0x7b2b2d8c32ce55b8, 0x1ba4eda6d2d87a2e
	.dword 0x8182faf5ec9ebd3c, 0x30d66eea5059f7d7
	.dword 0xa84f10adf583eac8, 0xb684b9e5ed4f3450
	.dword 0x05dcfbe0551f6f4d, 0x6a6bf06c60918bf4
	.dword 0x1fee39b968cb4557, 0x754da6e580f5bc4e
	.dword 0x06d24f28bfc00781, 0x47124bbc0a98c1a7
	.dword 0x02a418ea2fc39a2b, 0xdb8f20f820a479df
	.dword 0x71bd97bfdcac3c69, 0xe77fac2c6c3b2080
	.dword 0x3ee5bd00b14f343e, 0x9ccbc0932c95f80f
	.dword 0x3beffb56be318a09, 0x2b218774d054b4a6
	.dword 0x5abd9fc43cc4873f, 0x607d2acfb9c07bbf
	.dword 0x1f0d36e5ac5eec5a, 0x3aae0633a89e8d51
	.dword 0x2784827bebbf1210, 0x618381ee495bea20
	.dword 0x8825c32815f169c8, 0x4f49fc678c1c8b51
	.dword 0x1c295a74b73a1149, 0xf4e265cf6bcdff3c
	.dword 0x6d41091c0d576db4, 0x5e4571f58f067f85
	.dword 0x52da4d83115f01b4, 0xdded8479d776d46d
	.dword 0xc149a6850fd4f2f3, 0x8fb0bb254a469965
	.dword 0x2f20be7858b1f2cf, 0x3846ba975117b6e4
	.dword 0x8a8dc26acc127e4d, 0x2c4c2121d1e7257a

.align 8
loop_count: .word 0x40

RVTEST_DATA_END

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
	addi x16, x0, 1
	addi x29, x0, -1241
	la x25, test_memory+838
	lui x8, 452179
	div x17, x3, x3
	la x22, test_memory+2251
	sll x16, x16, 63
	xor x5, x10, x3
	lw x11, -586(x25)
	addi x6, x0, -1305
	addi x1, x0, 1503
	addi x9, x0, -1
	addi x21, x0, 1
	addi x20, x0, 573
	lb x28, -1519(x22)
	sll x21, x21, 63
	addi x2, x1, 1113
	xor x9, x9, x16
	addi x24, x29, -922
	divuw x31, x6, x6
	addi x4, x0, -387
	and x23, x19, x9
	or x15, x23, x16
	addi x19, x0, -1
	xor x19, x19, x21
	la x26, test_memory+707
	blt x2, x1, crash_backward
	la x3, test_memory-642
	lwu x30, -695(x26)
	sd x14, 650(x3)
	addw x10, x20, x4
	la x11, test_memory-952
	and x14, x2, x19
	or x18, x15, x21
	la x8, test_memory-182
	lh x2, 1080(x8)
	addi x28, x0, 1
	la x6, test_memory+2068
	la x27, test_memory+1981
	lhu x25, -1582(x6)
	sll x28, x28, 63
	lw x13, -1797(x27)
	lwu x30, 1812(x11)
	sub x29, x0, x30
	addi x26, x0, -1
	addi x5, x0, 615
	addi x31, x0, 472
	sra x24, x5, x31
	xor x26, x26, x28
	and x7, x18, x26
	or x17, x7, x28
	sllw x27, x21, x21
	addi x13, x0, 0
	la x4, test_memory+1399
	addi x30, x0, 1
	addi x23, x0, 1
	la x11, test_memory-496
	addi x6, x0, 0
	addi x20, x0, 19
	addi x21, x0, 187
	sll x23, x23, 63
	la x17, test_memory-479
	la x25, test_memory+2040
	xor x3, x24, x24
	addi x16, x0, -1
	xor x16, x16, x23
	lwu x10, -1135(x4)
	sb x23, -1556(x25)
	and x12, x0, x16
	addi x24, x1, 0
	sll x30, x30, 63
	addi x8, x0, -98
	addi x15, x24, 0
	addi x7, x0, 1024
	lwu x1, 1164(x11)
	addi x31, x0, -1
	addi x5, x21, 1423
	bltu x5, x21, crash_forward
	xor x31, x31, x30
	addi x13, x0, 655
	lhu x9, 943(x17)
	and x19, x2, x31
	and x29, x25, x25
	addi x11, x0, -786
	blt x24, x15, crash_backward
	or x2, x19, x30
	mulhu x1, x5, x5
	srl x18, x7, x7
	addi x21, x0, 986
	addi x10, x13, 1052
	remu x9, x15, x6
	addi x27, x0, 402
	sra x4, x11, x21
	remw x15, x27, x5
	addi x1, x0, 1011
	addi x18, x0, -1558
	la x28, test_memory+382
	sraw x24, x24, x24
	sub x14, x20, x8
	addi x5, x0, 1200
	la x11, test_memory+1988
	sb x9, -1174(x11)
	addi x3, x0, -37
	addi x17, x0, 1134
	sraw x6, x27, x3
	ld x26, -158(x28)
	mulw x29, x18, x18
	sltu x7, x1, x17
	mulhu x27, x21, x21
	addi x25, x5, 1781
	or x22, x12, x23
	la x14, test_memory-441
	xor x28, x24, x11
	bgeu x12, x22, crash_forward
	remu x17, x21, x13
	la x1, test_memory-985
	addi x4, x0, 808
	bge x5, x25, crash_backward
	la x20, test_memory+1234
	blt x19, x2, crash_backward
	la x10, test_memory-565
	addi x15, x0, -2000
	divu x28, x9, x9
	sub x9, x2, x27
	addi x16, x0, 480
	addi x12, x0, 192
	addi x13, x0, -1562
	sb x6, 1993(x1)
	slt x11, x13, x13
	mulh x17, x16, x16
	ld x18, -858(x20)
	mulhu x21, x4, x15
	addi x3, x0, 1
	la x26, test_memory-394
	rem x24, x20, x20
	sh x18, 1270(x26)
	la x25, test_memory-401
	addi x1, x0, 1
	add x16, x21, x21
	mul x9, x19, x14
	xor x22, x12, x13
	addi x27, x0, 1804
	sll x1, x1, 63
	lb x23, 902(x10)
	la x21, test_memory-690
	sd x29, 1129(x25)
	addi x17, x0, -735
	lhu x5, 970(x21)
	addi x18, x27, 1038
	sll x3, x3, 63
	srlw x12, x5, x27
	addi x8, x0, -1
	srl x10, x20, x24
	la x16, test_memory+87
	remuw x24, x12, x4
	xor x8, x8, x3
	addi x31, x17, -1455
	la x20, test_memory+1635
	sd x22, -835(x20)
	la x9, test_memory+598
	lh x22, -278(x9)
	and x6, x24, x8
	addi x30, x0, -1
	addi x5, x0, 0
	addi x15, x0, 547
	or x7, x6, x3
	xor x30, x30, x1
	lbu x29, 1314(x14)
	sw x3, 733(x16)
	addi x25, x0, 0
	bge x31, x17, crash_backward
	and x2, x26, x30
	bltu x5, x25, crash_forward
	or x4, x23, x1
	bltu x7, x6, crash_forward
	addi x19, x0, -1968
	sra x28, x15, x19
	addi x10, x0, 1849
	addi x21, x0, 107
	addi x31, x0, 844
	la x28, test_memory-810
	la x26, test_memory+959
	addi x18, x0, 1
	addi x7, x0, -889
	la x27, test_memory-1134
	bltu x26, x26, crash_backward
	la x17, test_memory+2363
	sd x11, 1410(x28)
	la x5, test_memory-1372
	addi x6, x0, 2030
	sll x4, x10, x10
	addi x12, x0, 1260
	la x4, test_memory+2681
	divuw x20, x21, x7
	mulh x30, x31, x31
	sh x31, -1419(x17)
	la x9, test_memory+2523
	la x21, test_memory-234
	blt x12, x12, crash_backward
	addi x17, x0, 398
	sw x7, -667(x26)
	srlw x19, x31, x5
	lb x10, -2001(x4)
	addi x23, x0, -1167
	div x16, x12, x12
	sh x10, 1628(x27)
	addi x28, x0, 710
	srl x3, x29, x3
	slt x20, x17, x17
	la x14, test_memory+108
	addi x31, x0, 1675
	sb x12, 782(x14)
	srlw x15, x6, x23
	lbu x7, 1221(x21)
	ld x24, -1635(x9)
	la x25, test_memory+1758
	sll x18, x18, 63
	la x23, test_memory-1556
	addi x14, x0, 849
	divu x30, x28, x31
	sh x31, -1350(x25)
	la x3, test_memory+422
	la x6, test_memory+661
	la x27, test_memory+224
	sw x31, 644(x27)
	addi x8, x0, -1
	xor x8, x8, x18
	remw x12, x13, x27
	addi x10, x0, -928
	and x22, x24, x8
	addi x7, x10, -1412
	bltu x10, x7, crash_forward
	lhu x15, 329(x6)
	addi x31, x0, 399
	lw x29, 1780(x5)
	la x16, test_memory+61
	la x21, test_memory-956
	or x11, x22, x18
	la x20, test_memory+301
	lb x19, 2045(x23)
	addi x1, x31, 738
	addi x17, x14, 697
	lhu x4, 589(x16)
	lb x9, 652(x20)
	sb x30, 1605(x21)
	ld x24, 442(x3)
	la x20, test_memory-719
	addi x6, x0, 1
	addi x21, x0, 1
	sll x6, x6, 63
	mulh x4, x8, x8
	addi x18, x0, -1
	la x12, test_memory+381
	la x25, test_memory+784
	ld x2, 251(x12)
	sb x31, -351(x25)
	addi x13, x0, -952
	sll x21, x21, 63
	addi x16, x0, -1261
	addi x15, x0, 1
	ld x22, 1151(x20)
	addw x10, x0, x0
	la x29, test_memory+2296
	la x5, test_memory-434
	lh x31, -1966(x29)
	addi x3, x0, -1
	addi x11, x0, 1269
	xor x3, x3, x21
	xor x18, x18, x6
	sll x15, x15, 63
	and x8, x13, x3
	addi x26, x11, 1484
	addi x23, x0, -1
	mulhsu x24, x13, x16
	and x27, x23, x18
	xor x23, x23, x15
	and x7, x16, x23
	la x31, test_memory+1079
	sb x30, -222(x31)
	lbu x17, 1111(x5)
	or x14, x2, x15
	addi x16, x0, 0
	addi x4, x0, 0
	bne x16, x4, crash_forward
	addi x28, x0, 1308
	or x30, x29, x6
	la x20, test_memory-1757
	or x9, x9, x21
	addi x19, x0, 1
	sll x19, x19, 63
	sub x29, x16, x29
	la x24, test_memory-893
	bge x9, x8, crash_forward
	addi x13, x0, -1
	lhu x10, 2019(x20)
	rem x21, x0, x0
	sraiw x4, x26, 6
	lhu x25, 1657(x24)
	la x31, test_memory+1852
	la x3, test_memory-317
	xor x13, x13, x19
	addi x8, x0, -1474
	bltu x30, x27, crash_forward
	and x22, x26, x13
	sd x10, -1844(x31)
	or x12, x21, x19
	addi x16, x0, 56
	bltu x12, x22, crash_backward
	addi x1, x0, -1553
	and x29, x8, x16
	lwu x9, 353(x3)
	la x5, test_memory-119
	subw x2, x28, x1
	addi x20, x0, -821
	la x27, test_memory-1924
	la x30, test_memory-399
	ld x15, 903(x30)
	la x4, test_memory-96
	la x16, test_memory-136
	addi x28, x0, -759
	addi x24, x20, -1885
	addi x11, x0, -1856
	ori x25, x14, 1322
	la x1, test_memory+394
	divw x13, x0, x21
	addi x31, x0, -894
	addi x26, x0, 1050
	la x2, test_memory+962
	mulw x18, x26, x26
	lbu x6, 403(x4)
	lwu x10, 1996(x27)
	sra x3, x19, x19
	mulhu x7, x29, x29
	mulhsu x12, x31, x31
	ld x14, 414(x1)
	lwu x17, 703(x5)
	addi x8, x0, -447
	addi x23, x8, -1162
	beq x20, x24, crash_forward
	divu x22, x28, x11
	lhu x21, -48(x2)
	sh x7, 1140(x16)
	addi x6, x0, 1677
	addi x28, x0, 1138
	slliw x11, x7, 30
	addi x8, x0, -1464
	addi x14, x0, -70
	mulhu x21, x31, x11
	addi x13, x14, -76
	addi x24, x0, 547
	bltu x14, x13, crash_forward
	mulw x10, x29, x29
	subw x3, x11, x29
	addi x18, x24, 1274
	addi x3, x0, 1759
	addi x29, x0, 1
	addiw x11, x13, -531
	addi x14, x0, 196
	la x19, test_memory+1056
	sll x29, x29, 63
	mul x23, x2, x2
	rem x26, x6, x6
	or x5, x20, x20
	remw x21, x30, x7
	remw x26, x28, x26
	addi x16, x0, 638
	rem x5, x13, x13
	addi x25, x0, 1
	sw x31, -1048(x19)
	or x11, x19, x11
	mulhsu x4, x8, x16
	addi x1, x0, -1
	la x2, test_memory+2664
	lw x7, -1768(x2)
	la x23, test_memory+242
	xor x1, x1, x29
	mulhsu x11, x30, x13
	div x4, x22, x22
	bge x24, x18, crash_forward
	blt x2, x2, crash_forward
	divuw x10, x3, x14
	la x11, test_memory-1009
	sub x5, x19, x22
	and x13, x1, x20
	lb x6, 73(x23)
	la x21, test_memory+2560
	addi x24, x0, -1122
	sll x25, x25, 63
	lbu x7, -1633(x21)
	addi x9, x0, 225
	addi x19, x0, 1
	addi x31, x0, 565
	addi x20, x31, 2020
	addi x4, x0, 1540
	addi x15, x0, -1
	and x17, x7, x1
	remuw x8, x24, x4
	sltu x22, x28, x9
	sll x19, x19, 63
	addi x26, x0, -1
	addi x5, x0, 1525
	xor x15, x15, x25
	xor x26, x26, x19
	addi x13, x0, -721
	addi x10, x0, -1815
	or x27, x17, x29
	addi x21, x0, 1
	and x16, x12, x26
	addi x8, x0, 0
	addi x28, x0, 0
	addi x9, x0, 204
	sll x21, x21, 63
	bge x27, x17, crash_forward
	addw x31, x5, x28
	bne x8, x28, crash_forward
	lhu x18, 1961(x11)
	or x2, x16, x19
	la x24, test_memory+1223
	mul x7, x13, x10
	addi x22, x0, -1723
	addi x3, x0, -1
	and x12, x18, x15
	or x30, x27, x25
	addi x23, x5, 1506
	sd x4, -447(x24)
	bgeu x5, x23, crash_backward
	sraw x4, x9, x22
	xor x3, x3, x21
	sll x15, x9, x9
	la x13, test_memory+1683
	addi x18, x0, 1013
	and x6, x22, x3
	srl x20, x9, x9
	addi x4, x0, 1449
	remu x24, x4, x4
	or x14, x6, x21
	la x7, test_memory+309
	la x29, test_memory+340
	addi x10, x0, 1
	addi x16, x0, 0
	addi x17, x0, 275
	addi x22, x0, 0
	lwu x28, -192(x29)
	sll x10, x10, 63
	addi x26, x0, -1
	bltu x28, x28, crash_backward
	xor x26, x26, x10
	lh x5, -245(x7)
	remuw x8, x18, x17
	lh x11, -761(x13)
	and x9, x16, x26
	or x31, x9, x10
	bge x31, x9, crash_backward
	lui x25, 311641
	blt x16, x22, crash_backward
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
	sd x8, 64(x1)
	sd x9, 72(x1)
	sd x10, 80(x1)
	sd x11, 88(x1)
	sd x12, 96(x1)
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
	sd x24, 192(x1)
	sd x25, 200(x1)
	sd x26, 208(x1)
	sd x27, 216(x1)
	sd x28, 224(x1)
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
reg_x0_init:	.dword 0xbe70e547dc1abcc7
reg_x1_init:	.dword 0xffffffffffffffff
reg_x2_init:	.dword 0x52cebfb839036a15
reg_x3_init:	.dword 0x2bd4528a22f117ad
reg_x4_init:	.dword 0x4f311bd9b8cfc2ff
reg_x5_init:	.dword 0xf313d99a645ae820
reg_x6_init:	.dword 0xffffffffffff8004
reg_x7_init:	.dword 0x0000000000000008
reg_x8_init:	.dword 0xffffffff80000003
reg_x9_init:	.dword 0x0000000000000003
reg_x10_init:	.dword 0x3e6e8e80e35afb83
reg_x11_init:	.dword 0x60b587097eb78fa5
reg_x12_init:	.dword 0x64bf9e884f25b5d5
reg_x13_init:	.dword 0xd7ab07d6b745e12c
reg_x14_init:	.dword 0xea2d1e476e35ab81
reg_x15_init:	.dword 0xffffffffffff8009
reg_x16_init:	.dword 0xff128ff9fa751072
reg_x17_init:	.dword 0xffffffffffff8003
reg_x18_init:	.dword 0x834129e9120dfa19
reg_x19_init:	.dword 0xea477d7ffeb190c2
reg_x20_init:	.dword 0xffffffffffffffef
reg_x21_init:	.dword 0xffffffffffff8004
reg_x22_init:	.dword 0x0000000000000000
reg_x23_init:	.dword 0xffffffffffffffff
reg_x24_init:	.dword 0xffffffffffffffff
reg_x25_init:	.dword 0xffffffffffffffff
reg_x26_init:	.dword 0x53946e0739eff2e5
reg_x27_init:	.dword 0x6cb37ee5680d0219
reg_x28_init:	.dword 0x7f2195e081fa561c
reg_x29_init:	.dword 0xac70eef0c2809d2a
reg_x30_init:	.dword 0x6095bcdce991e3c8
reg_x31_init:	.dword 0x5c026cc229e04865

RVTEST_DATA_BEGIN

	.align 8
xreg_output_data:
reg_x0_output:	.dword 0xda090dbc6d427476
reg_x1_output:	.dword 0x3fb1a06ffc40e268
reg_x2_output:	.dword 0x62b4086d02c93d1e
reg_x3_output:	.dword 0x000ca2db82314e85
reg_x4_output:	.dword 0x107ab74be180dbfb
reg_x5_output:	.dword 0x118d313623d9b1d4
reg_x6_output:	.dword 0x7bd5bbf881a385c6
reg_x7_output:	.dword 0xe2134fc867504296
reg_x8_output:	.dword 0x33a32824cb9f8c77
reg_x9_output:	.dword 0xc152b0d48c27ecf4
reg_x10_output:	.dword 0x46f744776adce663
reg_x11_output:	.dword 0x74b93021ed3b8232
reg_x12_output:	.dword 0x10f861b31d6b928c
reg_x13_output:	.dword 0x284302b82ea02725
reg_x14_output:	.dword 0x0344181900436e34
reg_x15_output:	.dword 0x7bfb9ee829abb5e2
reg_x16_output:	.dword 0x0a5e9909d1334fb3
reg_x17_output:	.dword 0xfc56a08f6e9306b7
reg_x18_output:	.dword 0xcc92f6f133267a8a
reg_x19_output:	.dword 0xf47c2d9a92ef545f
reg_x20_output:	.dword 0x68b587603c44c0b7
reg_x21_output:	.dword 0x61589ecd4db92f70
reg_x22_output:	.dword 0xdda7c37898e2e54a
reg_x23_output:	.dword 0x02f770c0373ab518
reg_x24_output:	.dword 0xe78f4a8ecf7e1437
reg_x25_output:	.dword 0x8badc1297d61fd08
reg_x26_output:	.dword 0xcaa7eb0c3a56836e
reg_x27_output:	.dword 0xaa18dc5ec5f7f2af
reg_x28_output:	.dword 0x3fb2d593f7ea9129
reg_x29_output:	.dword 0xd8399f1e0fcf0dab
reg_x30_output:	.dword 0xf1835e69d5d4f384
reg_x31_output:	.dword 0x2f3db0869d409d7c

// Memory Blocks
	.align 8
test_memory:
	.dword 0xc84bf11356a5cd52, 0xf913d869b4869c7a
	.dword 0x94541a37c477bc2d, 0xd6f8f5c868eb3e08
	.dword 0xa0eacbd0747f33ce, 0x5aff599339a6ac0a
	.dword 0xcff63f7e34e3ba9f, 0x2a6a89b763d6a794
	.dword 0x38b51b376b17db8e, 0xb3d5b05c838300e3
	.dword 0xe75abc26d6dde124, 0x46bb3b6cf75d1a90
	.dword 0x716acbd4ba74add5, 0xbe5870554b17ec02
	.dword 0x2a56838464494599, 0xd04ff80948193724
	.dword 0x0f2041dba73edcbb, 0x841aa749bb1be557
	.dword 0x14f056c8ad687ff0, 0x038607293a66bfaa
	.dword 0x9fd029a30b2ca9aa, 0x3a7461ce72b9f648
	.dword 0x226f1d8eef7c58ae, 0x050a57749c492b31
	.dword 0x8826d824764c7be4, 0xa3b23fb88c3ef42c
	.dword 0x35aace514619c76d, 0x041ddb156da207fc
	.dword 0x6d293b7cdd2c46fa, 0x19f318a605438ad1
	.dword 0x6661e6eef8d1415b, 0xf958f434b2e12e01
	.dword 0xc4995b6ed5174156, 0xe565b0754d1d16f7
	.dword 0x7995752d400157ba, 0xccbff187d998c16b
	.dword 0xf03a69e18ce3eab2, 0x43d87bc6cd9f50d3
	.dword 0x492daf34dceea65e, 0x763a9ac2799f0519
	.dword 0xea56635f460c629f, 0x93cd7484f978c68d
	.dword 0xe5691c108a7b1232, 0x3bc0cd1d28a7fd1c
	.dword 0x34273f940f0b0f00, 0x6983fe59cab426c2
	.dword 0x48d84c31dd1657b3, 0x88ce27d52980e13d
	.dword 0x6905b1d3e535928c, 0xf0aadb33a3285b02
	.dword 0x0de821eba1c1e973, 0xfaeec8abfb575f74
	.dword 0x937f79943190134f, 0xe1ac2fc72fe17253
	.dword 0xb33ca9f72d421e97, 0x2777186730b6ae72
	.dword 0x23b742efc952d129, 0x7dc5980a47cc5bac
	.dword 0xa25e83f055d6b15a, 0x4eb8a74d81247018
	.dword 0x30b01723381c0c4d, 0x795e4bb6bd2f707b
	.dword 0x5a7cdad503148d88, 0xa94619afbb8763fe
	.dword 0x80665d121f083bc4, 0x784d52cec0b9cf20
	.dword 0xd745ed8d58baef04, 0x3c18245d1ac1e9ed
	.dword 0xacd869c1e12a93e8, 0xc401ca13c4338570
	.dword 0x8a18275d829dd042, 0x28a59929812a5465
	.dword 0x9e60a0ddab1fdce9, 0x2fbf378dc2188b32
	.dword 0x020dc87510ffa8cd, 0x3e4083714acb0b18
	.dword 0x7e03253220b5994b, 0xb35fef076ea88ca5
	.dword 0xada51e61a5f47bc2, 0x2a4a548db9947d6d
	.dword 0x34911931a0df7c66, 0x214f868f1e3584f9
	.dword 0xf7074c996da83654, 0x0511206379eae4fe
	.dword 0x85c36f741d7530e5, 0x80af5af81bbb28d1
	.dword 0x5a2fa4f27ca25e46, 0x2167e9d46139d81a
	.dword 0xd8af4b30f9726f48, 0x00d72459c20920c7
	.dword 0xfa759028b8611074, 0xf54bff4c5377ac44
	.dword 0xc935f0c83db36462, 0x2fa39a90e90a13e8
	.dword 0xab3b065f5fe54f4a, 0xaa2967372fc2a8b2
	.dword 0xb052463bb96767db, 0x184529ba1ff18234
	.dword 0x55c19796a30aa14b, 0x63905c85bf8208ce
	.dword 0x6b65e3b150b402ae, 0x3480b6b9bc5a6f1f
	.dword 0x24680439f8c3ff8b, 0x936ddb2de6b4ceb9
	.dword 0xcce7b3f1d14245ac, 0xa69473b6fda0dc13
	.dword 0xe1d265930d981436, 0xc3193ca8bf5865c3
	.dword 0x4b1624ee21b06ff8, 0x0632c49c630012ec
	.dword 0x88bee65434f6c907, 0x10c8e472dd1114f4
	.dword 0xb38ee8368621e58a, 0x27453398da3fc07a
	.dword 0x17890b10414225d1, 0x413ffc8db17e4187
	.dword 0xe4ee4382016775ac, 0xa56975a09bf9df03
	.dword 0x589d8abd87a47efa, 0xadc741fdece48169
	.dword 0xd1d7f1288f79f180, 0xab5a7eeb61c370be
	.dword 0x7760b73b9e0df3fb, 0x86c2e14dc2177dbe
	.dword 0x5b0b90ac13411277, 0x61b7a77221c20a58
	.dword 0xe74975ca12f33de1, 0xdb77630a27cda55d

.align 8
loop_count: .word 0x40

RVTEST_DATA_END

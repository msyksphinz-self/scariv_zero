命令デコーダ
============

RVC命令の展開機能
-----------------

RISC-VにはRVCと呼ばれる16ビット短縮命令が定義されています。
RVCはRISC-V ISAアルファベットでは'C'と定義されています。

RVC命令の命令識別は、命令ビットの下位2ビットにより識別できます。

- 00 : RVC命令 Quadrant 0
- 01 : RVC命令 Quadrant 1
- 10 : RVC命令 Quadrant 2
- 11 : 通常命令 32ビット以上

それぞれのRVC命令は、32ビットの命令に等価変換することができます。
それぞれのRVC命令について、等価な32ビット命令を示します。

=============================== ========= =====================
RVC命令                         Quadrant  展開命令
=============================== ========= =====================
`c.addi4spn rd', nzuimm`        00        `addi rd, x2, nzuimm`
`c.fld      rd', offset(rs1')`  00        `fld rd, offset(rs1)`
`c.lw       rd', offset(rs1')`  00        `lw rd, offset(rs1)`
`c.flw      rd', offset(rs1')`  00        `flw rd, offset(rs1)`
`c.ld       rd', offset(rs1')`  00        `ld rd, offset(rs1)`
`c.fsd      rd', offset(rs1')`  00        `fsd rs2, offset(rs1)`
`c.sw       rd', offset(rs1')`  00        `sw rs2, offset(rs1)`
`c.fsw      rd', offset(rs1')`  00        `fsw rs2, offset(rs1)`
`c.sd       rd', offset(rs1')`  00        `sd rs2, offset(rs1)`
`c.nop`                         01        `nop`
`c.addi     rd, nzimm`          01        `addi rd, rd, nzimm`
`c.jal      offset`             01        `jal x1, offset`
`c.addiw    rd, imm`            01        `addiw rd, rd, imm`
`c.li       rd, uimm`           01        `addi rd, x0, imm`
`c.addi16sp rd',nzimm`          01        `addi x2, x2, nzimm`
`c.lui      rd, nzimm`          01        `lui rd, nzimm`
`c.srli     rd', uimm`          01        `srli rd, rd, shamt`
`c.srli64   rd', uimm`          01        `srli rd, rd, shamt`
`c.srai     rd', uimm`          01        `srai rd, rd, shamt`
`c.srai64   rd', uimm`          01        `srai rd, rd, shamt`
`c.andi     rd', uimm`          01        `andi rd,  rd, imm`
`c.sub      rd', rd'`           01        `sub rd, rd, rs2`
`c.xor      rd', rd'`           01        `xor rd, rd, rs2`
`c.or       rd', rd'`           01        `or rd, rd, rs2`
`c.and      rd', rd'`           01        `and rd, rd, rs2`
`c.subw     rd', rs2`           01        `subw rd, rd, rs2`
`c.addw     rd', rs2`           01        `addw rd, rd, rs2`
`c.j        offset`             01        `jal x0, offset`
`c.beqz     rs1, offset`        01        `beq rs1, x0, offset`
`c.bnez     rs1, offset`        10        `bne rs1, x0, offset`
`c.slli     rd, uimm`           10        `slli rd, rd, shamt`
`c.fldsp    rd, offset(x2)`     10        `fld rd, offset(x2)`
`c.lwsp     rd, offset`         10        `lw rd, offset(x2)`
`c.flwsp    rd, offset`         10        `flw rd, offset(x2)`
`c.ldsp     rd, offset(x2)`     10        `ld rd, offset(x2)`
`c.jr       rd`                 10        `jalr x0, 0(rs1)`
`c.mv       rd, rs2`            10        `add rd, x0, rs2`
`c.ebreak`                      10        `ebreak`
`c.jalr     rs1`                10        `jalr x1, 0(rs1)`
`c.add      rd, rs2`            10        `add rd, rd, rs2`
`c.fsdsp    rs2, offset(x2)`    10        `fsd rs2, offset(sp)`
`c.swsp     rs2, offset(x2)`    10        `sw rs2, offset(sp)`
`c.fswsp    rs2, offset(x2)`    10        `fsw rs2, offset(sp)`
`c.sdsp     rs2, offset(x2)`    10        `sd rs2, offset(sp)`
=============================== ========= =====================

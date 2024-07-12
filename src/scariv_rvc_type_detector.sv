// ------------------------------------------------------------------------
// NAME : scariv_rvc_type_detector
// TYPE : module
// ------------------------------------------------------------------------
// RVC Instruction Type detector
// ------------------------------------------------------------------------
// Input: 16-bit RVC instruction
// Output: 32-bit normal instruction
// ------------------------------------------------------------------------

module scariv_rvc_type_detector
  (
   input logic [15: 0]  i_rvc_inst,
   output decoder_inst_cat_pkg::inst_cat_t    o_inst_cat,
   output decoder_inst_cat_pkg::inst_subcat_t o_inst_subcat
   );

wire [ 9: 0]            w_addi4spn_imm = {i_rvc_inst[10: 7], i_rvc_inst[12:11], i_rvc_inst[5], i_rvc_inst[6], 2'b00};
wire [ 6: 0]            w_lw_imm       = {i_rvc_inst[    5], i_rvc_inst[12:10], i_rvc_inst[6], 2'b00};
wire [ 7: 0]            w_ld_imm       = {i_rvc_inst[ 6: 5], i_rvc_inst[12:10], 3'b000};
wire [ 7: 0]            w_lwsp_imm     = {i_rvc_inst[ 3: 2], i_rvc_inst[   12], i_rvc_inst[ 6: 4], 2'b00};
wire [ 8: 0]            w_ldsp_imm     = {i_rvc_inst[ 4: 2], i_rvc_inst[   12], i_rvc_inst[ 6: 5], 3'b000};
wire [ 7: 0]            w_swsp_imm     = {i_rvc_inst[ 8: 7], i_rvc_inst[12: 9], 2'b00};
wire [ 8: 0]            w_sdsp_imm     = {i_rvc_inst[ 9: 7], i_rvc_inst[12:10], 3'b000};
wire [31: 0]            w_lui_imm      = {{15{i_rvc_inst[12]}}, i_rvc_inst[ 6: 2], 12'h000};
wire [11: 0]            w_addi16sp_imm = {{ 3{i_rvc_inst[12]}}, i_rvc_inst[ 4: 3], i_rvc_inst[5], i_rvc_inst[2], i_rvc_inst[6], 4'b0000};
wire [11: 0]            w_addi_imm     = {{ 7{i_rvc_inst[12]}}, i_rvc_inst[ 6: 2]};
wire [20: 0]            w_j_imm        = {{10{i_rvc_inst[12]}}, i_rvc_inst[    8], i_rvc_inst[10: 9], i_rvc_inst[6], i_rvc_inst[7], i_rvc_inst[2], i_rvc_inst[11], i_rvc_inst[ 5: 3], 1'b0};
wire [12: 0]            w_b_imm        = {{ 5{i_rvc_inst[12]}}, i_rvc_inst[ 6: 5], i_rvc_inst[2], i_rvc_inst[11:10], i_rvc_inst[ 4: 3], 1'b0};
wire [ 5: 0]            w_shamt        = {i_rvc_inst[12], i_rvc_inst[ 6: 2]};

wire [ 4: 0]            x0   = 5'h0;
wire [ 4: 0]            ra   = 5'h1;
wire [ 4: 0]            sp   = 5'h2;
wire [ 4: 0]            rs1p = {2'b01, i_rvc_inst[ 9: 7]};
wire [ 4: 0]            rs2p = {2'b01, i_rvc_inst[ 4: 2]};
wire [ 4: 0]            rs2  = i_rvc_inst[ 6: 2];
wire [ 4: 0]            rd   = i_rvc_inst[11: 7];

logic [ 6: 0]           w_opc;

always_comb begin
  w_opc = 'h0;
  case ({i_rvc_inst[15:13], i_rvc_inst[1: 0]})
    5'b000_00 : begin
      w_opc = |i_rvc_inst[12: 5] ? 7'h13 : 7'h1f;
      // `c.addi4spn rd', nzuimm`        00        `addi rd, x2, nzuimm`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b001_00 : begin
      // `c.fld      rd', offset(rs1')`  00        `fld rd, offset(rs1)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_LD;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_FPU;
    end
    5'b010_00 : begin
      // `c.lw       rd', offset(rs1')`  00        `lw rd, offset(rs1)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_LD;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b011_00 : begin
`ifdef RV32
      // `c.flw      rd', offset(rs1')`  00        `flw rd, offset(rs1)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_LD;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
`else // RV32
      // `c.ld       rd', offset(rs1')`  00        `ld rd, offset(rs1)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_LD;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
`endif // RV32
    end
    5'b100_00 : begin
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT__;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT__;
    end
    5'b101_00 : begin
      // `c.fsd      rd', offset(rs1')`  00        `fsd rs2, offset(rs1)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ST;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b110_00 : begin
      // `c.sw       rd', offset(rs1')`  00        `sw rs2, offset(rs1)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ST;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b111_00 : begin
`ifdef RV32
      // `c.fsw      rd', offset(rs1')`  00        `fsw rs2, offset(rs1)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ST;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_FPU;
`else // RV32
      // `c.sd       rd', offset(rs1')`  00        `sd rs2, offset(rs1)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ST;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
`endif // RV32
    end

    5'b000_01 : begin
      // `c.nop`                         01        `nop`
      // `c.addi     rd, nzimm`          01        `addi rd, rd, nzimm`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b001_01 : begin
`ifdef RV32
 	  // `c.jal      offset`             01        `jal x1, offset`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_BR;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_BRANCH;
`else // RV32
      // `c.addiw    rd, imm`            01        `addiw rd, rd, imm`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
`endif // RV32
    end
    5'b010_01 : begin
      // `c.li       rd, uimm`           01        `addi rd, x0, imm`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b011_01 : begin
      if (i_rvc_inst[11: 7] == 'h0 || i_rvc_inst[11: 7] == 'h2) begin
        // `c.addi16sp rd',nzimm`          01        `addi x2, x2, nzimm`
        o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
        o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
      end else begin
        // `c.lui      rd, nzimm`          01        `lui rd, nzimm`
        o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
        o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
      end // else: !if(i_rvc_inst[11: 7] == 'h0 || i_rvc_inst[11: 7] == 'h2)
    end // case: 5'b011_01
    5'b100_01 : begin
      case (i_rvc_inst[11:10])
        2'b00 : begin
          // `c.srli     rd', uimm`          01        `srli rd, rd, shamt`
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
        end
        2'b01 : begin
          // `c.srai     rd', uimm`          01        `srai rd, rd, shamt`
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
        end
        2'b10 : begin
          // `c.andi     rd', uimm`          01        `andi rd,  rd, imm`
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
        end
        2'b11 : begin
          case ({i_rvc_inst[12], i_rvc_inst[6:5]})
            3'b000 : begin
              // `c.sub      rd', rd'`           01        `sub rd, rd, rs2`
              o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
              o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
            end
            3'b001 : begin
              // `c.xor      rd', rd'`           01        `xor rd, rd, rs2`
              o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
              o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
            end
            3'b010 : begin
              // `c.or       rd', rd'`           01        `or rd, rd, rs2`
              o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
              o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
            end
            3'b011 : begin
              // `c.and      rd', rd'`           01        `and rd, rd, rs2`
              o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
              o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
            end
            3'b100 : begin
              // `c.subw     rd', rs2`           01        `subw rd, rd, rs2`
              o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
              o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
            end
            3'b101 : begin
              // `c.addw     rd', rs2`           01        `addw rd, rd, rs2`
              o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
              o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
            end
            3'b110 : begin
              o_inst_cat = decoder_inst_cat_pkg::INST_CAT__;
              o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT__;
            end
            3'b111 : begin
              o_inst_cat = decoder_inst_cat_pkg::INST_CAT__;
              o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT__;
            end
          endcase // case ({i_rvc_inst[12], i_rvc_inst[6:5]})
        end // case: 2'b11
      endcase // case (i_rvc_inst[11:10])
    end // case: 5'b100_01

    5'b101_01 : begin
      // `c.j        offset`             01        `jal x0, offset`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_BR;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_BRANCH;
    end
    5'b110_01 : begin
      // `c.beqz     rs1, offset`        01        `beq rs1, x0, offset`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_BR;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_BRANCH;
    end
    5'b111_01 : begin
      // `c.bnez     rs1, offset`        10        `bne rs1, x0, offset`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_BR;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_BRANCH;
    end
    5'b000_10 : begin
      // `c.slli     rd, uimm`           10        `slli rd, rd, shamt`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b001_10 : begin
      // `c.fldsp    rd, offset(x2)`     10        `fld rd, offset(x2)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_LD;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_FPU;
    end
    5'b010_10 : begin
      // `c.lwsp     rd, offset`         10        `lw rd, offset(x2)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_LD;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b011_10 : begin
`ifdef RV32
      // `c.flwsp    rd, offset`         10        `flw rd, offset(x2)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_LD;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_FPU;
`else // RV32
      // `c.ldsp     rd, offset(x2)`     10        `ld rd, offset(x2)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_LD;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
`endif // RV32
    end
    5'b100_10 : begin
      if (~i_rvc_inst[12]) begin
        if (i_rvc_inst[6:2] == 'h0) begin
          // `c.jr       rd`                 10        `jalr x0, 0(rs1)`
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT_BR;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_BRANCH;
        end else begin
          // `c.mv       rd, rs2`            10        `add rd, x0, rs2`
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
        end
      end else begin
        if (i_rvc_inst[11:7] == 'h0 && i_rvc_inst[6:2] == 'h0) begin
          // `c.ebreak`                      10        `ebreak`
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT_CSU;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT__;
        end else if (i_rvc_inst[11:7] != 'h0 && i_rvc_inst[6:2] == 'h0) begin
          // `c.jalr     rs1`                10        `jalr x1, 0(rs1)`
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT_BR;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_BRANCH;
        end else if (i_rvc_inst[11:7] != 'h0 && i_rvc_inst[6:2] != 'h0) begin
          // `c.add      rd, rs2`            10        `add rd, rd, rs2`
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ARITH;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
        end else begin
          o_inst_cat = decoder_inst_cat_pkg::INST_CAT__;
          o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT__;
        end
      end // else: !if(i_rvc_inst[12])
    end
    5'b101_10 : begin
      // `c.fsdsp    rs2, offset(x2)`    10        `fsd rs2, offset(sp)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ST;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_FPU;
    end
    5'b110_10 : begin
      // `c.swsp     rs2, offset(x2)`    10        `sw rs2, offset(sp)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ST;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
    end
    5'b111_10 : begin
`ifdef RV32
      // `c.fswsp    rs2, offset(x2)`    10        `fsw rs2, offset(sp)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ST;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_FPU;
`else // RV32
      // `c.sdsp     rs2, offset(x2)`    10        `sd rs2, offset(sp)`
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT_ST;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT_INT;
`endif // RV32
    end
    default : begin
      o_inst_cat = decoder_inst_cat_pkg::INST_CAT__;
      o_inst_subcat = decoder_inst_cat_pkg::INST_SUBCAT__;
    end
  endcase // case ({i_rvc_inst[15:13], i_rvc_inst[1: 0]})
end // always_comb

endmodule // scariv_rvc_type_detector

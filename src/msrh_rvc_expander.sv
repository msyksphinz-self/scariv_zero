module msrh_rvc_expander
  (
   input logic [15: 0]  i_rvc_inst,
   output logic [31: 0] out_32bit
   );

wire [ 7: 0]            w_addi4spn_imm = {i_rv_inst[10: 7], i_rvc_inst[12:11], i_rvc_inst[5], i_rvc_inst[6], 2'b00};
wire [ 6: 0]            w_lw_imm       = {i_rv_inst[    5], i_rvc_inst[12:10], i_rvc_inst[6], 2'b00};
wire [ 7: 0]            w_ld_imm       = {i_rv_inst[ 6: 5], i_rvc_inst[12:10], 3'b000};
wire [ 6: 0]            w_lwsp_imm     = {i_rv_inst[ 3: 2], i_rvc_inst[   12], i_rvc_inst[ 6: 4], 2'b00};
wire [ 7: 0]            w_ldsp_imm     = {i_rv_inst[ 4: 2], i_rvc_inst[   12], i_rvc_inst[ 6: 5], 3'b000};
wire [ 6: 0]            w_swsp_imm     = {i_rv_inst[ 8: 7], i_rvc_inst[12: 9], 2'b00};
wire [ 7: 0]            w_sdsp_imm     = {i_rv_inst[ 9: 7], i_rvc_inst[12:10], 3'b000};
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

always_comb begin
  case ({i_rvc_inst[15:13], i_rvc_inst[1: 0]})
    5'b000_00 : begin
      // `c.addi4spn rd', nzuimm`        00        `addi rd, x2, nzuimm`
      out_32bit = {w_addi4spn_imm, sp, 3'b000, rs2p, opc};
    end
    5'b001_00 : begin
      // `c.fld      rd', offset(rs1')`  00        `fld rd, offset(rs1)`
      out_32bit = {w_ld_imm, rs1p, 3'b011, rs2p, 7'b0000011};
    end
    5'b010_00 : begin
      // `c.lw       rd', offset(rs1')`  00        `lw rd, offset(rs1)`
      out_32bit = {lw_imm, rs1p, 3'b010, rs2p, 7'b0000011};
    end
    5'b011_00 : begin
`ifdef RV32
      // `c.flw      rd', offset(rs1')`  00        `flw rd, offset(rs1)`
      out_32bit = {lw_imm, rs1p, 3'b010, rs2p, 7'b0000111};
`else // RV32
      // `c.ld       rd', offset(rs1')`  00        `ld rd, offset(rs1)`
      out_32bit = {w_ld_imm, rs1p, 3'b011, rs2p, 7'b0000011};
`endif // RV32
    end
    5'b100_00 : begin
      out_32bit = 'h0;
    end
    5'b101_00 : begin
      // `c.fsd      rd', offset(rs1')`  00        `fsd rs2, offset(rs1)`
      out_32bit = {w_ld_imm >> 5, rs2p, rs1p, 3'b011, w_ld_imm[ 4: 0], 7'b0100111};
    end
    5'b110_00 : begin
      // `c.sw       rd', offset(rs1')`  00        `sw rs2, offset(rs1)`
      out_32bit = {lw_imm >> 5, rs2p, rs1p, 3'b010, lw_imm[ 4: 0], 7'b0100011};
    end
    5'b111_00 : begin
`ifdef RV32
      // `c.fsw      rd', offset(rs1')`  00        `fsw rs2, offset(rs1)`
      out_32bit = {lw_imm >> 5, rs2p, rs1p, 3'b010, lw_imm[ 4: 0], 7'b0100111};
`else // RV32
      // `c.sd       rd', offset(rs1')`  00        `sd rs2, offset(rs1)`
      out_32bit = {w_ld_imm >> 5, rs2p, rs1p, 3'b011, w_ld_imm[ 4: 0], 7'b0100011};
`endif // RV32
    end

    5'b000_01 : begin
      // `c.nop`                         01        `nop`
      // `c.addi     rd, nzimm`          01        `addi rd, rd, nzimm`
      out_32bit = {addi_imm, rd, 3'b000, rd, 7'b0010011};
    end
    5'b001_01 : begin
`ifdef RV32
 	  // `c.jal      offset`             01        `jal x1, offset`
      out_32bit = {w_j_imm[20], w_j_imm[10,1], w_j_imm[11], w_j_imm[19,12], ra, 7'b110_1111};
`else // RV32
      // `c.addiw    rd, imm`            01        `addiw rd, rd, imm`
      out_32bit = {w_addi_imm, rd, 3'b000, rd, opc};
`endif // RV32
    end
    5'b010_01 : begin
      // `c.li       rd, uimm`           01        `addi rd, x0, imm`
      out_32bit = {w_addi_imm, x0, 3'b000, rd, 7'b0010011};
    end
    5'b011_01 : begin
      if (i_rvc_inst[11: 7] == 'h0 || i_rvc_inst[11: 7] == 'h2) begin
        // `c.addi16sp rd',nzimm`          01        `addi x2, x2, nzimm`
        out_32bit = {w_addi16sp_imm, rd, 3'b000, rd, opc};
      end else begin
        // `c.lui      rd, nzimm`          01        `lui rd, nzimm`
        out_32bit = {w_lui_imm[31:12], rd, opc};
      end
    end
    5'b100_01 : begin
      case (i_rvc_inst[11:10])
        2'b00 : begin
          // `c.srli     rd', uimm`          01        `srli rd, rd, shamt`
          out_32bit = {w_shamt, rs1p, 3'b101, rs1p, 7'b0010011};
        end
        2'b01 : begin
          // `c.srai     rd', uimm`          01        `srai rd, rd, shamt`
          out_32bit = srli | (1 << 30).U;
        end
        2'b10 : begin
          // `c.andi     rd', uimm`          01        `andi rd,  rd, imm`
          out_32bit = {addi_imm, rs1p, 3'b111, rs1p, 7'b0010011};
        end
        2'b11 : begin
          case ({i_rvc_inst[12], i_rvc_inst[6:5]})
            3'b000 : begin
              // `c.sub      rd', rd'`           01        `sub rd, rd, rs2`
              out_32bit = {rs2p, rs1p, 3'b000, rs1p, 7'b011_0011};
            end
            3'b001 : begin
              // `c.xor      rd', rd'`           01        `xor rd, rd, rs2`
              out_32bit = {rs2p, rs1p, 3'b100, rs1p, 7'b011_0011};
            end
            3'b010 : begin
              // `c.or       rd', rd'`           01        `or rd, rd, rs2`
              out_32bit = {rs2p, rs1p, 3'b110, rs1p, 7'b011_0011};
            end
            3'b011 : begin
              // `c.and      rd', rd'`           01        `and rd, rd, rs2`
              out_32bit = {rs2p, rs1p, 3'b111, rs1p, 7'b011_0011};
            end
            3'b100 : begin
              // `c.subw     rd', rs2`           01        `subw rd, rd, rs2`
              out_32bit = {rs2p, rs1p, 3'b000, rs1p, 7'b011_1011};
            end
            3'b101 : begin
              // `c.addw     rd', rs2`           01        `addw rd, rd, rs2`
              out_32bit = {rs2p, rs1p, 3'b000, rs1p, 7'b011_1011};
            end
            3'b110 : begin
            end
            3'b111 : begin
            end
          endcase // case ({i_rvc_inst[12], i_rvc_inst[6:5]})
        end // case: 2'b11
      endcase // case (i_rvc_inst[11:10])
    end // case: 5'b100_01

    5'b101_01 : begin
      // `c.j        offset`             01        `jal x0, offset`
      out_32bit = {w_j_imm[20], w_j_imm[10:1], w_j_imm[11], w_j_imm[19:12], x0, 7'b110_1111};
    end
    5'b110_01 : begin
      // `c.beqz     rs1, offset`        01        `beq rs1, x0, offset`
      out_32bit = {w_b_imm[12], w_b_imm[10:5], x0, rs1p, 3'b000, w_b_imm[ 4: 1], w_b_imm[11], 7'b110_0011};
    end
    5'b111_01 : begin
      // `c.bnez     rs1, offset`        10        `bne rs1, x0, offset`
      out_32bit = {w_b_imm[12], w_b_imm[10:5], x0, rs1p, 3'b001, w_b_imm[ 4: 1], w_b_imm[11], 7'b110_0011};
    end

    5'b000_10 : begin
      // `c.slli     rd, uimm`           10        `slli rd, rd, shamt`
      out_32bit = {w_shamt, rd, 3'b001, rd, 7'b001_0011};
    end
    5'b001_10 : begin
      // `c.fldsp    rd, offset(x2)`     10        `fld rd, offset(x2)`
      out_32bit = {w_ldsp_imm, sp, 3'b011, rd, 7'b000_0111};
    end
    5'b010_10 : begin
      // `c.lwsp     rd, offset`         10        `lw rd, offset(x2)`
      out_32bit = {w_lwsp_imm, sp, 3'b010, rd, 7'b000_0011};
    end
    5'b011_10 : begin
`ifdef RV32
      // `c.flwsp    rd, offset`         10        `flw rd, offset(x2)`
      out_32bit = {w_lwsp_imm, sp, 3'b010, rd, 7'b000_0111};
`else // RV32
      // `c.ldsp     rd, offset(x2)`     10        `ld rd, offset(x2)`
      out_32bit = {w_ldsp_imm, sp, 3'b011, rd, 7'b000_0011};
`endif // RV32
    end
    5'b100_10 : begin
      if (i_rvc_inst[12]) begin
        if (i_rvc_inst[11:7] != 'h0) begin
          // `c.jr       rd`                 10        `jalr x0, 0(rs1)`
          assign out_32bit = {rs2, rd, 3'b000, x0, 7'b110_0111};
        end else begin
          // `c.mv       rd, rs2`            10        `add rd, x0, rs2`
          assign out_32bit = {rs2, x0, 3'b000, rd, 7'b011_0011};
        end
      end else begin
        if (i_rvc_inst[11:7] == 'h0 && i_rvc_inst[6:2] == 'h0) begin
          // `c.ebreak`                      10        `ebreak`
          assign out_32bit = {jr >> 7, 7'b111_0011} | (1 << 20);
        end else if (i_rvc_inst[11:7] != 'h0 && i_rvc_inst[6:2] == 'h0) begin
          // `c.jalr     rs1`                10        `jalr x1, 0(rs1)`
          assign out_32bit = {rs2, rd, 3'b000, ra, 7'b110_0111};
        end else if (i_rvc_inst[11:7] != 'h0 && i_rvc_inst[6:2] != 'h0) begin
          // `c.add      rd, rs2`            10        `add rd, rd, rs2`
          assign out_32bit = {rs2, rd, 3'b000, rd, 7'b011_0011};
        end
      end // else: !if(i_rvc_inst[12])
    end
    5'b101_10 : begin
      // `c.fsdsp    rs2, offset(x2)`    10        `fsd rs2, offset(sp)`
      out_32bit = {sdsp_imm >> 5, rs2, sp, 3'b011, sdsp_imm[ 4: 0], 7'b0100111};
    end
    5'b110_10 : begin
      // `c.swsp     rs2, offset(x2)`    10        `sw rs2, offset(sp)`
      out_32bit = {swsp_imm >> 5, rs2, sp, 3'b010, swsp_imm[ 4: 0], 7'b0100011};
    end
    5'b111_10 : begin
`ifdef RV32
      // `c.fswsp    rs2, offset(x2)`    10        `fsw rs2, offset(sp)`
      out_32bit = {swsp_imm >> 5, rs2, sp, 3'b010, swsp_imm[ 4: 0], 7'b0100111};
`else // RV32
      // `c.sdsp     rs2, offset(x2)`    10        `sd rs2, offset(sp)`
      out_32bit = {sdsp_imm >> 5, rs2, sp, 3'b011, sdsp_imm[ 4: 0], 7'b0100011};
`endif // RV32
    end
  endcase // case (i_rvc_inst[15:13] , i_rvc_inst[1: 0])
end // always_comb

endmodule // msrh_rvc_expander

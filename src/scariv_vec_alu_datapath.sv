// ------------------------------------------------------------------------
// NAME : scariv_vec_alu_datapath
// TYPE : module
// ------------------------------------------------------------------------
// Arithmetic Unit
// ------------------------------------------------------------------------
// ex0: Decode instruction
// ex1: Send Early-release
// ex2: Get Forwarding data
// ex3: Write Data / Done Report
// ------------------------------------------------------------------------

module scariv_vec_alu_datapath
  import decoder_valu_ctrl_pkg::*;

(
 input op_t                        i_op,
 input logic                       i_is_vmask_op,

 input scariv_vec_pkg::ew_t        i_sew,
 input riscv_pkg::xlen_t           i_vs1,
 input logic                       i_rs1_valid,
 input riscv_pkg::xlen_t           i_rs1,
 input riscv_pkg::xlen_t           i_vs2,
 input riscv_pkg::xlen_t           i_wr_old,
 input [riscv_pkg::XLEN_W/8-1: 0]  i_wr_mask_old,
 input [ 7: 0]                     i_en_mask,
 input riscv_pkg::xlen_t           i_mm_mask,
 input riscv_pkg::xlen_t           i_v0,

 output riscv_pkg::xlen_t          o_alu_res,
 output [riscv_pkg::XLEN_W/8-1: 0] o_mask_res
 );

typedef union packed {
  logic [0:0][63:0] w64;
  logic [1:0][31:0] w32;
  logic [3:0][15:0] w16;
  logic [7:0][ 7:0] w8;
} data_64bit_t;

data_64bit_t w_rs1;
data_64bit_t w_vs1;
data_64bit_t w_vs2;
data_64bit_t w_wr_old;
data_64bit_t w_alu_masked_res;
data_64bit_t w_alu_res;

riscv_pkg::xlen_t w_mask_res;
riscv_pkg::xlen_t w_mask_masked_res;

assign w_vs1    = i_rs1_valid ? w_rs1 : i_vs1;
assign w_vs2    = i_vs2;
assign w_wr_old = i_wr_old;

always_comb begin
  unique case (i_sew)
    scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_rs1.w8 [b] = i_rs1[ 7: 0];
    scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_rs1.w16[b] = i_rs1[15: 0];
    scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_rs1.w32[b] = i_rs1[31: 0];
    scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_rs1.w64[b] = i_rs1[63: 0];
    default             :                             w_rs1 = 'h0;
  endcase // unique case (i_sew)
end

always_comb begin
  case (i_op)
    OP_MV_V_X, OP_MV_V_I, OP_MV_V_V, OP_MV_V_F : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = w_vs1.w64[b];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_ADD : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = w_vs1.w8 [b] + w_vs2.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = w_vs1.w16[b] + w_vs2.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = w_vs1.w32[b] + w_vs2.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = w_vs1.w64[b] + w_vs2.w64[b];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_SUB : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = w_vs2.w8 [b] - w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = w_vs2.w16[b] - w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = w_vs2.w32[b] - w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = w_vs2.w64[b] - w_vs1.w64[b];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_RSUB : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = w_vs1.w8 [b] - w_vs2.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = w_vs1.w16[b] - w_vs2.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = w_vs1.w32[b] - w_vs2.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = w_vs1.w64[b] - w_vs2.w64[b];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MAXU : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = $unsigned(w_vs2.w8 [b]) > $unsigned(w_vs1.w8 [b]) ? w_vs2.w8 [b] : w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = $unsigned(w_vs2.w16[b]) > $unsigned(w_vs1.w16[b]) ? w_vs2.w16[b] : w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = $unsigned(w_vs2.w32[b]) > $unsigned(w_vs1.w32[b]) ? w_vs2.w32[b] : w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = $unsigned(w_vs2.w64[b]) > $unsigned(w_vs1.w64[b]) ? w_vs2.w64[b] : w_vs1.w64[b];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MAX : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = $signed(w_vs2.w8 [b]) > $signed(w_vs1.w8 [b]) ? w_vs2.w8 [b] : w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = $signed(w_vs2.w16[b]) > $signed(w_vs1.w16[b]) ? w_vs2.w16[b] : w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = $signed(w_vs2.w32[b]) > $signed(w_vs1.w32[b]) ? w_vs2.w32[b] : w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = $signed(w_vs2.w64[b]) > $signed(w_vs1.w64[b]) ? w_vs2.w64[b] : w_vs1.w64[b];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MINU : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = $unsigned(w_vs2.w8 [b]) < $unsigned(w_vs1.w8 [b]) ? w_vs2.w8 [b] : w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = $unsigned(w_vs2.w16[b]) < $unsigned(w_vs1.w16[b]) ? w_vs2.w16[b] : w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = $unsigned(w_vs2.w32[b]) < $unsigned(w_vs1.w32[b]) ? w_vs2.w32[b] : w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = $unsigned(w_vs2.w64[b]) < $unsigned(w_vs1.w64[b]) ? w_vs2.w64[b] : w_vs1.w64[b];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MIN : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = $signed(w_vs2.w8 [b]) < $signed(w_vs1.w8 [b]) ? w_vs2.w8 [b] : w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = $signed(w_vs2.w16[b]) < $signed(w_vs1.w16[b]) ? w_vs2.w16[b] : w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = $signed(w_vs2.w32[b]) < $signed(w_vs1.w32[b]) ? w_vs2.w32[b] : w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = $signed(w_vs2.w64[b]) < $signed(w_vs1.w64[b]) ? w_vs2.w64[b] : w_vs1.w64[b];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_SLL : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = w_vs2.w8 [b] << w_vs1.w8 [b][ 2: 0];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = w_vs2.w16[b] << w_vs1.w16[b][ 3: 0];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = w_vs2.w32[b] << w_vs1.w32[b][ 4: 0];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = w_vs2.w64[b] << w_vs1.w64[b][ 5: 0];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_SRL : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = w_vs2.w8 [b] >> w_vs1.w8 [b][ 2: 0];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = w_vs2.w16[b] >> w_vs1.w16[b][ 3: 0];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = w_vs2.w32[b] >> w_vs1.w32[b][ 4: 0];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = w_vs2.w64[b] >> w_vs1.w64[b][ 5: 0];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_SRA : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_res.w8 [b] = $signed(w_vs2.w8 [b]) >> w_vs1.w8 [b][ 2: 0];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_res.w16[b] = $signed(w_vs2.w16[b]) >> w_vs1.w16[b][ 3: 0];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_res.w32[b] = $signed(w_vs2.w32[b]) >> w_vs1.w32[b][ 4: 0];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_res.w64[b] = $signed(w_vs2.w64[b]) >> w_vs1.w64[b][ 5: 0];
        default             :                             w_alu_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_AND  : begin w_alu_res.w64[0] =   w_vs2.w64[0] &  w_vs1.w64[0] ; end
    OP_OR   : begin w_alu_res.w64[0] =   w_vs2.w64[0] |  w_vs1.w64[0] ; end
    OP_XOR  : begin w_alu_res.w64[0] =   w_vs2.w64[0] ^  w_vs1.w64[0] ; end
    OP_ANDN : begin w_alu_res.w64[0] =   w_vs2.w64[0] & ~w_vs1.w64[0] ; end
    OP_ORN  : begin w_alu_res.w64[0] =   w_vs2.w64[0] | ~w_vs1.w64[0] ; end
    OP_NAND : begin w_alu_res.w64[0] = ~(w_vs2.w64[0] &  w_vs1.w64[0]); end
    OP_NOR  : begin w_alu_res.w64[0] = ~(w_vs2.w64[0] |  w_vs1.w64[0]); end
    OP_XNOR : begin w_alu_res.w64[0] = ~(w_vs2.w64[0] ^  w_vs1.w64[0]); end
    default : begin
      w_alu_res = 'h0;
    end
  endcase // case (i_op)
end // always_comb

always_comb begin
  case (i_op)
    OP_MSEQ  : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_res[b] = w_vs2.w8 [b] == w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_res[b] = w_vs2.w16[b] == w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_res[b] = w_vs2.w32[b] == w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_res[b] = w_vs2.w64[b] == w_vs1.w64[b];
        default             :                             w_mask_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MSNE  : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_res[b] = w_vs2.w8 [b] != w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_res[b] = w_vs2.w16[b] != w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_res[b] = w_vs2.w32[b] != w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_res[b] = w_vs2.w64[b] != w_vs1.w64[b];
        default             :                             w_mask_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MSLTU : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_res[b] = w_vs2.w8 [b] < w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_res[b] = w_vs2.w16[b] < w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_res[b] = w_vs2.w32[b] < w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_res[b] = w_vs2.w64[b] < w_vs1.w64[b];
        default             :                             w_mask_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MSLT  : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_res[b] = $signed(w_vs2.w8 [b]) < $signed(w_vs1.w8 [b]);
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_res[b] = $signed(w_vs2.w16[b]) < $signed(w_vs1.w16[b]);
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_res[b] = $signed(w_vs2.w32[b]) < $signed(w_vs1.w32[b]);
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_res[b] = $signed(w_vs2.w64[b]) < $signed(w_vs1.w64[b]);
        default             :                             w_mask_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MSLEU : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_res[b] = w_vs2.w8 [b] <= w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_res[b] = w_vs2.w16[b] <= w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_res[b] = w_vs2.w32[b] <= w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_res[b] = w_vs2.w64[b] <= w_vs1.w64[b];
        default             :                             w_mask_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MSLE  : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_res[b] = $signed(w_vs2.w8 [b]) <= $signed(w_vs1.w8 [b]);
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_res[b] = $signed(w_vs2.w16[b]) <= $signed(w_vs1.w16[b]);
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_res[b] = $signed(w_vs2.w32[b]) <= $signed(w_vs1.w32[b]);
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_res[b] = $signed(w_vs2.w64[b]) <= $signed(w_vs1.w64[b]);
        default             :                             w_mask_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MSGTU : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_res[b] = w_vs2.w8 [b] > w_vs1.w8 [b];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_res[b] = w_vs2.w16[b] > w_vs1.w16[b];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_res[b] = w_vs2.w32[b] > w_vs1.w32[b];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_res[b] = w_vs2.w64[b] > w_vs1.w64[b];
        default             :                             w_mask_res = 'h0;
      endcase // unique case (i_sew)
    end
    OP_MSGT : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_res[b] = $signed(w_vs2.w8 [b]) > $signed(w_vs1.w8 [b]);
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_res[b] = $signed(w_vs2.w16[b]) > $signed(w_vs1.w16[b]);
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_res[b] = $signed(w_vs2.w32[b]) > $signed(w_vs1.w32[b]);
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_res[b] = $signed(w_vs2.w64[b]) > $signed(w_vs1.w64[b]);
        default             :                             w_mask_res = 'h0;
      endcase // unique case (i_sew)
    end
    default : begin
      w_mask_res = 'h0;
    end
  endcase // case (i_op)
end // always_comb

always_comb begin
  if (i_is_vmask_op) begin
    w_alu_masked_res.w64[0] = w_alu_res.w64[0] &  i_mm_mask |
                              w_wr_old.w64 [0] & ~i_mm_mask;
  end else begin
    unique case (i_sew)
      scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_alu_masked_res.w8 [b] = i_en_mask[b] ? w_alu_res.w8 [b] : w_wr_old.w8 [b];
      scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_alu_masked_res.w16[b] = i_en_mask[b] ? w_alu_res.w16[b] : w_wr_old.w16[b];
      scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_alu_masked_res.w32[b] = i_en_mask[b] ? w_alu_res.w32[b] : w_wr_old.w32[b];
      scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_alu_masked_res.w64[b] = i_en_mask[b] ? w_alu_res.w64[b] : w_wr_old.w64[b];
      default             :                             w_alu_masked_res = 'h0;
    endcase // unique case (i_sew)
  end // else: !if(i_is_vmask_op)

  unique case (i_sew)
    scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_mask_masked_res[b] = i_en_mask[b] ? w_mask_res[b] : i_wr_mask_old[b];
    scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_mask_masked_res[b] = i_en_mask[b] ? w_mask_res[b] : i_wr_mask_old[b];
    scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_mask_masked_res[b] = i_en_mask[b] ? w_mask_res[b] : i_wr_mask_old[b];
    scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_mask_masked_res[b] = i_en_mask[b] ? w_mask_res[b] : i_wr_mask_old[b];
    default             :                             w_mask_masked_res = 'h0;
  endcase // unique case (i_sew)
end

assign o_alu_res  = w_alu_masked_res;
assign o_mask_res = w_mask_masked_res;

endmodule // scariv_vec_alu_datapath

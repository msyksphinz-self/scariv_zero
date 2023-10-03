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
  import decoder_vec_ctrl_pkg::*;

(
 input op_t                 i_op,
 input scariv_vec_pkg::ew_t i_sew,
 input [63: 0]              i_vs1,
 input [63: 0]              i_vs2,
 input riscv_pkg::xlen_t    i_rs1,
 input [63: 0]              i_v0,
 output [63: 0]             o_res
 );

typedef union packed {
  logic [0:0][63:0] w64;
  logic [1:0][31:0] w32;
  logic [3:0][15:0] w16;
  logic [7:0][ 7:0] w8;
} data_64bit_t;

data_64bit_t w_vs1;
data_64bit_t w_vs2;
data_64bit_t w_res;

assign w_vs1 = i_vs1;
assign w_vs2 = i_vs2;

always_comb begin
  case (i_op)
    OP_MV_V_X : begin
      unique case (i_sew)
        scariv_vec_pkg::EW8 : for (int b = 0; b < 8; b++) w_res.w8 [b] = i_rs1[ 7: 0];
        scariv_vec_pkg::EW16: for (int b = 0; b < 4; b++) w_res.w16[b] = i_rs1[15: 0];
        scariv_vec_pkg::EW32: for (int b = 0; b < 2; b++) w_res.w32[b] = i_rs1[31: 0];
        scariv_vec_pkg::EW64: for (int b = 0; b < 1; b++) w_res.w64[b] = i_rs1[63: 0];
        default             :                             w_res = 'h0;
      endcase // unique case (i_sew)
    end
    default : begin
      w_res = 'h0;
    end
  endcase // case (i_op)
end // always_comb

assign o_res = w_res;

endmodule // scariv_vec_alu_datapath

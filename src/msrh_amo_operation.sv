// ------------------------------------------------------------------------
// NAME : MSRH Atomic Operations
// TYPE : module
// ------------------------------------------------------------------------
// Atomic Operations
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_amo_operation
  (
   input riscv_pkg::xlen_t             i_data0,
   input riscv_pkg::xlen_t             i_data1,
   input decoder_lsu_ctrl_pkg::rmwop_t i_op,
   output riscv_pkg::xlen_t            o_data
   );

always_comb begin
  case (i_op)
    decoder_lsu_ctrl_pkg::RMWOP_SWAP32 : o_data = i_data0[31: 0];
    decoder_lsu_ctrl_pkg::RMWOP_ADD32  : o_data = i_data0[31: 0] + i_data1[31: 0];
    decoder_lsu_ctrl_pkg::RMWOP_XOR32  : o_data = i_data0[31: 0] ^ i_data1[31: 0];
    decoder_lsu_ctrl_pkg::RMWOP_AND32  : o_data = i_data0[31: 0] & i_data1[31: 0];
    decoder_lsu_ctrl_pkg::RMWOP_OR32   : o_data = i_data0[31: 0] | i_data1[31: 0];
    decoder_lsu_ctrl_pkg::RMWOP_MIN32  : o_data = $signed(i_data0[31: 0]) <  $signed(i_data1[31: 0]) ? i_data0[31: 0] : i_data1[31: 0];
    decoder_lsu_ctrl_pkg::RMWOP_MAX32  : o_data = $signed(i_data0[31: 0]) >= $signed(i_data1[31: 0]) ? i_data0[31: 0] : i_data1[31: 0];
    decoder_lsu_ctrl_pkg::RMWOP_MINU32 : o_data = i_data0[31: 0] <  i_data1[31: 0] ? i_data0[31: 0] : i_data1[31: 0];
    decoder_lsu_ctrl_pkg::RMWOP_MAXU32 : o_data = i_data0[31: 0] >= i_data1[31: 0] ? i_data0[31: 0] : i_data1[31: 0];
`ifdef RV64
    decoder_lsu_ctrl_pkg::RMWOP_SWAP64 : o_data = i_data0[63: 0];
    decoder_lsu_ctrl_pkg::RMWOP_ADD64  : o_data = i_data0[63: 0] + i_data1[63: 0];
    decoder_lsu_ctrl_pkg::RMWOP_XOR64  : o_data = i_data0[63: 0] ^ i_data1[63: 0];
    decoder_lsu_ctrl_pkg::RMWOP_AND64  : o_data = i_data0[63: 0] & i_data1[63: 0];
    decoder_lsu_ctrl_pkg::RMWOP_OR64   : o_data = i_data0[63: 0] | i_data1[63: 0];
    decoder_lsu_ctrl_pkg::RMWOP_MIN64  : o_data = $signed(i_data0[63: 0]) <  $signed(i_data1[63: 0]) ? i_data0[63: 0] : i_data1[63: 0];
    decoder_lsu_ctrl_pkg::RMWOP_MAX64  : o_data = $signed(i_data0[63: 0]) >= $signed(i_data1[63: 0]) ? i_data0[63: 0] : i_data1[63: 0];
    decoder_lsu_ctrl_pkg::RMWOP_MINU64 : o_data = i_data0[63: 0] <  i_data1[63: 0] ? i_data0[63: 0] : i_data1[63: 0];
    decoder_lsu_ctrl_pkg::RMWOP_MAXU64 : o_data = i_data0[63: 0] >= i_data1[63: 0] ? i_data0[63: 0] : i_data1[63: 0];
`endif //  `ifdef RV64
    default                            : o_data = 'hx;
  endcase // case (i_op)
end // always_comb

endmodule // msrh_amo_operation

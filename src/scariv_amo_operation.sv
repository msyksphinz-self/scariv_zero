// ------------------------------------------------------------------------
// NAME : scariv_amo_operation
// TYPE : module
// ------------------------------------------------------------------------
// Atomic Operations
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_amo_operation
  (
   input riscv_pkg::xlen_t             i_data0,
   input riscv_pkg::xlen_t             i_data1,
   input decoder_lsu_ctrl_pkg::rmwop_t i_op,
   input decoder_lsu_ctrl_pkg::size_t  i_size,
   output riscv_pkg::xlen_t            o_data
   );

always_comb begin
  if (i_size == decoder_lsu_ctrl_pkg::SIZE_W) begin
    case (i_op)
      decoder_lsu_ctrl_pkg::RMWOP_SWAP : o_data = i_data0[31: 0];
      decoder_lsu_ctrl_pkg::RMWOP_ADD  : o_data = i_data0[31: 0] + i_data1[31: 0];
      decoder_lsu_ctrl_pkg::RMWOP_XOR  : o_data = i_data0[31: 0] ^ i_data1[31: 0];
      decoder_lsu_ctrl_pkg::RMWOP_AND  : o_data = i_data0[31: 0] & i_data1[31: 0];
      decoder_lsu_ctrl_pkg::RMWOP_OR   : o_data = i_data0[31: 0] | i_data1[31: 0];
      decoder_lsu_ctrl_pkg::RMWOP_MIN  : o_data = $signed(i_data0[31: 0]) <  $signed(i_data1[31: 0]) ? i_data0[31: 0] : i_data1[31: 0];
      decoder_lsu_ctrl_pkg::RMWOP_MAX  : o_data = $signed(i_data0[31: 0]) >= $signed(i_data1[31: 0]) ? i_data0[31: 0] : i_data1[31: 0];
      decoder_lsu_ctrl_pkg::RMWOP_MINU : o_data = i_data0[31: 0] <  i_data1[31: 0] ? i_data0[31: 0] : i_data1[31: 0];
      decoder_lsu_ctrl_pkg::RMWOP_MAXU : o_data = i_data0[31: 0] >= i_data1[31: 0] ? i_data0[31: 0] : i_data1[31: 0];
      default                          : o_data = 'hx;
    endcase // case (i_op)
`ifdef RV64
  end else if (i_size == decoder_lsu_ctrl_pkg::SIZE_DW) begin
    case (i_op)
      decoder_lsu_ctrl_pkg::RMWOP_SWAP : o_data = i_data0[63: 0];
      decoder_lsu_ctrl_pkg::RMWOP_ADD  : o_data = i_data0[63: 0] + i_data1[63: 0];
      decoder_lsu_ctrl_pkg::RMWOP_XOR  : o_data = i_data0[63: 0] ^ i_data1[63: 0];
      decoder_lsu_ctrl_pkg::RMWOP_AND  : o_data = i_data0[63: 0] & i_data1[63: 0];
      decoder_lsu_ctrl_pkg::RMWOP_OR   : o_data = i_data0[63: 0] | i_data1[63: 0];
      decoder_lsu_ctrl_pkg::RMWOP_MIN  : o_data = $signed(i_data0[63: 0]) <  $signed(i_data1[63: 0]) ? i_data0[63: 0] : i_data1[63: 0];
      decoder_lsu_ctrl_pkg::RMWOP_MAX  : o_data = $signed(i_data0[63: 0]) >= $signed(i_data1[63: 0]) ? i_data0[63: 0] : i_data1[63: 0];
      decoder_lsu_ctrl_pkg::RMWOP_MINU : o_data = i_data0[63: 0] <  i_data1[63: 0] ? i_data0[63: 0] : i_data1[63: 0];
      decoder_lsu_ctrl_pkg::RMWOP_MAXU : o_data = i_data0[63: 0] >= i_data1[63: 0] ? i_data0[63: 0] : i_data1[63: 0];
      default                          : o_data = 'hx;
    endcase // case (i_op)
`endif //  `ifdef RV64
  end else begin // if (i_size == decoder_lsu_ctrl_pkg::SIZE_DW)
    o_data = 'hx;
  end // else: !if(i_size == decoder_lsu_ctrl_pkg::SIZE_DW)
end // always_comb

endmodule // scariv_amo_operation

// ------------------------------------------------------------------------
// NAME : scariv_bitmanip_alu
// TYPE : module
// ------------------------------------------------------------------------
// Bit-manipulation extension ALU
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_zicond_alu
  import decoder_alu_ctrl_pkg::*;
(
 input riscv_pkg::xlen_t  i_rs1,
 input riscv_pkg::xlen_t  i_rs2,
 input op_t               i_op,

 output riscv_pkg::xlen_t o_out,
 output logic             o_valid
 );

`ifdef NEVER
always_comb begin
  o_valid = 1'b1;
  case (i_op)
    OP_CZERO_EQZ : begin
      o_out = i_rs2 == 'h0 ? 'h0 : i_rs1;
    end
    OP_CZERO_NEZ : begin
      o_out = i_rs2 != 'h0 ? 'h0 : i_rs1;
    end
    default : begin
      o_out = 'h0;
      o_valid = 1'b0;
    end
  endcase // case (i_op)
end // always_comb

`else // NEVER

assign o_out = 'h0;
assign o_valid = 1'b0;

`endif // !`ifdef NEVER

endmodule // scariv_zicond_alu

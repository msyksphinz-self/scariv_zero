module msrh_decoder
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.slave disp_from_frontend,
   disp_if.master disp_to_renamer
   );

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    disp_to_renamer.valid   <= 1'b0;
    disp_to_renamer.pc_addr <= 'h0;
  end else begin
    disp_to_renamer.valid <= disp_from_frontend.valid;
    disp_to_renamer.pc_addr <= disp_from_frontend.pc_addr;
  end
end
assign disp_from_frontend.ready = disp_to_renamer.ready;

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : decode_loop
  msrh_pkg::disp_t disp_to_rename_d;

logic [ 2: 0] w_op;
logic         w_imm;
logic         w_size;
logic         w_sign;

  decoder_inst_ctrl u_decoder_inst_ctrl
                             (
                              .inst(disp_from_frontend.inst[d_idx].inst),

                              .op(w_op),
                              .imm(w_imm),
                              .size(w_size),
                              .sign(w_sign)
                              );


  always_comb begin
    disp_to_rename_d = disp_from_frontend.inst[d_idx];

    disp_to_rename_d.op   = w_op;
    disp_to_rename_d.imm  = w_imm;
    disp_to_rename_d.size = w_size;
    disp_to_rename_d.sign = w_sign;

  end

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      disp_to_renamer.inst[d_idx] <= 'h0;
    end else begin
      disp_to_renamer.inst[d_idx] <= disp_to_rename_d;
    end
  end

end
endgenerate


endmodule // msrh_decoder

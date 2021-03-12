module msrh_decoder
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.slave  iq_disp,
   disp_if.master id_disp
   );

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    id_disp.valid   <= 1'b0;
    id_disp.pc_addr <= 'h0;
  end else begin
    id_disp.valid <= iq_disp.valid;
    id_disp.cat   <= iq_disp.cat;
    id_disp.pc_addr <= iq_disp.pc_addr;
  end
end
assign iq_disp.ready = id_disp.ready;

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : decode_loop
  msrh_pkg::disp_t w_id_disp_next;

logic [ 2: 0] w_op;
logic         w_imm;
logic         w_size;
logic         w_sign;

  decoder_inst_ctrl u_decoder_inst_ctrl
                             (
                              .inst(iq_disp.inst[d_idx].inst),

                              .op(w_op),
                              .imm(w_imm),
                              .size(w_size),
                              .sign(w_sign)
                              );


  always_comb begin
    w_id_disp_next = iq_disp.inst[d_idx];

    w_id_disp_next.op   = w_op;
    w_id_disp_next.imm  = w_imm;
    w_id_disp_next.size = w_size;
    w_id_disp_next.sign = w_sign;

  end

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      id_disp.inst[d_idx] <= 'h0;
    end else begin
      id_disp.inst[d_idx] <= w_id_disp_next;
    end
  end

end
endgenerate


endmodule // msrh_decoder

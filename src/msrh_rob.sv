module msrh_rob
  (
   input logic                             i_clk,
   input logic                             i_reset_n,

   disp_if.watch                           sc_disp,
   input logic [msrh_pkg::DISP_SIZE-1:0]   i_old_rd_valid,
   input logic [msrh_pkg::RNID_W-1:0]      i_old_rd_rnid[msrh_pkg::DISP_SIZE],

   output logic [msrh_pkg::CMT_BLK_W-1: 0] o_sc_new_cmt_id,

   input msrh_pkg::done_rpt_t i_done_rpt [msrh_pkg::CMT_BUS_SIZE]
   );

logic [msrh_pkg::CMT_BLK_W-1:0]            r_cmt_id;
logic [msrh_pkg::DISP_SIZE-1:0]            w_disp_grp_id;
logic [msrh_pkg::CMT_BLK_SIZE-1:0]         w_entry_all_done;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_cmt_id <= 'h0;
  end else begin
    r_cmt_id <= sc_disp.valid ? r_cmt_id + 'h1 : r_cmt_id;
  end
end

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign w_disp_grp_id[d_idx] = sc_disp.inst[d_idx].valid;
end
endgenerate


generate for (genvar c_idx = 0; c_idx < msrh_pkg::CMT_BLK_SIZE; c_idx++) begin : entry_loop
logic w_load_valid;
  assign w_load_valid = sc_disp.valid & (r_cmt_id == c_idx);

  msrh_rob_entry u_entry
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_cmt_id (c_idx[msrh_pkg::CMT_BLK_W-1:0]),

     .i_load_valid   (w_load_valid),
     .i_load_pc_addr (sc_disp.pc_addr),
     .i_load_inst    (sc_disp.inst),
     .i_load_grp_id  (w_disp_grp_id),
     .i_old_rd_valid (i_old_rd_valid),
     .i_old_rd_rnid  (i_old_rd_rnid),

     .i_done_rpt (i_done_rpt),

     .o_block_all_done (w_entry_all_done[c_idx])
     );

end
endgenerate

assign o_sc_new_cmt_id = r_cmt_id;

endmodule // msrh_rob

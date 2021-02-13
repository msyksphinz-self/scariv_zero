module msrh_rob
  (
   input logic                             i_clk,
   input logic                             i_reset_n,

   input logic                             i_disp_valid,
   input msrh_pkg::disp_t [msrh_pkg::DISP_SIZE-1:0] i_disp,
   input logic [msrh_pkg::DISP_SIZE-1:0]   i_old_rd_valid,
   input logic [msrh_pkg::RNID_W-1:0]      i_old_rd_rnid[msrh_pkg::DISP_SIZE],

   output logic [msrh_pkg::CMT_BLK_W-1: 0] o_new_ctag,

   input msrh_pkg::done_rpt_t i_done_rpt [msrh_pkg::CMT_BUS_SIZE]
   );

logic [msrh_pkg::CMT_BLK_W-1:0]            r_ctag;
logic [msrh_pkg::DISP_SIZE-1:0]            w_disp_ii;
logic [msrh_pkg::CMT_BLK_SIZE-1:0]         w_entry_all_done;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ctag <= 'h0;
  end else begin
    r_ctag <= i_disp_valid ? r_ctag + 'h1 : r_ctag;
  end
end

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign w_disp_ii[d_idx] = i_disp[d_idx].valid;
end
endgenerate


generate for (genvar c_idx = 0; c_idx < msrh_pkg::CMT_BLK_SIZE; c_idx++) begin : entry_loop
logic w_load_valid;
  assign w_load_valid = i_disp_valid & (r_ctag == c_idx);

  msrh_rob_entry u_entry
    (
     .i_clk (i_clk),
     .i_reset_n (i_reset_n),

     .i_ctag (c_idx[msrh_pkg::CMT_BLK_W-1:0]),

     .i_load_valid   (w_load_valid),
     .i_load_ii      (w_disp_ii),
     .i_old_rd_valid (i_old_rd_valid),
     .i_old_rd_rnid  (i_old_rd_rnid),

     .i_done_rpt (i_done_rpt),

     .o_block_all_done (w_entry_all_done[c_idx])
     );

end
endgenerate


endmodule // msrh_rob

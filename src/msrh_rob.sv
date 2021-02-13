module msrh_rob
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic                           i_disp_valid,
   input logic [msrh_pkg::DISP_SIZE-1:0] i_old_rd_valid,
   input logic [msrh_pkg::RNID_W-1:0]    i_old_rd_rnid[msrh_pkg::DISP_SIZE],

   output logic [msrh_pkg::CMT_BLK_W-1: 0] o_new_ctag
   );

logic [msrh_pkg::CMT_BLK_W-1:0]            r_ctag;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ctag <= 'h0;
  end else begin
    r_ctag <= i_disp_valid ? r_ctag + 'h1 : r_ctag;
  end
end

generate for (genvar c_idx = 0; c_idx < msrh_pkg::CMT_BLK_SIZE; c_idx++) begin : entry_loop
logic w_load_valid;
  assign w_load_valid = i_disp_valid & (r_ctag == c_idx);

  msrh_rob_entry u_entry
                             (
                              .i_clk (i_clk),
                              .i_reset_n (i_reset_n),

                              .i_load_valid (w_load_valid),
                              .i_old_rd_valid (i_old_rd_valid),
                              .i_old_rd_rnid (i_old_rd_rnid)
                              );

end
endgenerate


endmodule // msrh_rob

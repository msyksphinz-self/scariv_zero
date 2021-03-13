module msrh_rob
  (
   input logic                             i_clk,
   input logic                             i_reset_n,

   disp_if.watch                           sc_disp,
   input logic [msrh_conf_pkg::DISP_SIZE-1:0]   i_old_rd_valid,
   input logic [msrh_pkg::RNID_W-1:0]      i_old_rd_rnid[msrh_conf_pkg::DISP_SIZE],

   output logic [msrh_pkg::CMT_BLK_W-1: 0] o_sc_new_cmt_id,

   input msrh_pkg::done_rpt_t i_done_rpt [msrh_pkg::CMT_BUS_SIZE],
   br_upd_if.slave            ex3_br_upd_if,

   output msrh_pkg::commit_blk_t o_commit
   );

logic [msrh_pkg::CMT_BLK_W-1:0]            w_in_cmt_id, w_out_cmt_id;
logic [msrh_conf_pkg::DISP_SIZE-1:0]            w_disp_grp_id;
logic [msrh_pkg::CMT_BLK_SIZE-1:0]         w_entry_all_done;
logic [msrh_conf_pkg::DISP_SIZE-1:0]            w_entry_done_grp_id[msrh_pkg::CMT_BLK_SIZE];

//
// LRQ Pointer
//
logic                                      w_in_vld, w_out_vld;
assign w_in_vld  = sc_disp.valid;
assign w_out_vld = w_entry_all_done[w_out_cmt_id];

inoutptr #(.SIZE(msrh_pkg::CMT_BLK_SIZE)) u_cmt_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                    .i_in_vld (w_in_vld ), .o_in_ptr (w_in_cmt_id  ),
                                                    .i_out_vld(w_out_vld), .o_out_ptr(w_out_cmt_id));


generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  assign w_disp_grp_id[d_idx] = sc_disp.inst[d_idx].valid;
end
endgenerate


generate for (genvar c_idx = 0; c_idx < msrh_pkg::CMT_BLK_SIZE; c_idx++) begin : entry_loop
logic w_load_valid;
  assign w_load_valid = sc_disp.valid & (w_in_cmt_id == c_idx);

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

     .o_block_all_done (w_entry_all_done[c_idx]),
     .o_block_done_grp_id (w_entry_done_grp_id[c_idx]),
     .i_commit_finish (w_entry_all_done[c_idx] & (w_out_cmt_id == c_idx)),

     .br_upd_if (ex3_br_upd_if)
     );

end
endgenerate

assign o_sc_new_cmt_id = w_in_cmt_id;

assign o_commit.commit = w_entry_all_done[w_out_cmt_id];
assign o_commit.cmt_id = w_out_cmt_id;
assign o_commit.grp_id = w_entry_done_grp_id[w_out_cmt_id];

endmodule // msrh_rob

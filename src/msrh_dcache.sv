module msrh_dcache
  #(
    parameter RD_PORT_NUM = msrh_conf_pkg::LSU_INST_NUM
    )
(
   input logic i_clk,
   input logic i_reset_n,

   // LSU_INST_NUM ports from pipe, and STQ read and update port, PTW
   l1d_rd_if.slave l1d_rd_if[RD_PORT_NUM],
   l1d_wr_if.slave l1d_stq_wr_if,
   l1d_wr_if.slave l1d_ext_wr_if
   );

msrh_lsu_pkg::dc_update_t r_rp2_dc_update;

msrh_lsu_pkg::dc_read_req_t  w_dc_read_req [RD_PORT_NUM];
msrh_lsu_pkg::dc_read_resp_t w_dc_read_resp[RD_PORT_NUM];

msrh_dcache_array
  #(
    .READ_PORT_NUM(RD_PORT_NUM)
    )
u_dcache_array
  (
  .i_clk     (i_clk    ),
  .i_reset_n (i_reset_n),

  .i_dc_update (r_rp2_dc_update),
  .i_dc_read_req (w_dc_read_req ),
  .o_dc_read_resp(w_dc_read_resp)
   );

generate for (genvar p_idx = 0; p_idx < RD_PORT_NUM; p_idx++) begin : port_loop
  assign w_dc_read_req [p_idx].valid = l1d_rd_if[p_idx].s0_valid;
  assign w_dc_read_req [p_idx].paddr = l1d_rd_if[p_idx].s0_paddr;
  assign w_dc_read_req [p_idx].h_pri = l1d_rd_if[p_idx].s0_h_pri;

  assign l1d_rd_if[p_idx].s1_hit      = w_dc_read_resp[p_idx].hit ;
  assign l1d_rd_if[p_idx].s1_miss     = w_dc_read_resp[p_idx].miss;
  assign l1d_rd_if[p_idx].s1_conflict = w_dc_read_resp[p_idx].conflict;
  assign l1d_rd_if[p_idx].s1_data     = w_dc_read_resp[p_idx].data;

  assign l1d_rd_if[p_idx].s1_replace_valid = w_dc_read_resp[p_idx].replace_valid;
  assign l1d_rd_if[p_idx].s1_replace_way   = w_dc_read_resp[p_idx].replace_way;
  assign l1d_rd_if[p_idx].s1_replace_paddr = w_dc_read_resp[p_idx].replace_paddr;
end
endgenerate


// -------------
// Update of DC
// -------------
assign r_rp2_dc_update.valid = l1d_ext_wr_if.valid | l1d_stq_wr_if.valid;
assign r_rp2_dc_update.addr  = l1d_ext_wr_if.valid ? l1d_ext_wr_if.paddr : l1d_stq_wr_if.paddr;
assign r_rp2_dc_update.data  = l1d_ext_wr_if.valid ? l1d_ext_wr_if.data  : l1d_stq_wr_if.data;
assign r_rp2_dc_update.be    = l1d_ext_wr_if.valid ? l1d_ext_wr_if.be    : l1d_stq_wr_if.be;

assign l1d_stq_wr_if.conflict = l1d_ext_wr_if.valid & l1d_stq_wr_if.valid;
assign l1d_ext_wr_if.conflict = 1'b0;

endmodule // msrh_dcache

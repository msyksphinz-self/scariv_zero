module msrh_dcache
  #(
    parameter RD_PORT_NUM = msrh_conf_pkg::LSU_INST_NUM + 1 + 1 + 1
    )
(
   input logic i_clk,
   input logic i_reset_n,

   // LSU_INST_NUM ports from pipe, and STQ read and update port, PTW
   l1d_rd_if.slave l1d_rd_if[RD_PORT_NUM],
   l1d_wr_if.slave l1d_wr_if,

   // L2 cache response
   l2_resp_if.slave  l1d_ext_resp,

   // LRQ search interface
   lrq_search_if.master lrq_search_if
   );

msrh_lsu_pkg::dc_update_t r_rp2_dc_update;

msrh_lsu_pkg::dc_read_req_t  w_dc_read_req [RD_PORT_NUM];
msrh_lsu_pkg::dc_read_resp_t w_dc_read_resp[RD_PORT_NUM];

msrh_dcache_array
  u_dcache_array
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_dc_update (r_rp2_dc_update),
     .i_dc_read_req (w_dc_read_req ),
     .o_dc_read_resp(w_dc_read_resp)
     );

generate for (genvar p_idx = 0; p_idx < RD_PORT_NUM; p_idx++) begin : port_loop
  assign w_dc_read_req [p_idx].valid = l1d_rd_if[p_idx].valid;
  assign w_dc_read_req [p_idx].paddr = l1d_rd_if[p_idx].paddr;

  assign l1d_rd_if[p_idx].hit      = w_dc_read_resp[p_idx].hit ;
  assign l1d_rd_if[p_idx].miss     = w_dc_read_resp[p_idx].miss;
  assign l1d_rd_if[p_idx].conflict = w_dc_read_resp[p_idx].conflict;
  assign l1d_rd_if[p_idx].data     = w_dc_read_resp[p_idx].data;

end
endgenerate


// ==========================
// L2 Reponse
// RESP1 : Getting Data
// ==========================
logic r_rp1_l1d_exp_resp_valid;
logic [msrh_pkg::LRQ_ENTRY_W-1:0] r_rp1_lrq_resp_tag;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] r_rp1_lrq_resp_data;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_rp1_l1d_exp_resp_valid <= 1'b0;
    r_rp1_lrq_resp_tag <= 'h0;
    r_rp1_lrq_resp_data <= 'h0;
  end else begin
    r_rp1_l1d_exp_resp_valid <= l1d_ext_resp.valid &
                                (l1d_ext_resp.payload.tag[msrh_lsu_pkg::L2_CMD_TAG_W-1:msrh_lsu_pkg::L2_CMD_TAG_W-2] == msrh_lsu_pkg::L2_UPPER_TAG_L1D);
    r_rp1_lrq_resp_tag       <= l1d_ext_resp.payload.tag[msrh_pkg::LRQ_ENTRY_W-1:0];
    r_rp1_lrq_resp_data      <= l1d_ext_resp.payload.data;
  end
end


// --------------------------------------------------
// Interface of LRQ Search Entry to get information
// --------------------------------------------------
assign lrq_search_if.valid = r_rp1_l1d_exp_resp_valid;
assign lrq_search_if.index = r_rp1_lrq_resp_tag;

// ===========================
// L2 Reponse
// RESP2 : Search LRQ Entiers
// ===========================

logic r_rp2_valid;
msrh_lsu_pkg::lrq_entry_t r_rp2_searched_lrq_entry;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] r_rp2_resp_data;
logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1: 0] r_rp2_be;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_rp2_valid <= 1'b0;
    r_rp2_searched_lrq_entry <= 'h0;
    r_rp2_resp_data <= 'h0;
    r_rp2_be <= 'h0;
  end else begin
    r_rp2_valid <= r_rp1_l1d_exp_resp_valid;
    r_rp2_searched_lrq_entry <= lrq_search_if.lrq_entry;
    r_rp2_resp_data <= r_rp1_lrq_resp_data;
    r_rp2_be        <= {msrh_lsu_pkg::DCACHE_DATA_B_W{1'b1}};
  end
end


// -------------
// Update of DC
// -------------
assign r_rp2_dc_update.valid = r_rp2_valid  | l1d_wr_if.valid;
assign r_rp2_dc_update.addr  = r_rp2_valid ? r_rp2_searched_lrq_entry.paddr :
                               l1d_wr_if.paddr;
assign r_rp2_dc_update.data  = r_rp2_valid ? r_rp2_resp_data :
                               l1d_wr_if.data;
assign r_rp2_dc_update.be    = r_rp2_valid ? r_rp2_be :
                               l1d_wr_if.be;

assign l1d_wr_if.conflict = r_rp2_valid & l1d_wr_if.valid;

endmodule // msrh_dcache

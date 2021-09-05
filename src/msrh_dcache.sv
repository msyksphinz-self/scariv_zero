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
   l1d_wr_if.slave l1d_merge_if,

   // L2 cache response
   l2_resp_if.slave  l1d_ext_resp,

   // LRQ search interface
   lrq_search_if.master lrq_search_if
   );

msrh_lsu_pkg::dc_update_t r_rp2_dc_update;

msrh_lsu_pkg::dc_read_req_t  w_dc_read_req [RD_PORT_NUM];
msrh_lsu_pkg::dc_read_resp_t w_dc_read_resp[RD_PORT_NUM];

msrh_dcache_array
  #(.READ_PORT_NUM(RD_PORT_NUM))
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
  assign l1d_rd_if[p_idx].s1_replace_data  = w_dc_read_resp[p_idx].replace_data;
  assign l1d_rd_if[p_idx].s1_replace_paddr = w_dc_read_resp[p_idx].replace_paddr;
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
                                (l1d_ext_resp.payload.tag[msrh_lsu_pkg::L2_CMD_TAG_W-1:msrh_lsu_pkg::L2_CMD_TAG_W-2] == msrh_lsu_pkg::L2_UPPER_TAG_RD_L1D);
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
logic                                     w_rp2_merge_valid;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] w_rp2_merge_data;
assign w_rp2_merge_valid = r_rp2_valid | l1d_merge_if.valid;
generate for (genvar b_idx = 0; b_idx < msrh_lsu_pkg::DCACHE_DATA_B_W; b_idx++) begin : merge_byte_loop
  assign w_rp2_merge_data[b_idx*8 +: 8] = l1d_merge_if.be[b_idx] ? l1d_merge_if.data[b_idx*8 +: 8] :
                                          r_rp2_resp_data[b_idx*8 +: 8];
end
endgenerate

assign r_rp2_dc_update.valid = w_rp2_merge_valid | l1d_wr_if.valid;
assign r_rp2_dc_update.addr  = r_rp2_valid ? r_rp2_searched_lrq_entry.paddr :
                               l1d_wr_if.paddr;
assign r_rp2_dc_update.data  = r_rp2_valid ? w_rp2_merge_data :
                               l1d_wr_if.data;
assign r_rp2_dc_update.be    = r_rp2_valid ? r_rp2_be :
                               l1d_wr_if.be;

assign l1d_wr_if.conflict = r_rp2_valid & l1d_wr_if.valid;


`ifdef SIMULATION
import "DPI-C" function void record_l1d_load
(
 input longint rtl_time,
 input longint paddr,
 input int ram_addr,
 input int unsigned array[msrh_conf_pkg::DCACHE_DATA_W/32],
 input int     size
);

int unsigned l1d_array[msrh_conf_pkg::DCACHE_DATA_W/32];
generate for (genvar idx = 0; idx < msrh_conf_pkg::DCACHE_DATA_W/32; idx++) begin : array_loop
  assign l1d_array[idx] = r_rp2_resp_data[idx*32+:32];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (r_rp2_valid) begin
      /* verilator lint_off WIDTH */
      record_l1d_load($time,
                      r_rp2_searched_lrq_entry.paddr,
                      r_rp2_searched_lrq_entry.paddr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW],
                      l1d_array,
                      msrh_lsu_pkg::DCACHE_DATA_B_W);
      // $fwrite(msrh_pkg::STDERR, "%t : L1D Load-In   : %0x(%x) <= ",
      //         $time,
      //         r_rp2_searched_lrq_entry.paddr,
      //         r_rp2_searched_lrq_entry.paddr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW]);
      // for (int i = msrh_lsu_pkg::DCACHE_DATA_B_W/4-1; i >=0 ; i--) begin
      //   $fwrite(msrh_pkg::STDERR, "%08x", r_rp2_resp_data[i*32 +: 32]);
      //   if (i != 0) begin
      //     $fwrite(msrh_pkg::STDERR, "_");
      //   end else begin
      //     $fwrite(msrh_pkg::STDERR, "\n");
      //   end
      // end
    end // if (l1d_wr_if.valid)
  end // if (i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)
`endif // SIMULATION


endmodule // msrh_dcache

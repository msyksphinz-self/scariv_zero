// ------------------------------------------------------------------------
// NAME : scariv_store_requestor
// TYPE : module
// ------------------------------------------------------------------------
// Store Requester for L2 Write
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_store_requestor
  import scariv_lsu_pkg::*;
  (
   input logic  i_clk,
   input logic  i_reset_n,

   // Forward check interface from LSU Pipeline
   fwd_check_if.slave  fwd_check_if[scariv_conf_pkg::LSU_INST_NUM],

   // Store Requestor Monitor
   st_req_info_if.master st_req_info_if,

   uc_write_if.slave  uc_write_if,
   l1d_evict_if.slave l1d_evict_if,

   // Snoop Interface
   streq_snoop_if.slave  streq_snoop_if,

   l2_req_if.master  l1d_ext_wr_req
   );

logic           st_ext_arbiter;

logic           r_l1d_evict_req_valid;
evict_payload_t r_ext_evict_payload;

// ===============
// L1D Eviction
// ===============
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_l1d_evict_req_valid <= 1'b0;
    r_ext_evict_payload <= 'h0;
  end else begin
    if (l1d_evict_if.valid & l1d_evict_if.ready) begin
      r_l1d_evict_req_valid <= 1'b1;
      r_ext_evict_payload <= l1d_evict_if.payload;
    end else if (r_l1d_evict_req_valid &
                 (st_ext_arbiter == 1'b0) &
                 l1d_ext_wr_req.ready) begin
      r_l1d_evict_req_valid <= 1'b0;
    end
  end // else: !if(i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign l1d_evict_if.ready = !r_l1d_evict_req_valid;


// =========
// UC Store
// =========
logic           r_uc_wr_req_valid;
scariv_pkg::paddr_t                r_uc_wr_paddr;
riscv_pkg::xlen_t                r_uc_wr_data;
logic [riscv_pkg::XLEN_W/8-1: 0] r_uc_wr_strb;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_uc_wr_req_valid <= 1'b0;

    r_uc_wr_paddr <= 'h0;
    r_uc_wr_data  <= 'h0;
    r_uc_wr_strb  <= 'h0;
  end else begin
    if (uc_write_if.valid & uc_write_if.ready) begin
      r_uc_wr_req_valid <= 1'b1;

      r_uc_wr_paddr <= uc_write_if.paddr;
      r_uc_wr_data  <= uc_write_if.data;
      r_uc_wr_strb  <= uc_write_if.size == decoder_lsu_ctrl_pkg::SIZE_DW ? 'h0ff :
                       uc_write_if.size == decoder_lsu_ctrl_pkg::SIZE_W  ? 'h00f :
                       uc_write_if.size == decoder_lsu_ctrl_pkg::SIZE_H  ? 'h003 :
                       uc_write_if.size == decoder_lsu_ctrl_pkg::SIZE_B  ? 'h001 :
                       'h0;
    end else if (r_uc_wr_req_valid &
                 (st_ext_arbiter == 1'b1) &
                 l1d_ext_wr_req.ready) begin
      r_uc_wr_req_valid <= 1'b0;
    end
  end // else: !if(i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign uc_write_if.ready = !r_uc_wr_req_valid;
assign uc_write_if.is_empty = !r_uc_wr_req_valid;

assign st_ext_arbiter = r_l1d_evict_req_valid ? 1'b0 :
                        r_uc_wr_req_valid     ? 1'b1 :
                        1'b0;

always_comb begin
  l1d_ext_wr_req.valid           = r_l1d_evict_req_valid | r_uc_wr_req_valid;
  l1d_ext_wr_req.payload.cmd     = M_XWR;
  if (!st_ext_arbiter) begin
    l1d_ext_wr_req.payload.addr    = r_ext_evict_payload.paddr;
    l1d_ext_wr_req.payload.color   = r_ext_evict_payload.color;
    l1d_ext_wr_req.tag             = {L2_UPPER_TAG_WR_L1D, {(L2_CMD_TAG_W-2){1'b0}}};
    l1d_ext_wr_req.payload.data    = r_ext_evict_payload.data;
    l1d_ext_wr_req.payload.byte_en = {DCACHE_DATA_B_W{1'b1}};
  end else begin
    l1d_ext_wr_req.payload.addr    = r_uc_wr_paddr;
    l1d_ext_wr_req.payload.color   = 'h0;
    l1d_ext_wr_req.tag             = {L2_UPPER_TAG_WR_L1D, {(L2_CMD_TAG_W-2){1'b0}}};
    l1d_ext_wr_req.payload.data    = r_uc_wr_data;
    l1d_ext_wr_req.payload.byte_en = r_uc_wr_strb;
  end // else: !if(r_l1d_evict_req_valid)
end // always_comb


// ----------------
// Forward checker
// ----------------

// -----------------------------------
// Forwarding check from LSU Pipeline
// -----------------------------------
generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : lsu_fwd_loop
  assign fwd_check_if[p_idx].fwd_valid = r_l1d_evict_req_valid & fwd_check_if[p_idx].valid &
                                         (r_ext_evict_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)] ==
                                          fwd_check_if[p_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)]);
  assign fwd_check_if[p_idx].fwd_dw    = fwd_check_if[p_idx].fwd_valid ? {(riscv_pkg::XLEN_W/8){1'b1}} : {(riscv_pkg::XLEN_W/8){1'b0}};
  assign fwd_check_if[p_idx].fwd_data  = r_ext_evict_payload.data >> {fwd_check_if[p_idx].paddr[$clog2(DCACHE_DATA_B_W)-1: 0], 3'b000};
end // block: lsu_fwd_loop
endgenerate


// --------------
// Snoop Checker
// --------------

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    streq_snoop_if.resp_s1_valid <= 'h0;
  end else begin
    streq_snoop_if.resp_s1_valid <= streq_snoop_if.req_s0_valid;
    streq_snoop_if.resp_s1_data  <= r_ext_evict_payload.data;
    streq_snoop_if.resp_s1_be    <= {DCACHE_DATA_B_W{r_l1d_evict_req_valid & is_cache_addr_same(r_ext_evict_payload.paddr, streq_snoop_if.req_s0_paddr)}};
  end
end

// --------------------
// Status broadcasting
// --------------------
assign st_req_info_if.busy  = r_l1d_evict_req_valid;
assign st_req_info_if.paddr = r_ext_evict_payload.paddr;

`ifdef SIMULATION
  `ifdef COMPARE_ISS
import "DPI-C" function void record_l1d_evict
(
 input longint rtl_time,
 input longint paddr,
 input int     ram_addr,
 input int unsigned array[scariv_conf_pkg::DCACHE_DATA_W/32],
 input int     size
);

int unsigned l1d_array[scariv_conf_pkg::DCACHE_DATA_W/32];
generate for (genvar idx = 0; idx < scariv_conf_pkg::DCACHE_DATA_W/32; idx++) begin : array_loop
  assign l1d_array[idx] = l1d_ext_wr_req.payload.data[idx*32+:32];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (l1d_ext_wr_req.valid & l1d_ext_wr_req.ready) begin
      /* verilator lint_off WIDTH */
      record_l1d_evict ($time,
                        l1d_ext_wr_req.payload.addr,
                        l1d_ext_wr_req.payload.addr[$clog2(DCACHE_DATA_B_W) +: DCACHE_TAG_LOW],
                        l1d_array,
                        DCACHE_DATA_B_W);
      // $fwrite(scariv_pkg::STDERR, "%t : L1D Store-Out : %0x(%x) <= ",
      //         $time,
      //         l1d_ext_wr_req.payload.addr,
      //         l1d_ext_wr_req.payload.addr[$clog2(DCACHE_DATA_B_W) +: DCACHE_TAG_LOW]);
      // for (int i = DCACHE_DATA_B_W/4-1; i >=0 ; i--) begin
      //   $fwrite(scariv_pkg::STDERR, "%08x", l1d_ext_wr_req.payload.data[i*32 +: 32]);
      //   if (i != 0) begin
      //     $fwrite(scariv_pkg::STDERR, "_");
      //   end else begin
      //     $fwrite(scariv_pkg::STDERR, "\n");
      //   end
      // end
    end // if (l1d_ext_wr_req.valid)
  end // if (i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)
  `endif // COMPARE_ISS
`endif // SIMULATION

endmodule // scariv_store_requestor

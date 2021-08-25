// ------------------------------------------------------------------------
// NAME : MSRH Store Buffer
// TYPE : module
// ------------------------------------------------------------------------
// After STQ commit, request L1D write and control
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_st_buffer
  import decoder_lsu_ctrl_pkg::*;
  import msrh_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 st_buffer_if.slave st_buffer_if,
 // L1D Miss/Hit Interface
 l1d_rd_if.master l1d_rd_if,
 // Search LRQ interface during eviction
 lrq_evict_search_if.master lrq_evict_search_if,
 // Interface of Missed Data for Store
 l1d_lrq_if.master l1d_lrq_stq_miss_if,
 // Write Data to DCache
 l1d_wr_if.master l1d_wr_if,
 l1d_wr_if.master l1d_merge_if,

 // Forward check interface from LSU Pipeline
 fwd_check_if.slave  stbuf_fwd_check_if[msrh_conf_pkg::LSU_INST_NUM],

 // LRQ Resolve Notofication
 input       lrq_resolve_t i_lrq_resolve
 );


// =========================
// Declarations
// =========================
logic [ST_BUF_ENTRY_SIZE-1: 0] w_in_ptr_oh;
logic                          w_out_valid;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_out_ptr_oh;

logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_valids;
logic                          w_entry_full;
logic                          w_st_buffer_allocated;
logic                          w_st_buffer_accepted;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_l1d_rd_req;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_l1d_rd_req_oh;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_l1d_wr_req;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_l1d_wr_req_oh;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_l1d_merge_req;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_l1d_merge_req_oh;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_finish;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_merge_accept;

logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_lrq_req;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_lrq_req_oh;

logic                          r_l1d_rd_if_resp;

st_buffer_entry_t w_init_load;

logic [msrh_conf_pkg::LSU_INST_NUM-1:0] w_stbuf_fwd_hit[ST_BUF_ENTRY_SIZE];

// ----------------------
// STQ All Entries
// ----------------------
st_buffer_entry_t w_entries[ST_BUF_ENTRY_SIZE];


assign w_st_buffer_allocated = st_buffer_if.valid &
                               (!(|w_merge_accept) & !w_entry_full);
assign w_entry_full = &w_entry_valids;
assign w_out_valid  = |w_entry_finish;

// -----------------------
// Input / Output Pointer
// -----------------------
inoutptr_var_oh #(.SIZE(ST_BUF_ENTRY_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n), .i_rollback(1'b0),
                                                      .i_in_valid (w_st_buffer_allocated ), .i_in_val ('h1), .o_in_ptr_oh (w_in_ptr_oh ),
                                                      .i_out_valid(w_out_valid), .i_out_val('h1), .o_out_ptr_oh(w_out_ptr_oh));

// New Entry create
assign w_init_load = assign_st_buffer(st_buffer_if.paddr, st_buffer_if.strb, st_buffer_if.data);


generate for (genvar e_idx = 0; e_idx < ST_BUF_ENTRY_SIZE; e_idx++) begin : entry_loop
  logic w_ready_to_merge;
  logic w_load;

  assign w_entry_valids[e_idx] = w_entries[e_idx].valid;

  assign w_load = st_buffer_if.valid & w_in_ptr_oh[e_idx] & w_st_buffer_allocated;

  msrh_st_buffer_entry
  u_entry
    (
     .i_clk    (i_clk    ),
     .i_reset_n(i_reset_n),

     .i_load (w_load),
     .i_entry(w_init_load),
     .i_merge_accept (w_merge_accept[e_idx]),

     .o_l1d_rd_req(w_entry_l1d_rd_req[e_idx]),
     .i_l1d_rd_accepted (w_entry_l1d_rd_req_oh[e_idx]),

     .o_lrq_req      (w_entry_lrq_req   [e_idx]),
     .i_lrq_accepted (w_entry_lrq_req_oh[e_idx]),

     .i_l1d_rd_miss     (l1d_rd_if.s1_miss),

     // Forward check interface from LSU Pipeline
     .stbuf_fwd_check_if (stbuf_fwd_check_if    ),
     .o_fwd_lsu_hit      (w_stbuf_fwd_hit[e_idx]),

     .o_l1d_wr_req      (w_entry_l1d_wr_req[e_idx]),
     .i_l1d_rd_conflict (l1d_rd_if.s1_conflict),
     .i_evict_merged    (lrq_evict_search_if.s1_hit_merged),
     .i_l1d_wr_conflict (l1d_wr_if.conflict),

     .i_lrq_full    (l1d_lrq_stq_miss_if.resp_payload.full    ),
     .i_lrq_conflict(l1d_lrq_stq_miss_if.resp_payload.conflict),
     .i_lrq_index_oh(l1d_lrq_stq_miss_if.resp_payload.lrq_index_oh),

     .i_lrq_resolve (i_lrq_resolve),

     .o_ready_to_merge (w_ready_to_merge),
     .o_l1d_merge_req  (w_entry_l1d_merge_req[e_idx]),
     .o_entry(w_entries[e_idx]),
     .o_entry_finish (w_entry_finish[e_idx])
     );

  // Search Merging
  assign w_merge_accept[e_idx] = w_entries[e_idx].valid & st_buffer_if.valid & w_ready_to_merge &
                                 w_entries[e_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)] == st_buffer_if.paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)];


end
endgenerate

// -----------------
// Make L1D request
// -----------------
st_buffer_entry_t  w_l1d_rd_entry;
bit_extract_lsb_ptr_oh #(.WIDTH(ST_BUF_ENTRY_SIZE)) u_l1d_rd_req_sel (.in(w_entry_l1d_rd_req), .i_ptr_oh(w_out_ptr_oh), .out(w_entry_l1d_rd_req_oh));
bit_oh_or
  #(.T(st_buffer_entry_t), .WORDS(ST_BUF_ENTRY_SIZE))
select_l1d_rd_entry_oh
  (
   .i_oh(w_entry_l1d_rd_req_oh),
   .i_data(w_entries),
   .o_selected(w_l1d_rd_entry)
   );

assign l1d_rd_if.s0_valid = |w_entry_l1d_rd_req;
assign l1d_rd_if.s0_h_pri = 1'b0;
assign l1d_rd_if.s0_paddr = {w_l1d_rd_entry.paddr, {$clog2(ST_BUF_WIDTH/8){1'b0}}};


// ------------------------
// Make LRQ Refill request-
// -----------------------
st_buffer_entry_t  w_lrq_target_entry;
bit_extract_lsb_ptr_oh #(.WIDTH(ST_BUF_ENTRY_SIZE)) u_lrq_req_sel (.in(w_entry_lrq_req), .i_ptr_oh(w_out_ptr_oh), .out(w_entry_lrq_req_oh));
bit_oh_or
  #(.T(st_buffer_entry_t), .WORDS(ST_BUF_ENTRY_SIZE))
select_lrq_entry_oh
  (
   .i_oh(w_entry_lrq_req_oh),
   .i_data(w_entries),
   .o_selected(w_lrq_target_entry)
   );

// Eviction: Replaced Address
logic                                     r_s2_replace_valid;
logic [msrh_conf_pkg::DCACHE_WAYS-1: 0]   r_s2_replace_way;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] r_s2_replace_data;
logic [riscv_pkg::PADDR_W-1: 0]           r_s2_replace_paddr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_replace_valid <= 1'b0;
  end else begin
    r_s2_replace_valid <= l1d_rd_if.s1_replace_valid;
    r_s2_replace_way   <= l1d_rd_if.s1_replace_way;
    r_s2_replace_data  <= l1d_rd_if.s1_replace_data;
    r_s2_replace_paddr <= l1d_rd_if.s1_replace_paddr;
  end
end


assign l1d_lrq_stq_miss_if.load = |w_entry_lrq_req;
assign l1d_lrq_stq_miss_if.req_payload.paddr               = {w_lrq_target_entry.paddr, {($clog2(msrh_lsu_pkg::ST_BUF_WIDTH/8)){1'b0}}};
assign l1d_lrq_stq_miss_if.req_payload.evict_valid         = r_s2_replace_valid;
assign l1d_lrq_stq_miss_if.req_payload.evict_payload.paddr = r_s2_replace_paddr;
assign l1d_lrq_stq_miss_if.req_payload.evict_payload.way   = r_s2_replace_way;
assign l1d_lrq_stq_miss_if.req_payload.evict_payload.data  = r_s2_replace_data;


// --------------------------------------------
// Search Eviction Data that is ready to Evict
// --------------------------------------------
assign lrq_evict_search_if.s0_valid = l1d_rd_if.s0_valid;
assign lrq_evict_search_if.s0_paddr = {w_l1d_rd_entry.paddr, {$clog2(ST_BUF_WIDTH/8){1'b0}}};
assign lrq_evict_search_if.s0_data  = w_l1d_rd_entry.data;
assign lrq_evict_search_if.s0_strb  = w_l1d_rd_entry.strb;

localparam multiply_dc_stbuf_width  = msrh_conf_pkg::DCACHE_DATA_W / msrh_lsu_pkg::ST_BUF_WIDTH;


// --------------------------------------------
// Write L1D Interface
// --------------------------------------------
st_buffer_entry_t  w_l1d_wr_entry;
bit_extract_lsb_ptr_oh #(.WIDTH(ST_BUF_ENTRY_SIZE)) u_l1d_wr_req_sel (.in(w_entry_l1d_wr_req), .i_ptr_oh(w_out_ptr_oh), .out(w_entry_l1d_wr_req_oh));
bit_oh_or
  #(.T(st_buffer_entry_t), .WORDS(ST_BUF_ENTRY_SIZE))
select_l1d_wr_entry_oh
  (
   .i_oh(w_entry_l1d_wr_req_oh),
   .i_data(w_entries),
   .o_selected(w_l1d_wr_entry)
   );

assign l1d_wr_if.valid = |w_entry_l1d_wr_req_oh;
assign l1d_wr_if.paddr = {w_l1d_wr_entry.paddr, {($clog2(ST_BUF_WIDTH/8)){1'b0}}};
assign l1d_wr_if.data  = {multiply_dc_stbuf_width{w_l1d_wr_entry.data}};
/* verilator lint_off WIDTH */
assign l1d_wr_if.be    = w_l1d_wr_entry.strb << {w_l1d_wr_entry.paddr[$clog2(ST_BUF_WIDTH/8) +: $clog2(multiply_dc_stbuf_width)], {$clog2(ST_BUF_WIDTH/8){1'b0}}};

// --------------------------------------------
// L1D Merge Interface
// --------------------------------------------
st_buffer_entry_t  w_l1d_merge_entry;
bit_extract_lsb_ptr_oh #(.WIDTH(ST_BUF_ENTRY_SIZE)) u_l1d_merge_req_sel (.in(w_entry_l1d_merge_req), .i_ptr_oh(w_out_ptr_oh), .out(w_entry_l1d_merge_req_oh));
bit_oh_or
  #(.T(st_buffer_entry_t), .WORDS(ST_BUF_ENTRY_SIZE))
select_l1d_merge_entry_oh
  (
   .i_oh(w_entry_l1d_merge_req_oh),
   .i_data(w_entries),
   .o_selected(w_l1d_merge_entry)
   );

assign l1d_merge_if.valid = |w_entry_l1d_merge_req_oh;
assign l1d_merge_if.paddr = {w_l1d_merge_entry.paddr, {($clog2(ST_BUF_WIDTH/8)){1'b0}}};
assign l1d_merge_if.data  = {multiply_dc_stbuf_width{w_l1d_merge_entry.data}};
/* verilator lint_off WIDTH */
assign l1d_merge_if.be    = w_l1d_merge_entry.strb << {w_l1d_merge_entry.paddr[$clog2(ST_BUF_WIDTH/8) +: $clog2(multiply_dc_stbuf_width)], {$clog2(ST_BUF_WIDTH/8){1'b0}}};



// -----------------------------------
// Forwarding check from LSU Pipeline
// -----------------------------------
generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : lsu_fwd_loop
  logic [ST_BUF_ENTRY_SIZE-1:0] st_buf_hit_array;
  for (genvar s_idx = 0; s_idx < ST_BUF_ENTRY_SIZE; s_idx++) begin : st_buf_loop
    assign st_buf_hit_array[s_idx] = w_stbuf_fwd_hit[s_idx][p_idx];
  end
  st_buffer_entry_t w_fwd_entry;
  bit_oh_or #(.T(st_buffer_entry_t), .WORDS(ST_BUF_ENTRY_SIZE)) fwd_select_entry (.i_data(w_entries), .i_oh(st_buf_hit_array), .o_selected(w_fwd_entry));

  logic dw_upper;
  assign dw_upper = stbuf_fwd_check_if[p_idx].paddr[$clog2(ST_BUF_WIDTH/8)-1];

  assign stbuf_fwd_check_if[p_idx].fwd_valid = |st_buf_hit_array;
  assign stbuf_fwd_check_if[p_idx].fwd_dw    = dw_upper ? w_fwd_entry.strb[riscv_pkg::XLEN_W/8 +: riscv_pkg::XLEN_W/8] :
                                               w_fwd_entry.strb[riscv_pkg::XLEN_W/8-1: 0];
  assign stbuf_fwd_check_if[p_idx].fwd_data  = dw_upper ? w_fwd_entry.data[riscv_pkg::XLEN_W +: riscv_pkg::XLEN_W] :
                                               w_fwd_entry.data[riscv_pkg::XLEN_W-1: 0];

end
endgenerate


// always_ff @ (posedge i_clk, negedge i_reset_n) begin
//   if (!i_reset_n) begin
//     r_l1d_rd_if_resp <= 'b0;
//     l1d_wr_if.valid <= 1'b0;
//   end else begin
//     r_l1d_rd_if_resp <= l1d_rd_if.s0_valid;
//     if (r_l1d_rd_if_resp) begin
//       if (l1d_rd_if.s1_hit) begin
//         l1d_wr_if.valid <= 1'b1;
//         l1d_wr_if.paddr <= {w_l1d_rd_entry.paddr, {($clog2(ST_BUF_WIDTH/8)){1'b0}}};
//         l1d_wr_if.data  <= {multiply_dc_stbuf_width{w_l1d_rd_entry.data}};
//         /* verilator lint_off WIDTH */
//         l1d_wr_if.be    <= w_l1d_rd_entry.strb << {w_l1d_rd_entry.paddr[$clog2(ST_BUF_WIDTH/8) +: $clog2(multiply_dc_stbuf_width)], 3'b000};
//       end else begin
//         l1d_wr_if.valid <= 1'b0;
//       end
//     end else begin
//       l1d_wr_if.valid <= 1'b0;
//     end // else: !if(r_l1d_rd_if_resp)
//   end // else: !if(!i_reset_n)
// end // always_ff @ (posedge i_clk, negedge i_reset_n)

`ifdef SIMULATION

import "DPI-C" function void record_stq_store
(
 input longint rtl_time,
 input longint paddr,
 input int     ram_addr,
 input byte    array[msrh_lsu_pkg::DCACHE_DATA_B_W],
 input longint be,
 input int     size
);

byte l1d_array[msrh_lsu_pkg::DCACHE_DATA_B_W];
generate for (genvar idx = 0; idx < msrh_lsu_pkg::DCACHE_DATA_B_W; idx++) begin : array_loop
  assign l1d_array[idx] = l1d_wr_if.data[idx*8+:8];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (l1d_wr_if.valid & !l1d_wr_if.conflict) begin
      /* verilator lint_off WIDTH */
      record_stq_store($time,
                       l1d_wr_if.paddr,
                       l1d_wr_if.paddr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW],
                       l1d_array,
                       l1d_wr_if.be,
                       msrh_lsu_pkg::DCACHE_DATA_B_W);
      // $fwrite(msrh_pkg::STDERR, "%t : L1D Stq Store : %0x(%x) <= ",
      //         $time,
      //         l1d_wr_if.paddr,
      //         l1d_wr_if.paddr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W) +: msrh_lsu_pkg::DCACHE_TAG_LOW]);
      // for (int i = msrh_lsu_pkg::DCACHE_DATA_B_W-1; i >=0 ; i--) begin
      //   if (l1d_wr_if.be[i]) begin
      //     $fwrite(msrh_pkg::STDERR, "%02x", l1d_wr_if.data[i*8 +: 8]);
      //   end else begin
      //     $fwrite(msrh_pkg::STDERR, "__");
      //   end
      //   if (i == 0) begin
      //     $fwrite(msrh_pkg::STDERR, "\n");
      //   end else begin
      //     if (i % 4 == 0) begin
      //       $fwrite(msrh_pkg::STDERR, "_");
      //     end
      //   end
      // end
    end // if (l1d_wr_if.valid)
  end // if (i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)
`endif // SIMULATION

endmodule // msrh_st_buffer

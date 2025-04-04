// ------------------------------------------------------------------------
// NAME : SCARIV Store Buffer
// TYPE : module
// ------------------------------------------------------------------------
// After STQ commit, request L1D write and control
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_st_buffer
  import decoder_lsu_ctrl_pkg::*;
  import scariv_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 st_buffer_if.slave st_buffer_if,
 // L1D Miss/Hit Interface
 l1d_rd_if.master l1d_rd_if,

 // Interface of Missed Data for Store
 l1d_missu_if.master l1d_missu_stq_miss_if,
 // Write Data to DCache
 l1d_wr_if.master l1d_stbuf_wr_if,
 // Watch for write successfuly with merged data
 l1d_wr_if.watch  l1d_mshr_wr_if,
 // MSHR to STBuf: Write Merge Interface
 mshr_stbuf_search_if.slave mshr_stbuf_search_if,

 // Forward check interface from LSU Pipeline
 fwd_check_if.slave  stbuf_fwd_check_if[scariv_conf_pkg::LSU_INST_NUM],

 // RMW Ordere Hazard Check
 rmw_order_check_if.slave rmw_order_check_if[scariv_conf_pkg::LSU_INST_NUM],

 // Search MISSU entry: same cycle as L1D Search
 missu_pa_search_if.master   missu_pa_search_if,

 // Snoop Interface
 snoop_info_if.monitor snoop_info_if,
 stbuf_snoop_if.slave  stbuf_snoop_if,

 // MISSU Resolve Notofication
 input       missu_resolve_t i_missu_resolve
 );


// =========================
// Declarations
// =========================
localparam multiply_dc_stbuf_width  = (scariv_conf_pkg::DCACHE_DATA_W / ST_BUF_WIDTH);

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
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_l1d_merge_hit;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_finish;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_merge_accept;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_merge_refused;

logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_missu_req;
logic [ST_BUF_ENTRY_SIZE-1: 0] w_entry_missu_req_oh;

logic                          r_l1d_rd_if_resp;

st_buffer_entry_t w_init_load;

logic [scariv_conf_pkg::LSU_INST_NUM-1:0] w_stbuf_fwd_hit[ST_BUF_ENTRY_SIZE];

amo_op_if w_amo_op_if();

logic [ST_BUF_ENTRY_SIZE-1: 0]          w_ex2_rmw_order_haz_vld[scariv_conf_pkg::LSU_INST_NUM];

// ----------------------
// STQ All Entries
// ----------------------
st_buffer_entry_t w_entries[ST_BUF_ENTRY_SIZE];
st_buffer_state_t w_state  [ST_BUF_ENTRY_SIZE];


assign w_st_buffer_allocated = st_buffer_if.valid &
                               !(|w_merge_refused) & !(|w_merge_accept) & !w_entry_full;
assign w_entry_full = &w_entry_valids;
assign w_out_valid  = |(w_entry_finish & w_out_ptr_oh);

// -----------------------
// Input / Output Pointer
// -----------------------
inoutptr_oh
  #(.SIZE(ST_BUF_ENTRY_SIZE))
u_req_ptr
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_rollback (1'b0),
   .i_clear    (st_buffer_if.valid & st_buffer_if.is_rmw),

   .i_in_valid  (w_st_buffer_allocated ),
   .o_in_ptr    (w_in_ptr_oh ),

   .i_out_valid (w_out_valid),
   .o_out_ptr   (w_out_ptr_oh)
   );

// New Entry create
assign w_init_load = assign_st_buffer(
`ifdef SIMULATION
                                      st_buffer_if.cmt_id, st_buffer_if.grp_id,
`endif // SIMULATION
                                      st_buffer_if.paddr, st_buffer_if.strb, st_buffer_if.data,
                                      st_buffer_if.rmwop, st_buffer_if.size);

assign st_buffer_if.resp = w_st_buffer_allocated ? ST_BUF_ALLOC :
                           |w_merge_accept       ? ST_BUF_MERGE :
                           ST_BUF_FULL;

assign st_buffer_if.is_empty = ~|w_entry_valids;

generate for (genvar e_idx = 0; e_idx < ST_BUF_ENTRY_SIZE; e_idx++) begin : entry_loop
  logic w_ready_to_merge;
  logic w_load;

  assign w_entry_valids[e_idx] = w_entries[e_idx].valid;

  assign w_load = st_buffer_if.valid & (st_buffer_if.is_rmw ? e_idx == 0 : w_in_ptr_oh[e_idx]) & w_st_buffer_allocated;

  if (e_idx == 0) begin
    scariv_st_buffer_amo_entry
      u_entry
        (
         .i_clk    (i_clk    ),
         .i_reset_n(i_reset_n),

         .i_load (w_load),
         .i_entry(w_init_load),
         .i_merge_accept (w_merge_accept[e_idx]),

         .o_l1d_rd_req(w_entry_l1d_rd_req[e_idx]),
         .i_l1d_rd_accepted (w_entry_l1d_rd_req_oh[e_idx]),

         .o_missu_req      (w_entry_missu_req   [e_idx]),
         .i_missu_accepted (w_entry_missu_req_oh[e_idx]),

         .i_missu_search_update_hit(missu_pa_search_if.s1_hit_update_index_oh),
         .i_missu_search_hit       (missu_pa_search_if.s1_hit_index_oh),
         .i_missu_evict_search_hit (missu_pa_search_if.s1_evict_hit_index_oh),
         .i_missu_evict_sent       (missu_pa_search_if.s1_evict_sent),

         // Forward check interface from LSU Pipeline
         .stbuf_fwd_check_if (stbuf_fwd_check_if    ),
         .o_fwd_lsu_hit      (w_stbuf_fwd_hit[e_idx]),

         .i_l1d_rd_s1_conflict (l1d_rd_if.s1_conflict),
         .i_l1d_rd_s1_miss     (l1d_rd_if.s1_miss    ),
         .i_l1d_s1_way         (l1d_rd_if.s1_hit_way ),
         .i_l1d_s1_data        (l1d_rd_if.s1_data    ),

         .o_l1d_wr_req         (w_entry_l1d_wr_req   [e_idx]),
         .i_l1d_wr_accepted    (w_entry_l1d_wr_req_oh[e_idx]),

         .i_l1d_wr_s1_resp_hit      (l1d_stbuf_wr_if.s1_wr_resp.s1_hit),
         .i_l1d_wr_s1_resp_conflict (l1d_stbuf_wr_if.s1_wr_resp.s1_conflict),

         .i_snoop_busy     (snoop_info_if.busy),
         .i_st_missu_resp  (l1d_missu_stq_miss_if.resp_payload ),
         .i_missu_resolve (i_missu_resolve),

         .amo_op_if (w_amo_op_if),

         .l1d_mshr_wr_if   (l1d_mshr_wr_if),
         .o_ready_to_merge (w_ready_to_merge),
         .i_mshr_l1d_wr_merged (w_entry_l1d_merge_hit[e_idx]),
         .o_entry(w_entries[e_idx]),
         .o_state(w_state  [e_idx]),
         .o_entry_finish (w_entry_finish[e_idx]),
         .i_finish_accepted(w_out_ptr_oh[e_idx])
         );
  end else begin // if (e_idx == 0)
    scariv_st_buffer_entry
      u_entry
        (
         .i_clk    (i_clk    ),
         .i_reset_n(i_reset_n),

         .i_load (w_load),
         .i_entry(w_init_load),
         .i_merge_accept (w_merge_accept[e_idx]),

         .o_l1d_rd_req(w_entry_l1d_rd_req[e_idx]),
         .i_l1d_rd_accepted (w_entry_l1d_rd_req_oh[e_idx]),

         .o_missu_req      (w_entry_missu_req   [e_idx]),
         .i_missu_accepted (w_entry_missu_req_oh[e_idx]),

         .i_missu_search_update_hit(missu_pa_search_if.s1_hit_update_index_oh),
         .i_missu_search_hit       (missu_pa_search_if.s1_hit_index_oh),
         .i_missu_evict_search_hit (missu_pa_search_if.s1_evict_hit_index_oh),
         .i_missu_evict_sent       (missu_pa_search_if.s1_evict_sent),

         // Forward check interface from LSU Pipeline
         .stbuf_fwd_check_if (stbuf_fwd_check_if    ),
         .o_fwd_lsu_hit      (w_stbuf_fwd_hit[e_idx]),

         .i_l1d_rd_s1_conflict (l1d_rd_if.s1_conflict),
         .i_l1d_rd_s1_miss     (l1d_rd_if.s1_miss    ),
         .i_l1d_s1_way         (l1d_rd_if.s1_hit_way ),
         .i_l1d_s1_data        (l1d_rd_if.s1_data    ),

         .o_l1d_wr_req         (w_entry_l1d_wr_req   [e_idx]),
         .i_l1d_wr_accepted    (w_entry_l1d_wr_req_oh[e_idx]),

         .i_l1d_wr_s1_resp_hit      (l1d_stbuf_wr_if.s1_wr_resp.s1_hit),
         .i_l1d_wr_s1_resp_conflict (l1d_stbuf_wr_if.s1_wr_resp.s1_conflict),

         .i_snoop_busy     (snoop_info_if.busy),
         .i_st_missu_resp  (l1d_missu_stq_miss_if.resp_payload ),
         .i_missu_resolve (i_missu_resolve),

         .l1d_mshr_wr_if   (l1d_mshr_wr_if),
         .o_ready_to_merge (w_ready_to_merge),
         .i_mshr_l1d_wr_merged (w_entry_l1d_merge_hit[e_idx]),
         .o_entry(w_entries[e_idx]),
         .o_state(w_state  [e_idx]),
         .o_entry_finish (w_entry_finish[e_idx]),
         .i_finish_accepted(w_out_ptr_oh[e_idx])
         );
  end // else: !if(e_idx == 0)

  // Search Merging
  assign w_merge_accept[e_idx] = w_entries[e_idx].valid & st_buffer_if.valid & w_ready_to_merge & ~w_entry_l1d_merge_hit[e_idx] &
                                 w_entries[e_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)] == st_buffer_if.paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)];

  assign w_merge_refused[e_idx] = w_entries[e_idx].valid & st_buffer_if.valid & ~(w_ready_to_merge & ~w_entry_l1d_merge_hit[e_idx]) &
                                  w_entries[e_idx].paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)] == st_buffer_if.paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)];

  // RMW Order Hazard Check
  for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : rmw_order_haz_loop
    assign w_ex2_rmw_order_haz_vld[p_idx][e_idx] = w_entries[e_idx].valid &
                                                   (w_entries[e_idx].rmwop != decoder_lsu_ctrl_pkg::RMWOP__) &
                                                   rmw_order_check_if[p_idx].ex2_valid;
  end // block: rmw_order_haz_loop

  // MSHR L1D update & Merge
  assign w_entry_l1d_merge_hit[e_idx] = w_entries[e_idx].valid & (w_state[e_idx] == ST_BUF_WAIT_REFILL) &
                                        (w_entries[e_idx].rmwop == decoder_lsu_ctrl_pkg::RMWOP__) &
                                        |(w_entries[e_idx].missu_index_oh & mshr_stbuf_search_if.mshr_index_oh);

end // block: entry_loop
endgenerate

// RMW Order Hazard Check Logci
generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : rmw_haz_resp_loop
  assign rmw_order_check_if[p_idx].ex2_stbuf_haz_vld = |w_ex2_rmw_order_haz_vld[p_idx];
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

assign l1d_rd_if.s0_valid         = |w_entry_l1d_rd_req;
assign l1d_rd_if.s0_high_priority = w_l1d_rd_entry.l1d_high_priority;
assign l1d_rd_if.s0_paddr         = w_l1d_rd_entry.paddr;

// -----------------
// MISSU entry search
// -----------------
assign missu_pa_search_if.s0_valid = l1d_rd_if.s0_valid;
assign missu_pa_search_if.s0_paddr = l1d_rd_if.s0_paddr;

// ------------------------
// Make MISSU Refill request-
// -----------------------
st_buffer_entry_t  w_missu_target_entry;
bit_extract_lsb_ptr_oh #(.WIDTH(ST_BUF_ENTRY_SIZE)) u_missu_req_sel (.in(w_entry_missu_req), .i_ptr_oh(w_out_ptr_oh), .out(w_entry_missu_req_oh));
bit_oh_or
  #(.T(st_buffer_entry_t), .WORDS(ST_BUF_ENTRY_SIZE))
select_missu_entry_oh
  (
   .i_oh(w_entry_missu_req_oh),
   .i_data(w_entries),
   .o_selected(w_missu_target_entry)
   );

// Eviction: Replaced Address
logic                                           r_s2_replace_valid;
logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1: 0] r_s2_replace_way;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]       r_s2_replace_data;
scariv_pkg::paddr_t                 r_s2_replace_paddr;
logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1: 0] r_s2_hit_way;
// logic [scariv_conf_pkg::DCACHE_WAYS-1: 0]         r_s2_missu_evict_hit_ways;
// logic [scariv_conf_pkg::DCACHE_WAYS-1: 0]         w_s2_conflict_evict_addr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_replace_valid <= 1'b0;

    // r_s2_missu_evict_hit_ways <= 'h0;
  end else begin
    r_s2_hit_way <= l1d_rd_if.s1_hit_way;

    r_s2_replace_valid <= l1d_rd_if.s1_replace_valid;
    r_s2_replace_way   <= l1d_rd_if.s1_replace_way;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign l1d_missu_stq_miss_if.load = |w_entry_missu_req; /* & w_s2_conflict_evict_addrxo; */
assign l1d_missu_stq_miss_if.req_payload.paddr = w_missu_target_entry.paddr;
assign l1d_missu_stq_miss_if.req_payload.way   = w_missu_target_entry.l1d_way;


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

always_comb begin
  l1d_stbuf_wr_if.s0_valid                   = |w_entry_l1d_wr_req_oh;
  l1d_stbuf_wr_if.s0_wr_req.s0_way           = w_l1d_wr_entry.l1d_way;
  l1d_stbuf_wr_if.s0_wr_req.s0_paddr         = {w_l1d_wr_entry.paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)], {($clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)){1'b0}}};
  l1d_stbuf_wr_if.s0_wr_req.s0_data          = {multiply_dc_stbuf_width{w_l1d_wr_entry.data}};
  l1d_stbuf_wr_if.s0_wr_req.s0_mesi          = scariv_lsu_pkg::MESI_MODIFIED;
end

generate if (multiply_dc_stbuf_width == 1) begin
  assign l1d_stbuf_wr_if.s0_wr_req.s0_be    = w_l1d_wr_entry.strb;
  end else begin
  /* verilator lint_off WIDTH */
  assign l1d_stbuf_wr_if.s0_wr_req.s0_be    = w_l1d_wr_entry.strb << {w_l1d_wr_entry.paddr[$clog2(ST_BUF_WIDTH/8) +: $clog2(multiply_dc_stbuf_width)], {$clog2(ST_BUF_WIDTH/8){1'b0}}};
  end
endgenerate

// --------------------------------------------
// L1D Merge Interface
// --------------------------------------------
logic [DCACHE_DATA_B_W-1: 0] w_entries_be  [ST_BUF_ENTRY_SIZE];
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] w_entries_data[ST_BUF_ENTRY_SIZE];
  generate if (multiply_dc_stbuf_width == 1) begin
    for (genvar s_idx = 0; s_idx < ST_BUF_ENTRY_SIZE; s_idx++) begin : stbuf_be_loop
      assign w_entries_be  [s_idx] = w_entries[s_idx].strb;
      assign w_entries_data[s_idx] = w_entries[s_idx].data;
    end
  end else begin
    for (genvar s_idx = 0; s_idx < ST_BUF_ENTRY_SIZE; s_idx++) begin : stbuf_be_loop
      /* verilator lint_off WIDTH */
      assign w_entries_be  [s_idx] = w_entries[s_idx].strb << {w_entries[s_idx].paddr[$clog2(ST_BUF_WIDTH/8) +: $clog2(multiply_dc_stbuf_width)], {$clog2(ST_BUF_WIDTH/8){1'b0}}};
      assign w_entries_data[s_idx] = {multiply_dc_stbuf_width{w_entries[s_idx].data}};
    end
  end // else: !if(multiply_dc_stbuf_width == 1)
endgenerate

generate for (genvar b_idx = 0; b_idx < DCACHE_DATA_B_W; b_idx++) begin : l1d_merge_loop
  logic [ST_BUF_ENTRY_SIZE-1: 0] w_st_buf_byte_valid;
  logic [ 7: 0]                  w_st_buf_byte_data [ST_BUF_ENTRY_SIZE];
  logic [ 7: 0]                  w_st_buf_byte_sel_data;
  for (genvar s_idx = 0; s_idx < ST_BUF_ENTRY_SIZE; s_idx++) begin : stbuf_loop
    assign w_st_buf_byte_valid[s_idx] = w_entry_l1d_merge_hit[s_idx] & w_entries_be[s_idx][b_idx];
    assign w_st_buf_byte_data [s_idx] = w_entries_data[s_idx][b_idx*8 +: 8];
  end

  bit_oh_or #(.T(logic[7:0]), .WORDS(ST_BUF_ENTRY_SIZE)) select_be_data(.i_oh(w_st_buf_byte_valid), .i_data(w_st_buf_byte_data), .o_selected(w_st_buf_byte_sel_data));

  assign mshr_stbuf_search_if.stbuf_data[b_idx*8 +: 8]  = w_st_buf_byte_sel_data;
  assign mshr_stbuf_search_if.stbuf_be  [b_idx]         = |w_st_buf_byte_valid;
end // block: l1d_merge_loop
endgenerate


// -----------------------------------
// Forwarding check from LSU Pipeline
// -----------------------------------
generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : lsu_fwd_loop
  logic [ST_BUF_ENTRY_SIZE-1:0] st_buf_hit_array;
    for (genvar s_idx = 0; s_idx < ST_BUF_ENTRY_SIZE; s_idx++) begin : st_buf_loop
    assign st_buf_hit_array[s_idx] = w_stbuf_fwd_hit[s_idx][p_idx];
    end
  st_buffer_entry_t w_fwd_entry;
  bit_oh_or #(.T(st_buffer_entry_t), .WORDS(ST_BUF_ENTRY_SIZE)) fwd_select_entry (.i_data(w_entries), .i_oh(st_buf_hit_array), .o_selected(w_fwd_entry));

  assign stbuf_fwd_check_if[p_idx].fwd_valid = |st_buf_hit_array;
  if (ST_BUF_WIDTH == scariv_pkg::ALEN_W * 2) begin
    logic dw_upper;
    assign dw_upper = stbuf_fwd_check_if[p_idx].paddr[$clog2(ST_BUF_WIDTH/8)-1];

    assign stbuf_fwd_check_if[p_idx].fwd_dw    = dw_upper ? w_fwd_entry.strb[scariv_pkg::ALEN_W/8 +: scariv_pkg::ALEN_W/8] :
                                                 w_fwd_entry.strb[scariv_pkg::ALEN_W/8-1: 0];
    assign stbuf_fwd_check_if[p_idx].fwd_data  = dw_upper ? w_fwd_entry.data[scariv_pkg::ALEN_W +: scariv_pkg::ALEN_W] :
                                                 w_fwd_entry.data[scariv_pkg::ALEN_W-1: 0];
  end else begin
    assign stbuf_fwd_check_if[p_idx].fwd_dw    = w_fwd_entry.strb[scariv_pkg::ALEN_W/8-1: 0];
    assign stbuf_fwd_check_if[p_idx].fwd_data  = w_fwd_entry.data[scariv_pkg::ALEN_W-1: 0];
  end
end endgenerate // block: lsu_fwd_loop

// --------------
// AMO Operation
// --------------

scariv_amo_operation
u_amo_op
  (
   .i_data0 (w_amo_op_if.data0),
   .i_data1 (w_amo_op_if.data1),
   .i_op    (w_amo_op_if.rmwop),
   .i_size  (w_amo_op_if.size ),
   .o_data  (w_amo_op_if.result)
   );

// ----------------------------------
// Temporary implementation of Snoop
// ----------------------------------
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    stbuf_snoop_if.resp_s1_valid <= 'h0;
  end else begin
    stbuf_snoop_if.resp_s1_valid <= stbuf_snoop_if.req_s0_valid;
    stbuf_snoop_if.resp_s1_data  <= 'h0;
    stbuf_snoop_if.resp_s1_be    <= {DCACHE_DATA_B_W{1'b0}};
  end
end



`ifdef SIMULATION
  `ifdef COMPARE_ISS
import "DPI-C" function void record_stq_store
(
 input longint rtl_time,
 input longint paddr,
 input int     ram_addr,
 input byte    array[scariv_lsu_pkg::DCACHE_DATA_B_W],
 input longint be,
 input int     size
);

byte l1d_array[scariv_lsu_pkg::DCACHE_DATA_B_W];
  generate for (genvar idx = 0; idx < scariv_lsu_pkg::DCACHE_DATA_B_W; idx++) begin : array_loop
    assign l1d_array[idx] = l1d_stbuf_wr_if.s0_wr_req.s0_data[idx*8+:8];
  end
endgenerate

logic                                           sim_s1_valid;
scariv_pkg::paddr_t                  sim_s1_paddr;
logic [scariv_conf_pkg::DCACHE_DATA_W-1:0]        sim_s1_data ;
logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1:0]       sim_s1_be   ;
logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1: 0] sim_s1_way  ;
byte sim_s1_l1d_array[scariv_lsu_pkg::DCACHE_DATA_B_W];

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin

    sim_s1_valid <= l1d_stbuf_wr_if.s0_valid;
    sim_s1_paddr <= l1d_stbuf_wr_if.s0_wr_req.s0_paddr;
    sim_s1_data  <= l1d_stbuf_wr_if.s0_wr_req.s0_data;
    sim_s1_be    <= l1d_stbuf_wr_if.s0_wr_req.s0_be;
    sim_s1_way   <= l1d_stbuf_wr_if.s0_wr_req.s0_way;
    sim_s1_l1d_array <= l1d_array;
    if (l1d_stbuf_wr_if.s1_resp_valid & !l1d_stbuf_wr_if.s1_wr_resp.s1_conflict) begin
      /* verilator lint_off WIDTH */
      record_stq_store($time,
                       sim_s1_paddr,
                       sim_s1_paddr[$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W) +: scariv_lsu_pkg::DCACHE_TAG_LOW],
                       sim_s1_l1d_array,
                       sim_s1_be,
                       scariv_lsu_pkg::DCACHE_DATA_B_W);
    end // if (sim_s1_valid & !sim_s1_conflict)
  end // if (i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)
  `endif //  `ifdef COMPARE_ISS

logic [63: 0] sim_wr_l1d_cnt;
logic [63: 0] sim_st_buffer_cnt;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    sim_wr_l1d_cnt  <= 'h0;
    sim_st_buffer_cnt <= 'h0;
  end else begin
    if (l1d_stbuf_wr_if.s0_valid) begin
      sim_wr_l1d_cnt <= sim_wr_l1d_cnt + 'h1;
    end
    if (st_buffer_if.valid & st_buffer_if.resp != ST_BUF_FULL) begin
      sim_st_buffer_cnt <= sim_st_buffer_cnt + 'h1;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)

final begin
  $write ("==========================================\n");
  $write ("ST-Buffer L1D update\n\n");
  $write ("l1d_stbuf_wr_if : %d\n", sim_wr_l1d_cnt);
  $write ("st_buffer transfer : %d\n", sim_st_buffer_cnt);
  $write ("==========================================\n");
end

`endif //  `ifdef SIMULATION

endmodule // scariv_st_buffer

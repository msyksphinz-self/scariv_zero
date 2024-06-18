// ------------------------------------------------------------------------
// NAME : scariv_ibuf_pkg
// TYPE : package
// ------------------------------------------------------------------------
// Instruction Buffer packages
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

package scariv_ibuf_pkg;

typedef struct packed {
  logic             pred_taken;
  logic [1:0]       bim_value;
  logic             btb_valid;
  logic             is_cond;
  scariv_pkg::vaddr_t pred_target_vaddr;
  scariv_pkg::gshare_bht_t gshare_index;
  scariv_pkg::gshare_bht_t gshare_bhr;
} pred_info_t;


typedef struct packed {
  logic                           is_call;
  logic                           is_ret;
  logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] ras_index;
  scariv_pkg::vaddr_t                    pred_target_vaddr;
} ras_info_t;


typedef struct packed {
  logic [riscv_pkg::VADDR_W-1: 1]            pc;
  scariv_pkg::ic_data_t                      data;
  scariv_pkg::ic_strb_t                      byte_en;
  logic                                      tlb_except_valid;
  scariv_pkg::except_t                       tlb_except_cause;

  pred_info_t [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] pred_info;
  ras_info_t  [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] ras_info;
`ifdef SIMULATION
  scariv_pkg::vaddr_t pc_dbg;
`endif // SIMULATION
  logic               int_inserted;
} inst_buf_t;

// // Assignment function of frontend instruction queue
// function automatic inst_buf_t assign_entry (scariv_pkg::inst_buffer_in_t fetch);
//   inst_buf_t ret;
//
//   ret.data    = fetch.inst;
//   ret.pc      = fetch.pc;
//   ret.byte_en = fetch.byte_en;
//   ret.tlb_except_valid = fetch.tlb_except_valid;
//   ret.tlb_except_cause = fetch.tlb_except_cause;
//
//   for (int b_idx = 0; b_idx < scariv_lsu_pkg::ICACHE_DATA_B_W/2; b_idx++) begin : pred_loop
//     logic w_f2_ubtb_predict_hit;
//     w_f2_ubtb_predict_hit = i_f2_ubtb_predict_valid & i_f2_ubtb_info.taken & ((i_f2_ubtb_info.pc_offset >> 1) == b_idx);
//     ret.pred_info[b_idx].pred_taken        = w_f2_ubtb_predict_hit ? i_f2_ubtb_info.taken : gshare_search_if.f2_pred_taken[b_idx];
//     ret.pred_info[b_idx].is_cond           = btb_search_if.f2_is_cond      [b_idx];
//     ret.pred_info[b_idx].bim_value         = gshare_search_if.f2_bim_value [b_idx];
//     ret.pred_info[b_idx].btb_valid         = w_f2_ubtb_predict_hit ? i_f2_ubtb_info.taken        : btb_search_if.f2_hit          [b_idx];
//     ret.pred_info[b_idx].pred_target_vaddr = w_f2_ubtb_predict_hit ? i_f2_ubtb_info.target_vaddr : btb_search_if.f2_target_vaddr [b_idx];
//     ret.pred_info[b_idx].gshare_index      = gshare_search_if.f2_index     [b_idx];
//     ret.pred_info[b_idx].gshare_bhr        = gshare_search_if.f2_bhr       [b_idx];
//
//     ret.ras_info[b_idx].is_call           = ras_search_if.f2_is_call[b_idx];
//     ret.ras_info[b_idx].is_ret            = ras_search_if.f2_is_ret [b_idx];
//     // ret.ras_info[b_idx].ras_index         = ras_search_if.f2_ras_be [b_idx/2] & ras_search_if.f2_is_ret [b_idx] ? ras_search_if.f2_ras_index - 1 :
//     // ras_search_if.f2_ras_index;
//     ret.ras_info[b_idx].pred_target_vaddr = ras_search_if.f2_is_call[b_idx] ? {ras_search_if.f2_call_target_vaddr, 1'b0} : {ras_search_if.f2_ras_vaddr, 1'b0};
//   end // block: pred_loop
//
// `ifdef SIMULATION
//   ret.pc_dbg           = {fetch.pc, 1'b0};
// `endif // SIMULATION
//   ret.int_inserted = fetch.int_inserted;
//
//   return ret;
// endfunction // assign_entry

endpackage // scariv_ibuf_pkg

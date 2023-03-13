// ------------------------------------------------------------------------
// NAME : scariv_addr_check
// TYPE : module
// ------------------------------------------------------------------------
// Translate lookaside Buffer
// ------------------------------------------------------------------------
// Input: Virtual addr
// Output: Physical addr
// ------------------------------------------------------------------------

module scariv_addr_check
  import decoder_lsu_ctrl_pkg::*;
  import scariv_lsu_pkg::*;
(
 input scariv_pkg::cmt_id_t      i_entry_cmt_id,
 input scariv_pkg::grp_id_t i_entry_grp_id,
 input scariv_pkg::paddr_t      i_entry_paddr,
 input decoder_lsu_ctrl_pkg::size_t         i_entry_size,

 input ex2_addr_check_t                     i_ex2_addr_check[scariv_conf_pkg::LSU_INST_NUM],
 output logic                               o_addr_conflict
 );

logic [scariv_conf_pkg::LSU_INST_NUM-1: 0]    w_addr_hit;

generate for(genvar idx = 0; idx < scariv_conf_pkg::LSU_INST_NUM; idx++) begin : pipe_loop
  logic w_entry_is_older;
  logic w_cmt_is_older;

  assign w_cmt_is_older = i_entry_cmt_id[scariv_pkg::CMT_ID_W-1] ^ i_ex2_addr_check[idx].cmt_id[scariv_pkg::CMT_ID_W-1] ?
                          i_entry_cmt_id < i_ex2_addr_check[idx].cmt_id :
                          i_entry_cmt_id > i_ex2_addr_check[idx].cmt_id;
  assign w_entry_is_older = w_cmt_is_older ||
                            (i_entry_cmt_id == i_ex2_addr_check[idx].cmt_id &&
                             i_entry_grp_id >  i_ex2_addr_check[idx].grp_id);
  assign w_addr_hit[idx] = i_ex2_addr_check[idx].valid &
                           w_entry_is_older &
                           (i_ex2_addr_check[idx].paddr == i_entry_paddr[riscv_pkg::PADDR_W-1: 3]) &
                           (i_ex2_addr_check[idx].dw    == (i_entry_size == SIZE_DW ? 8'hff :
                                                            i_entry_size == SIZE_W  ? 8'h0f :
                                                            i_entry_size == SIZE_H  ? 8'h03 :
                                                            i_entry_size == SIZE_B  ? 8'h01 : 8'h00) << i_entry_paddr[ 2: 0]);
end
endgenerate

assign o_addr_conflict = |w_addr_hit;

endmodule // scariv_addr_check

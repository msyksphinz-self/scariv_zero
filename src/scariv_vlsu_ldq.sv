// ------------------------------------------------------------------------
// NAME : scariv_vlsu_ldq
// TYPE : module
// ------------------------------------------------------------------------
// Vector LSU Load Queue
// Dynamically Allocation
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_vlsu_ldq
  import scariv_vec_pkg::*;
#(
  parameter IN_PORT_SIZE = 1
  )
(
 input logic i_clk,
 input logic i_reset_n,

 vlsu_lsq_req_if.slave          vlsu_ldq_req_if,
 // ROB notification interface
 rob_info_if.slave              rob_info_if,
 // Commit notification
 input scariv_pkg::commit_blk_t i_commit,
 // Branch Flush Notification
 br_upd_if.slave                br_upd_if
 );

typedef logic [riscv_pkg::PADDR_W-1: $clog2(riscv_vec_conf_pkg::DLEN_W/8) + $clog2(VLSU_LDQ_BANK_SIZE)] vldq_paddr_t;
function automatic vldq_paddr_t to_vldq_paddr (scariv_pkg::paddr_t paddr);
  return paddr[riscv_pkg::PADDR_W-1: $clog2(riscv_vec_conf_pkg::DLEN_W/8) + $clog2(VLSU_LDQ_BANK_SIZE)];
endfunction // vldq_paddr
function automatic scariv_pkg::paddr_t to_paddr (logic [$clog2(VLSU_LDQ_BANK_SIZE)-1: 0] bank_idx, vldq_paddr_t paddr);
  return {paddr, bank_idx, {$clog2(VLSU_LDQ_BANK_SIZE){1'b0}}};
endfunction // to_paddr

typedef struct packed {
  logic                valid;
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  vldq_paddr_t         paddr;
`ifdef SIMULATION
  scariv_pkg::paddr_t sim_paddr;
`endif // SIMULATION
} vlsu_ldq_entry_t;

vlsu_ldq_entry_t r_vlsu_ldq_entries[VLSU_LDQ_BANK_SIZE][VLSU_LDQ_SIZE];
logic                w_commit_flush;

assign w_commit_flush = scariv_pkg::is_flushed_commit(i_commit);

generate for (genvar bank_idx = 0; bank_idx < VLSU_LDQ_BANK_SIZE; bank_idx++) begin : bank_loop

  logic [VLSU_LDQ_SIZE-1: 0] w_entry_load_index  [1];
  logic [VLSU_LDQ_SIZE-1: 0] w_entry_finish_index[1];

  logic                      w_vlsu_ldq_freelist_full;
  logic                      w_freelist_pop_valid;
  assign w_freelist_pop_valid = vlsu_ldq_req_if.valid &
                                vlsu_ldq_req_if.paddr[$clog2(riscv_vec_conf_pkg::DLEN_W/8) +: $clog2(VLSU_LDQ_BANK_SIZE)] == bank_idx[$clog2(VLSU_LDQ_BANK_SIZE)-1: 0] &
                                ~w_vlsu_ldq_freelist_full;

  scariv_freelist_multiports_oh
    #(
      .WIDTH (VLSU_LDQ_SIZE),
      .PORTS (1)
      )
  u_entry_freelist
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_push_id (w_entry_finish_index),
     .i_pop     (w_freelist_pop_valid),
     .o_pop_id  (w_entry_load_index  ),

     .o_is_empty (),
     .o_is_full  (w_vlsu_ldq_freelist_full)
     );


  for (genvar ldq_idx = 0; ldq_idx < VLSU_LDQ_SIZE; ldq_idx++) begin : ldq_loop

    logic w_br_flush;
    assign w_br_flush     = scariv_pkg::is_br_flush_target(r_vlsu_ldq_entries[bank_idx][ldq_idx].cmt_id,
                                                           r_vlsu_ldq_entries[bank_idx][ldq_idx].grp_id,
                                                           br_upd_if.cmt_id, br_upd_if.grp_id,
                                                           br_upd_if.dead, br_upd_if.mispredict) & br_upd_if.update & r_vlsu_ldq_entries[bank_idx][ldq_idx].valid;

    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_vlsu_ldq_entries[bank_idx][ldq_idx].valid <= 1'b0;
      end else begin
        if (w_freelist_pop_valid & w_entry_load_index[0][ldq_idx]) begin
          r_vlsu_ldq_entries[bank_idx][ldq_idx].valid  <= 1'b1;
          r_vlsu_ldq_entries[bank_idx][ldq_idx].cmt_id <= vlsu_ldq_req_if.cmt_id;
          r_vlsu_ldq_entries[bank_idx][ldq_idx].grp_id <= vlsu_ldq_req_if.grp_id;
          r_vlsu_ldq_entries[bank_idx][ldq_idx].paddr  <= to_vldq_paddr(vlsu_ldq_req_if.paddr);
        end else if (w_commit_flush) begin
          r_vlsu_ldq_entries[bank_idx][ldq_idx].valid  <= 1'b0;
        end else if (w_br_flush) begin
          r_vlsu_ldq_entries[bank_idx][ldq_idx].valid  <= 1'b0;
          // r_entry_clear_ready[ldq_idx].valid <= 1'b1;
        end
      end // else: !if(!i_reset_n)
    end
  end
end endgenerate

endmodule // scariv_vlsu_ldq

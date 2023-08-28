// ------------------------------------------------------------------------
// NAME : scariv_vec_vlvtype_snapshots
// TYPE : module
// ------------------------------------------------------------------------
// Rename vlvtype Snapshot Record
// ------------------------------------------------------------------------
// This module records RMT information by Branch
// ------------------------------------------------------------------------

module scariv_vec_vlvtype_snapshots
  import scariv_pkg::*;
  import scariv_vec_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic             i_load,
   input brtag_t           i_brtag,
   input vlvtype_ren_idx_t i_vlvtype_index,

   // Branch Tag Update Signal
   br_upd_if.slave br_upd_if,

   output vlvtype_ren_idx_t o_vlvtype_index
   );

vlvtype_ren_idx_t r_snapshots[scariv_conf_pkg::RV_BRU_ENTRY_SIZE];
/* verilator lint_off UNOPTFLAT */
vlvtype_ren_idx_t w_tmp_snapshots[scariv_conf_pkg::DISP_SIZE+1];

always_ff @ (posedge i_clk) begin
  if (i_load) begin
    r_snapshots[i_brtag] <= i_vlvtype_index;
  end
end

assign o_vlvtype_index = r_snapshots[br_upd_if.brtag];

endmodule // scariv_bru_rn_snapshots

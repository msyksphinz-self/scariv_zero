// ------------------------------------------------------------------------
// NAME : scariv_bru_rn_snapshots
// TYPE : module
// ------------------------------------------------------------------------
// Rename Snapshot Record
// ------------------------------------------------------------------------
// This module records RMT information by Branch
// ------------------------------------------------------------------------

module scariv_bru_rn_snapshots    //
  import scariv_pkg::*;
  #(parameter REG_TYPE = GPR,
    localparam RNID_SIZE  = REG_TYPE == GPR ? XPR_RNID_SIZE :
                            REG_TYPE == FPR ? FPR_RNID_SIZE :
                            scariv_vec_pkg::VEC_RNID_SIZE,
    localparam RNID_W = $clog2(RNID_SIZE),
    parameter type rnid_t = logic [RNID_W-1: 0])
(
   input logic         i_clk,
   input logic         i_reset_n,

   input rnid_t i_rn_list[32],

   input grp_id_t      i_load,
   input grp_id_t      i_rd_valid,
   input logic [ 4: 0] i_rd_archreg[scariv_conf_pkg::DISP_SIZE],
   input rnid_t        i_rd_rnid   [scariv_conf_pkg::DISP_SIZE],
   input brtag_t       i_brtag     [scariv_conf_pkg::DISP_SIZE],

   // Branch Tag Update Signal
   br_upd_if.slave br_upd_if,

   output              rnid_t o_rn_list[32]
   );

logic [31: 0][RNID_W-1: 0] r_snapshots[scariv_conf_pkg::RV_BRU_ENTRY_SIZE];
/* verilator lint_off UNOPTFLAT */
logic [31: 0][RNID_W-1: 0] w_tmp_snapshots[scariv_conf_pkg::DISP_SIZE+1];

generate for(genvar i =  0; i < 32; i++) begin
  assign w_tmp_snapshots[0][i] = i_rn_list[i];
end
endgenerate

brtag_t w_brtag_sel;
bit_oh_or #(.T(brtag_t), .WORDS(scariv_conf_pkg::DISP_SIZE))
u_brtag_sel (.i_oh(i_load), .i_data(i_brtag), .o_selected(w_brtag_sel));


generate for(genvar r_idx =  0; r_idx < 32; r_idx++) begin : register_loop
  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
    /* verilator lint_off ALWCOMBORDER */
    assign w_tmp_snapshots[d_idx+1][r_idx] = i_rd_valid[d_idx] & (i_rd_archreg[d_idx] == r_idx[ 4: 0]) ? i_rd_rnid[d_idx] : w_tmp_snapshots[d_idx][r_idx[ 4: 0]];
  end

end
endgenerate

generate for (genvar b_idx = 0; b_idx < scariv_conf_pkg::RV_BRU_ENTRY_SIZE; b_idx++) begin
  logic [scariv_conf_pkg::DISP_SIZE-1: 0]          w_input_hit;
  logic [$clog2(scariv_conf_pkg::DISP_SIZE+1)-1: 0]  w_input_hit_enc;
  for (genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin
    assign w_input_hit[d_idx] = i_load[d_idx] & i_brtag[d_idx] == b_idx;
  end
  bit_encoder #(.WIDTH(scariv_conf_pkg::DISP_SIZE+1)) u_encoder (.i_in({w_input_hit, 1'b0}), .o_out(w_input_hit_enc));

  always_ff @ (posedge i_clk) begin
    if (|w_input_hit) begin
      for (int i_idx = 0; i_idx < 32; i_idx++) begin : reg_loop
        r_snapshots[b_idx][i_idx] <= w_tmp_snapshots[w_input_hit_enc][i_idx];
      end
    end
  end
end endgenerate

generate for(genvar i =  0; i < 32; i++) begin : o_loop
  assign o_rn_list[i] = r_snapshots[br_upd_if.brtag][i];
end
endgenerate

endmodule // scariv_bru_rn_snapshots

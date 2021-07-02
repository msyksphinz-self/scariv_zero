module msrh_bru_rn_snapshots
  import msrh_pkg::*;
  (
   input logic                                                i_clk,
   input logic                                                i_reset_n,

   input logic [RNID_W-1: 0]                                  i_rn_list[32],

   input logic [msrh_conf_pkg::DISP_SIZE-1: 0]                i_load,
   input logic [msrh_conf_pkg::DISP_SIZE-1: 0]                i_rd_valid,
   input logic [ 4: 0]                                        i_rd_archreg[msrh_conf_pkg::DISP_SIZE],
   input logic [RNID_W-1: 0]                                  i_rd_rnid[msrh_conf_pkg::DISP_SIZE],
   input logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] i_brtag [msrh_conf_pkg::DISP_SIZE],

   // Branch Tag Update Signal
   br_upd_if.slave                                            br_upd_if,

   output logic [RNID_W-1: 0]                                 o_rn_list[32]
   );

logic [31: 0][RNID_W-1: 0]                                    r_snapshots[msrh_conf_pkg::RV_BRU_ENTRY_SIZE];
/* verilator lint_off UNOPTFLAT */
logic [31: 0][RNID_W-1: 0]                                    w_tmp_snapshots[msrh_conf_pkg::DISP_SIZE+1];

generate for(genvar i =  0; i < 32; i++) begin
  assign w_tmp_snapshots[0][i] = i_rn_list[i];
end
endgenerate


generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop

  always_comb begin
    for(int i =  0; i < 32; i++) begin
      /* verilator lint_off ALWCOMBORDER */
      w_tmp_snapshots[d_idx+1][i] = i_rd_valid[d_idx] & (i_rd_archreg[d_idx] == i[ 4: 0]) ? i_rd_rnid[d_idx] : w_tmp_snapshots[d_idx][i];
    end
  end

  always_ff @ (posedge i_clk) begin
    if (i_load[d_idx]) begin
      for(int i =  0; i < 32; i++) begin
        r_snapshots[i_brtag[d_idx]][i] <= w_tmp_snapshots[d_idx+1][i];
      end
    end
  end

end
endgenerate


generate for(genvar i =  0; i < 32; i++) begin : o_loop
  assign o_rn_list[i] = r_snapshots[br_upd_if.brtag][i];
end
endgenerate

endmodule // msrh_bru_rn_snapshots

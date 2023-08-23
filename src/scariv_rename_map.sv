// ------------------------------------------------------------------------
// NAME : scariv_rename_map
// TYPE : module
// ------------------------------------------------------------------------
// Rename Map
// ------------------------------------------------------------------------
// Input: Logical Register Index
// Output: Physical Register Index
// ------------------------------------------------------------------------

module scariv_rename_map
  import scariv_pkg::*;
  import scariv_conf_pkg::*;
#(parameter REG_TYPE = GPR,
  localparam NUM_OPERANDS = (REG_TYPE == GPR) ? 2 : 3)
(
   input logic                     i_clk,
   input logic                     i_reset_n,

   input logic [DISP_SIZE * NUM_OPERANDS-1:0] i_arch_valid,
   input logic [ 4: 0]             i_arch_id[DISP_SIZE * NUM_OPERANDS],
   output rnid_t      o_rnid[DISP_SIZE * NUM_OPERANDS],

   input logic [ 4: 0]             i_rd_regidx[DISP_SIZE],
   output rnid_t      o_rd_old_rnid[DISP_SIZE],

   input logic [DISP_SIZE-1:0]     i_update,
   input logic [ 4: 0]             i_update_arch_id [DISP_SIZE],
   input rnid_t       i_update_rnid [DISP_SIZE],

   input logic                     i_restore_from_queue,
   input rnid_t       i_restore_rn_list[32],

   input logic [DISP_SIZE-1: 0]    i_commit_rd_valid,
   input logic [ 4: 0]             i_commit_rd_regidx[DISP_SIZE],
   input rnid_t       i_commit_rd_rnid[DISP_SIZE],

   output rnid_t      o_rn_list[32]
   );

rnid_t                r_map[32];

function logic [RNID_W: 0] select_latest_rnid (input logic [DISP_SIZE-1:0] i_update,
                                               input logic [ 4: 0]       tgt_arch_id,
                                               input logic [ 4: 0]       i_update_arch_id [DISP_SIZE],
                                               input rnid_t i_update_rnid [DISP_SIZE]);

rnid_t                                                      rnid_tmp[DISP_SIZE];
logic [DISP_SIZE-1: 0]                                                   valid_tmp;
logic [RNID_W: 0]                                                        ret;

  for (int i = 0; i < DISP_SIZE; i++) begin
    if (i_update[i] && i_update_arch_id[i] == tgt_arch_id) begin
      rnid_tmp [i] = i_update_rnid[i];
      valid_tmp[i] = 1'b1;
    end else begin
      if (i == 0) begin
        rnid_tmp [i] = 'h0;
        valid_tmp[i] = 1'b0;
      end else begin
        rnid_tmp [i] = rnid_tmp[i-1];
        valid_tmp[i] = valid_tmp[i-1];
      end
    end
  end

  ret = {valid_tmp[DISP_SIZE-1], rnid_tmp[DISP_SIZE-1]};
  return ret;

endfunction // select_latest_rnid

generate for (genvar i = 0; i < 32; i++) begin : map_loop
  if ((REG_TYPE == GPR) & (i == 0)) begin
    assign r_map[0] = 'h0;
  end else begin
    logic w_update;
    rnid_t w_update_rnid;

    logic [DISP_SIZE-1: 0] w_rd_active_valid;
    logic [DISP_SIZE-1: 0] w_rd_active_valid_oh;
    rnid_t    w_commit_rd_rnid;
    for (genvar d = 0; d < DISP_SIZE; d++) begin
      assign w_rd_active_valid[d] = i_commit_rd_valid[d] &
                                    (i_commit_rd_regidx[d] == i[4:0]);
    end
    bit_extract_msb #(.WIDTH(DISP_SIZE)) extract_latest_rd_bit(.in(w_rd_active_valid), .out(w_rd_active_valid_oh));
    bit_oh_or #(.T(logic[RNID_W-1:0]), .WORDS(DISP_SIZE)) bit_rnid_or(.i_oh(w_rd_active_valid_oh),
                                                                      .i_data(i_commit_rd_rnid),
                                                                      .o_selected(w_commit_rd_rnid));

    assign {w_update, w_update_rnid} = |w_rd_active_valid ? {1'b1, w_commit_rd_rnid} :
                                       i_restore_from_queue ? {1'b1, i_restore_rn_list[i]} :
                                       select_latest_rnid (i_update,
                                                           i,
                                                           i_update_arch_id,
                                                           i_update_rnid);
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_map[i] <= i;
      end else begin
        if (w_update) begin
          r_map[i] <= w_update_rnid;
        end
      end
    end
  end // else: !if((REG_TYPE == GPR) & (i == 0))
end
endgenerate

generate for (genvar d_idx = 0; d_idx < DISP_SIZE; d_idx++) begin : rnid_loop
  for (genvar rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin : rs_loop
    assign o_rnid[d_idx * NUM_OPERANDS + rs_idx] = r_map[i_arch_id[d_idx * NUM_OPERANDS + rs_idx]];
  end

  assign o_rd_old_rnid[d_idx] = r_map[i_rd_regidx[d_idx]];
end
endgenerate

assign o_rn_list = r_map;

endmodule // scariv_rename_map

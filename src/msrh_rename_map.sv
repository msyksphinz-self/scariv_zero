module msrh_rename_map
  import msrh_pkg::*;
import msrh_conf_pkg::*;
(
   input logic                     i_clk,
   input logic                     i_reset_n,

   input logic [DISP_SIZE * 2-1:0] i_arch_valid,
   input logic [ 4: 0]             i_arch_id[DISP_SIZE * 2],
   output logic [RNID_W-1: 0]      o_rnid[DISP_SIZE * 2],

   input logic [DISP_SIZE-1:0]     i_update,
   input logic [ 4: 0]             i_update_arch_id [DISP_SIZE],
   input logic [RNID_W-1: 0]       i_update_rnid [DISP_SIZE],

   input logic                     i_restore_from_queue,
   input logic [RNID_W-1: 0]       i_restore_rn_list[32],

   input logic [DISP_SIZE-1: 0]    i_commit_rd_valid,
   input logic [ 4: 0]             i_commit_rd_regidx[DISP_SIZE],
   input logic [RNID_W-1: 0]       i_commit_rd_rnid[DISP_SIZE],

   output logic [RNID_W-1: 0]      o_rn_list[32]
   );

logic [RNID_W-1: 0]                r_map[32];

function logic [RNID_W: 0] select_latest_rnid (input logic [DISP_SIZE-1:0] i_update,
                                               input logic [ 4: 0]       tgt_arch_id,
                                               input logic [ 4: 0]       i_update_arch_id [DISP_SIZE],
                                               input logic [RNID_W-1: 0] i_update_rnid [DISP_SIZE]);

logic [RNID_W-1: 0]                                                      rnid_tmp[DISP_SIZE];
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

assign r_map[0] = 'h0;
generate for (genvar i = 1; i < 32; i++) begin : map_loop
logic w_update;
logic [RNID_W-1: 0] w_update_rnid;

  logic [DISP_SIZE-1: 0] w_rd_active_valid;
  logic [DISP_SIZE-1: 0] w_rd_active_valid_oh;
  logic [RNID_W-1: 0]    w_commit_rd_rnid;
  for (genvar d = 0; d < DISP_SIZE; d++) begin
    assign w_rd_active_valid[d] = i_commit_rd_valid[d] &
                                  (i_commit_rd_regidx[d] == i[4:0]);
  end
  bit_extract_msb #(.WIDTH(DISP_SIZE)) extract_latest_rd_bit(.in(w_rd_active_valid), .out(w_rd_active_valid_oh));
  bit_oh_or #(.WIDTH(RNID_W), .WORDS(DISP_SIZE)) bit_rnid_or(.i_oh(w_rd_active_valid_oh),
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

end
endgenerate

generate for (genvar i = 0; i < DISP_SIZE; i++) begin : rnid_loop
  assign o_rnid[i * 2 + 0] = r_map[i_arch_id[i * 2 + 0]];
  assign o_rnid[i * 2 + 1] = r_map[i_arch_id[i * 2 + 1]];
end
endgenerate

assign o_rn_list = r_map;

endmodule // msrh_rename_map

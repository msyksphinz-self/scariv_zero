module msrh_inflight_list
  import msrh_pkg::*;
  #(parameter REG_TYPE = GPR,
    localparam NUM_OPERANDS = (REG_TYPE == GPR) ? 2 : 3)
(
   input logic                               i_clk,
   input logic                               i_reset_n,

   input rnid_t        i_rnid[msrh_conf_pkg::DISP_SIZE * NUM_OPERANDS],
   output logic [msrh_conf_pkg::DISP_SIZE * NUM_OPERANDS-1: 0] o_valids,

   input grp_id_t i_update_fetch_valid,
   input rnid_t   i_update_fetch_rnid[msrh_conf_pkg::DISP_SIZE],
   input grp_id_t i_update_fetch_data,

   input phy_wr_t i_phy_wr[TGT_BUS_SIZE]
   );

logic [TGT_BUS_SIZE-1: 0] w_phy_valids;
rnid_t       w_phy_rnids[TGT_BUS_SIZE];

logic [RNID_SIZE-1: 0]             r_inflight_list;

generate for (genvar rn_idx = 0; rn_idx < RNID_SIZE; rn_idx++) begin : list_loop
  if ((REG_TYPE == GPR) & (rn_idx == 0)) begin

    assign r_inflight_list[0] = 1'b1;

  end else begin
    grp_id_t w_update_fetch_valid_tmp;
    grp_id_t w_update_fetch_data_tmp;
  logic w_update_fetch_valid;
  logic w_update_fetch_data;
    for (genvar d_fetch_idx = 0; d_fetch_idx < msrh_conf_pkg::DISP_SIZE; d_fetch_idx++) begin
      assign w_update_fetch_valid_tmp [d_fetch_idx] = i_update_fetch_valid[d_fetch_idx] & (i_update_fetch_rnid[d_fetch_idx] == rn_idx);
      assign w_update_fetch_data_tmp[d_fetch_idx] = i_update_fetch_valid[d_fetch_idx] &  i_update_fetch_data[d_fetch_idx];
    end
    assign w_update_fetch_valid   = |w_update_fetch_valid_tmp;
    assign w_update_fetch_data  = |w_update_fetch_data_tmp;

  logic [TGT_BUS_SIZE-1: 0] w_target_valid_tmp;
  logic                               w_target_valid;
    for (genvar d_cmt_idx = 0; d_cmt_idx < TGT_BUS_SIZE; d_cmt_idx++) begin
      assign w_target_valid_tmp [d_cmt_idx] = i_phy_wr[d_cmt_idx].valid &
                                              (i_phy_wr[d_cmt_idx].rd_rnid == rn_idx) &
                                              (i_phy_wr[d_cmt_idx].rd_type == REG_TYPE);
    end
    assign w_target_valid   = |w_target_valid_tmp;


    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_inflight_list[rn_idx] <= 1'b1;
      end else begin
        if (w_update_fetch_valid) begin
          r_inflight_list[rn_idx] <= w_update_fetch_data;
        end else if (w_target_valid) begin
          r_inflight_list[rn_idx] <= 'b1;
        end
      end
    end // always_ff @ (posedge i_clk, negedge i_reset_n)

  end // else: !if((REG_TYPE == GPR) & (rn_idx == 0))
end // block: list_loop
endgenerate

generate for (genvar p_idx = 0; p_idx < TGT_BUS_SIZE; p_idx++) begin : phy_loop
  assign w_phy_valids[p_idx] = i_phy_wr[p_idx].valid & (i_phy_wr[p_idx].rd_type == REG_TYPE);
  assign w_phy_rnids [p_idx] = i_phy_wr[p_idx].rd_rnid;
end
endgenerate

generate for (genvar d_idx = 0; d_idx < msrh_conf_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  logic [NUM_OPERANDS-1: 0] w_update_fetch_valid;
  logic [NUM_OPERANDS-1: 0] w_update_fetch_data;

  logic [NUM_OPERANDS-1: 0] w_update_phy_valids;
  rnid_t w_update_phy_rnids[NUM_OPERANDS];

  for (genvar rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin : rs_update_loop
     // RS register file
     // Forwarding information from update_fetch path
     select_latest_1bit
       #(
         .SEL_WIDTH(msrh_conf_pkg::DISP_SIZE),
         .KEY_WIDTH(RNID_W)
         )
     u_select_latest_update_0
       (
        .i_cmp_key (i_rnid[d_idx * NUM_OPERANDS + rs_idx]),
        .i_valid (i_update_fetch_valid),
        .i_keys  (i_update_fetch_rnid),
        .i_data  (i_update_fetch_data),

        .o_valid (w_update_fetch_valid [rs_idx]),
        .o_data  (w_update_fetch_data[rs_idx])
        );

     // RS register file
     // Forwarding information from physical register file
     select_latest_1bit
       #(
         .SEL_WIDTH(TGT_BUS_SIZE),
         .KEY_WIDTH(RNID_W)
         )
     u_select_latest_phy_0
       (
        .i_cmp_key (i_rnid[d_idx * NUM_OPERANDS + rs_idx]),
        .i_valid (w_phy_valids),
        .i_keys  (w_phy_rnids),
        .i_data  (),

        .o_valid (w_update_phy_valids[rs_idx]),
        .o_data  ()
        );
  end // block: rs_loop

  for (genvar rs_idx = 0; rs_idx < NUM_OPERANDS; rs_idx++) begin : rs_loop
    logic                         w_is_x0_reg;
    assign w_is_x0_reg = (REG_TYPE == GPR) & (i_rnid[d_idx * NUM_OPERANDS + rs_idx] == 'h0);
    assign o_valids[d_idx * NUM_OPERANDS + rs_idx] = w_is_x0_reg                  ? 1'b1 :
                                                    w_update_phy_valids [rs_idx] ? 1'b1 :
                                                    w_update_fetch_valid[rs_idx] ? w_update_fetch_data[rs_idx] :
                                                    r_inflight_list[i_rnid[d_idx * NUM_OPERANDS + rs_idx]];
  end

end // block: disp_loop
endgenerate

endmodule // msrh_inflight_list

module msrh_inflight_list
  (
   input logic                               i_clk,
   input logic                               i_reset_n,

   input logic [msrh_pkg::RNID_W-1:0]        i_rnid[msrh_pkg::DISP_SIZE*2],
   output logic [msrh_pkg::DISP_SIZE*2-1: 0] o_valids,

   input logic [msrh_pkg::DISP_SIZE-1: 0]    i_update_fetch_vld,
   input logic [msrh_pkg::RNID_W-1:0]        i_update_fetch_addr[msrh_pkg::DISP_SIZE],
   input logic [msrh_pkg::DISP_SIZE-1: 0]    i_update_fetch_data,

   input msrh_pkg::target_t target_in[msrh_pkg::TGT_BUS_SIZE]
   );

logic [msrh_pkg::RNID_SIZE-1: 0]             r_inflight_list;
generate for (genvar rn_idx = 0; rn_idx < msrh_pkg::RNID_SIZE; rn_idx++) begin : list_loop
  logic [msrh_pkg::DISP_SIZE-1: 0] w_update_fetch_vld_tmp;
  logic [msrh_pkg::DISP_SIZE-1: 0] w_update_fetch_data_tmp;
  logic w_update_fetch_vld;
  logic w_update_fetch_data;
  for (genvar d_fetch_idx = 0; d_fetch_idx < msrh_pkg::DISP_SIZE; d_fetch_idx++) begin
    assign w_update_fetch_vld_tmp [d_fetch_idx] = i_update_fetch_vld[d_fetch_idx] & i_update_fetch_addr[d_fetch_idx] == rn_idx;
    assign w_update_fetch_data_tmp[d_fetch_idx] = i_update_fetch_vld[d_fetch_idx] & i_update_fetch_data[d_fetch_idx];
  end
  assign w_update_fetch_vld   = |w_update_fetch_vld_tmp;
  assign w_update_fetch_data  = |w_update_fetch_data_tmp;

  logic [msrh_pkg::DISP_SIZE-1: 0] w_target_vld_tmp;
  logic w_target_vld;
  for (genvar d_cmt_idx = 0; d_cmt_idx < msrh_pkg::DISP_SIZE; d_cmt_idx++) begin
    assign w_target_vld_tmp [d_cmt_idx] = target_in[d_cmt_idx].valid & target_in[d_cmt_idx].rd_rnid == rn_idx;
  end
  assign w_target_vld   = |w_target_vld_tmp;


  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_inflight_list[rn_idx] <= 1'b1;
    end else begin
      if (w_update_fetch_vld) begin
        r_inflight_list[rn_idx] <= w_update_fetch_data;
      end else if (w_target_vld) begin
        r_inflight_list[rn_idx] <= 'b1;
      end
    end
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end // block: list_loop
endgenerate


generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : disp_loop
logic w_update_fetch_vld_0;
logic w_update_fetch_vld_1;
logic w_update_fetch_data_0;
logic w_update_fetch_data_1;

  // RS1 register file
  // Forwarding information from update_fetch path
  select_latest_1bit
    #(
      .SEL_WIDTH(msrh_pkg::DISP_SIZE),
      .KEY_WIDTH(msrh_pkg::RNID_W)
      )
  u_select_latest_update_0
    (
     .i_cmp_key (i_rnid[d_idx * 2 + 0]),
     .i_valid (i_update_fetch_vld),
     .i_keys  (i_update_fetch_addr),
     .i_data  (i_update_fetch_data),

     .o_valid (w_update_fetch_vld_0),
     .o_data  (w_update_fetch_data_0)
     );

  // RS2 register file
  // Forwarding information from update_fetch path
  select_latest_1bit
    #(
      .SEL_WIDTH(msrh_pkg::DISP_SIZE),
      .KEY_WIDTH(msrh_pkg::RNID_W)
      )
  u_select_latest_update_1
    (
     .i_cmp_key (i_rnid[d_idx * 2 + 1]),
     .i_valid (i_update_fetch_vld),
     .i_keys  (i_update_fetch_addr),
     .i_data  (i_update_fetch_data),

     .o_valid (w_update_fetch_vld_1),
     .o_data  (w_update_fetch_data_1)
     );


  assign o_valids[d_idx * 2 + 0] = w_update_fetch_vld_0 ? w_update_fetch_data_0 : r_inflight_list[i_rnid[d_idx * 2 + 0]];
  assign o_valids[d_idx * 2 + 1] = w_update_fetch_vld_1 ? w_update_fetch_data_1 : r_inflight_list[i_rnid[d_idx * 2 + 1]];
end
endgenerate

endmodule // msrh_inflight_list

module mrh_inflight_list
  (
   input logic                              i_clk,
   input logic                              i_reset_n,

   input logic [ 4: 0]                      i_addr[mrh_pkg::DISP_SIZE*2],
   output logic [mrh_pkg::DISP_SIZE*2-1: 0] o_valids,

   input logic [mrh_pkg::DISP_SIZE-1: 0]    i_update_fetch_vld,
   input logic [ 4: 0]                      i_update_fetch_addr[mrh_pkg::DISP_SIZE],
   input logic [mrh_pkg::DISP_SIZE-1: 0]    i_update_fetch_data,

   input logic [mrh_pkg::DISP_SIZE-1: 0]    i_update_cmt_vld,
   input logic [ 4: 0]                      i_update_cmt_addr[mrh_pkg::DISP_SIZE],
   input logic [mrh_pkg::DISP_SIZE-1: 0]    i_update_cmt_data
   );

logic                                       r_inflight_list[31: 0];
generate for (genvar i = 0; i < 32; i++) begin : list_loop
  logic [mrh_pkg::DISP_SIZE-1: 0] w_update_fetch_vld_tmp;
  logic [mrh_pkg::DISP_SIZE-1: 0] w_update_fetch_data_tmp;
  logic w_update_fetch_vld;
  logic w_update_fetch_data;
  for (genvar d_fetch_idx = 0; d_fetch_idx < mrh_pkg::DISP_SIZE; d_fetch_idx++) begin
    assign w_update_fetch_vld_tmp [d_fetch_idx] = i_update_fetch_vld[d_fetch_idx] & i_update_fetch_addr[d_fetch_idx] == i;
    assign w_update_fetch_data_tmp[d_fetch_idx] = i_update_fetch_vld[d_fetch_idx] & i_update_fetch_data[d_fetch_idx];
  end
  assign w_update_fetch_vld   = |w_update_fetch_vld_tmp;
  assign w_update_fetch_data  = |w_update_fetch_data_tmp;

  logic [mrh_pkg::DISP_SIZE-1: 0] w_update_cmt_vld_tmp;
  logic [mrh_pkg::DISP_SIZE-1: 0] w_update_cmt_data_tmp;
  logic w_update_cmt_vld;
  logic w_update_cmt_data;
  for (genvar d_cmt_idx = 0; d_cmt_idx < mrh_pkg::DISP_SIZE; d_cmt_idx++) begin
    assign w_update_cmt_vld_tmp [d_cmt_idx] = i_update_cmt_vld[d_cmt_idx] & i_update_cmt_addr[d_cmt_idx] == i;
    assign w_update_cmt_data_tmp[d_cmt_idx] = i_update_cmt_vld[d_cmt_idx] & i_update_cmt_data[d_cmt_idx];
  end
  assign w_update_cmt_vld   = |w_update_cmt_vld_tmp;
  assign w_update_cmt_data  = |w_update_cmt_data_tmp;


  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_inflight_list[i] <= 1'b1;
    end else begin
      if (w_update_fetch_vld) begin
        r_inflight_list[i] <= w_update_fetch_data;
      end else if (w_update_cmt_vld) begin
        r_inflight_list[i] <= w_update_cmt_data;
      end
    end
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

end // block: list_loop
endgenerate


generate for (genvar d_idx = 0; d_idx < mrh_pkg::DISP_SIZE; d_idx++) begin : disp_loop
  logic w_update_vld_tmp[mrh_pkg::DISP_SIZE];
  always_comb begin
    if (i_update_fetch_vld[0] &&
        i_addr[d_idx * 2 + 0] == i_update_fetch_addr[0]) begin
      w_update_vld_tmp [0] = 1'b1;
      w_update_data_tmp[0] = i_update_fetch_data[0];
    end
  end

  for (int u_idx = 1; u_idx < mrh_pkg::DIPS_SIZE; u_idx++) begin
    always_comb begin
      if (i_update_fetch_vld[u_idx] &&
          i_addr[d_idx * 2 + 0] == i_update_fetch_addr[u_idx]) begin
        w_update_vld_tmp [u_idx] = 1'b1;
        w_update_data_tmp[u_idx] = i_update_fetch_data[u_idx];
      end else begin
        w_update_vld_tmp [u_idx] = w_update_vld_tmp [u_idx-1];
        w_update_data_tmp[u_idx] = w_update_data_tmp[u_idx-1];
      end
    end
  end // for (int u_idx = 0; u_idx < mrh_pkg::DIPS_SIZE; u_idx++)

  assign o_valids[d_idx * 2 + 0] = r_inflight_list[i_addr[d_idx * 2 + 0]];
  assign o_valids[d_idx * 2 + 1] = r_inflight_list[i_addr[d_idx * 2 + 1]];
end
endgenerate

endmodule // mrh_inflight_list

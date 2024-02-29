module distributed_mp_ram
  #(
    parameter WR_PORTS = 1,
    parameter RD_PORTS = 1,
    parameter WIDTH = 64,
    parameter WORDS = 256
  )
(
  input logic i_clk,
  input logic i_reset_n,

  input logic [WR_PORTS-1: 0]        i_wr,
  input logic [$clog2(WORDS)-1:0] i_wr_addr[WR_PORTS],
  input logic [WIDTH-1:0]         i_wr_data[WR_PORTS],

  input logic [$clog2(WORDS)-1:0] i_rd_addr[RD_PORTS],
  output logic [WIDTH-1:0]        o_rd_data[RD_PORTS]
);

logic [$clog2(WR_PORTS)-1: 0]             r_lvt [WORDS];
generate for (genvar r_idx = 0; r_idx < RD_PORTS; r_idx++) begin : w_rd_loop
  logic [WIDTH-1: 0]        w_rd_data[WR_PORTS];

  for (genvar w_idx = 0; w_idx < WR_PORTS; w_idx++) begin : w_wr_loop

    (* RAM_STYLE = "distributed" *) logic [WIDTH-1:0] data_array[WORDS];

    always_ff @ (posedge i_clk) begin
      if (i_wr[w_idx]) begin
        data_array[i_wr_addr[w_idx]] <= i_wr_data[w_idx];
      end
    end

    assign w_rd_data[w_idx] = data_array[i_rd_addr[r_idx]];
  end // block: w_wr_loop

  // logic [WIDTH-1: 0] w_rd_data_sel;
  // bit_oh_or #(.T(logic[WIDTH-1: 0]), .WORDS(WR_PORTS)) u_data_sel (.i_oh (r_lvt[i_rd_addr[r_idx]]), .i_data(w_rd_data), .o_selected(o_rd_data[r_idx]));
  assign o_rd_data[r_idx] = w_rd_data[r_lvt[i_rd_addr[r_idx]]];

end endgenerate // block: w_wr_loop


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int i = 0; i < WORDS; i++)
      r_lvt[i] <= 'h0;
  end else begin
    for (int i = 0; i < WR_PORTS; i++) begin
      if (i_wr[i]) begin
        r_lvt[i_wr_addr[i]] <= i;
      end
    end
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)


// generate for (genvar i = 0; i < WORDS; i++) begin : word_loop
//   logic [$clog2(WORDS)-1: 0] w_wr_addr_array[WR_PORTS];
//   logic [$clog2(WORDS)-1: 0] w_wr_addr;
//   for (genvar w_idx = 0; w_idx < WR_PORTS; w_idx++) begin
//     assign w_wr_valid[w_idx] = i_wr[w_idx] ? i_wr_addr[w_idx] : 'h0;
//   end
//   bit_oh_or #(.T(logic[$clog2(WORDS)-1: 0]), .WORDS(WR_PORTS)) u_data_sel (.i_oh (i_wr), .i_data(w_wr_addr_array), .o_selected(w_wr_addr_array));
//
//   always_ff @ (posedge i_clk, negedge i_reset_n) begin
//     if (!i_reset_n) begin
//       r_lvt[i] <= 'h1;
//     end else begin
//       r_lvt[i] <= |w_wr_valid ? w_wr_valid : r_lvt[i];
//     end
//   end // always_ff @ (posedge i_clk, negedge i_reset_n)
// end endgenerate // block: rnid_loop

endmodule // distributed_mp_ram

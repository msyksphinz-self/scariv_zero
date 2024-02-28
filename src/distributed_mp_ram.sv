module distributed_mp_ram
  #(
    parameter PORTS = 2,
    parameter WIDTH = 32,
    parameter WORDS = 12
  )
(
  input logic i_clk,
  input logic i_reset_n,

  input logic [PORTS-1: 0]        i_wr,
  input logic [$clog2(WORDS)-1:0] i_wr_addr[PORTS],
  input logic [WIDTH-1:0]         i_wr_data[PORTS],

  input logic [$clog2(WORDS)-1:0] i_rd_addr,
  output logic [WIDTH-1:0]        o_rd_data
);

`define IVT_MULTIPORT

`ifdef IVT_MULTIPORT

logic [PORTS-1: 0] r_lvt [WORDS];

logic [WIDTH-1: 0]        w_rd_data[PORTS];

generate for (genvar w_idx = 0; w_idx < PORTS; w_idx++) begin : w_wr_loop

  (* RAM_STYLE = "distributed" *) logic [WIDTH-1:0] data_array[WORDS];

  always_ff @ (posedge i_clk) begin
    if (i_wr[w_idx]) begin
      data_array[i_wr_addr[w_idx]] <= i_wr_data[w_idx];
    end
  end

  assign w_rd_data[w_idx] = data_array[i_rd_addr];

end endgenerate // block: w_wr_loop

logic [WIDTH-1: 0] w_rd_data_sel;
bit_oh_or #(.T(logic[WIDTH-1: 0]), .WORDS(PORTS)) u_data_sel (.i_oh (r_lvt[i_rd_addr]), .i_data(w_rd_data), .o_selected(o_rd_data));

generate for (genvar i = 0; i < WORDS; i++) begin : word_loop
  logic [PORTS-1: 0] w_wr_valid;
  for (genvar w_idx = 0; w_idx < PORTS; w_idx++) begin
    assign w_wr_valid[w_idx] = i_wr[w_idx] & (i_wr_addr[w_idx] == i);
  end

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_lvt[i] <= 'h1;
    end else begin
      r_lvt[i] <= |w_wr_valid ? w_wr_valid : r_lvt[i];
    end
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end endgenerate // block: rnid_loop

`else // IVT_MULTIPORT

(* RAM_STYLE = "distributed" *) logic [WIDTH-1:0] data_array[WORDS];

generate if (PORTS == 1) begin : dual_port

  always_ff @ (posedge i_clk) begin
    if (i_wr[0]) begin
      data_array[i_wr_addr[0]] <= i_wr_data[0];
    end
  end

  assign o_rd_data = data_array[i_rd_addr];

end else if (PORTS == 2) begin : triple_port

  always_ff @ (posedge i_clk) begin
    if (i_wr[0]) begin
      data_array[i_wr_addr[0]] <= i_wr_data[0];
    end
    if (i_wr[1]) begin
      data_array[i_wr_addr[1]] <= i_wr_data[1];
    end
  end

  assign o_rd_data = data_array[i_rd_addr];

end else begin : multi_port

  always_ff @ (posedge i_clk) begin
    for (int ports = 0; ports < PORTS; ports++) begin : wr_loop
      if (i_wr[ports]) begin
        data_array[i_wr_addr[ports]] <= i_wr_data[ports];
      end
    end
  end

  assign o_rd_data = data_array[i_rd_addr];

end endgenerate // block: multi_port

`endif // !`ifdef IVT_MULTIPORT

endmodule // distributed_mp_ram

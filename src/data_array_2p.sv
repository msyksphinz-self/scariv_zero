module data_array_2p
  #(
    parameter WIDTH = 32,
    parameter ADDR_W = 12
  )
(
  input logic               i_clk,
  input logic               i_reset_n,

  input logic               i_wr,
  input logic [ADDR_W-1:0]  i_wr_addr,
  input logic [WIDTH-1:0]   i_wr_data,

  input logic [ADDR_W-1: 0] i_rd_addr,
  output logic [WIDTH-1:0]  o_rd_data
);


logic [WIDTH-1:0] data_array[2**ADDR_W];

always_ff @ (posedge i_clk) begin
  if (i_wr) begin
    data_array[i_wr_addr] <= i_wr_data;
  end
  o_rd_data <= data_array[i_rd_addr];
end

endmodule

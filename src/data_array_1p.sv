module data_array_1p
  #(
    parameter WIDTH = 32,
    parameter ADDR_W = 12
  )
(
  input logic i_clk,
  input logic i_reset_n,

  input logic              i_wr,
  input logic [ADDR_W-1:0] i_addr,
  output logic [WIDTH-1:0] o_data,
  input logic [WIDTH-1:0]  i_data
);


logic [WIDTH-1:0] data_array[2**ADDR_W];

always_ff @ (posedge i_clk) begin
  if (i_wr) begin
    data_array[i_addr] <= i_data;
  end
  o_data <= data_array[i_addr];
end

endmodule

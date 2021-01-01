`default_nettype none

module data_array
  #(
    parameter WIDTH = 32,
    parameter ADDR_W = 12
  )
(
  input logic clk,
  input logic reset_n,

  input logic [ADDR_W-1:0] addr,
  output logic [WIDTH-1:0] data
);


logic [WIDTH-1:0] data_array[2**ADDR_W];

always_ff @ (posedge clk, negedge reset_n) begin
  if (!reset_n) begin
    data <= {WIDTH{1'b0}};
  end else begin
    data <= data_array[addr];
  end
end

endmodule

`default_nettype wire

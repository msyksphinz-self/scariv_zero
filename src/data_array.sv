module data_array
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

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_data <= {WIDTH{1'b0}};
  end else begin
    if (i_wr) begin
      data_array[i_addr] <= i_data;
    end
    o_data <= data_array[i_addr];
  end
end

endmodule

module distributed_ram
  #(
    parameter WIDTH = 32,
    parameter WORDS = 12
  )
(
  input logic i_clk,
  input logic i_reset_n,

  input logic                     i_wr,
  input logic [$clog2(WORDS)-1:0] i_wr_addr,
  input logic [WIDTH-1:0]         i_wr_data,

  input logic [$clog2(WORDS)-1:0] i_rd_addr,
  output logic [WIDTH-1:0]        o_rd_data
);


(* RAM_STYLE = "distributed" *) logic [WIDTH-1:0] data_array[WORDS];

always_ff @ (posedge i_clk) begin
  if (i_wr) begin
    data_array[i_wr_addr] <= i_wr_data;
  end
end

assign o_rd_data = data_array[i_rd_addr];

endmodule // distributed_ram

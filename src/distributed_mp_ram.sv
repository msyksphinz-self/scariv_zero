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


logic [WIDTH-1:0] data_array[WORDS];

always_ff @ (posedge i_clk) begin
  for (int ports = 0; ports < PORTS; ports++) begin : wr_loop
    if (i_wr[ports]) begin
      data_array[i_wr_addr[ports]] <= i_wr_data[ports];
    end
  end
end

assign o_rd_data = data_array[i_rd_addr];

endmodule // distributed_mp_ram

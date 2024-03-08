module distributed_1rd_ram
  #(
    parameter WR_PORTS = 2,
    parameter WIDTH = 32,
    parameter WORDS = 12
  )
(
  input logic i_clk,
  input logic i_reset_n,

  input logic [WR_PORTS-1: 0]        i_wr,
  input logic [$clog2(WORDS)-1:0] i_wr_addr[WR_PORTS],
  input logic [WIDTH-1:0]         i_wr_data[WR_PORTS],

  input logic [$clog2(WORDS)-1:0] i_rd_addr,
  output logic [WIDTH-1:0]        o_rd_data
);

logic [$clog2(WORDS)-1:0]         w_rd_addr[1];
logic [WIDTH-1:0]                 w_rd_data[1];

assign w_rd_addr[0] = i_rd_addr;
assign o_rd_data    = w_rd_data[0];

distributed_mp_ram
  #(.WR_PORTS(WR_PORTS),
    .RD_PORTS(1),
    .WIDTH   (WIDTH),
    .WORDS   (WORDS)
    )
u_ram
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr (i_wr),
   .i_wr_addr (i_wr_addr),
   .i_wr_data (i_wr_data),

   .i_rd_addr (w_rd_addr),
   .o_rd_data (w_rd_data)
   );

endmodule // distributed_1rd_ram

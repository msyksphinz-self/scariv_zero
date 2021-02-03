module bit_cnt
  #(
    parameter WIDTH=32
    )
(
 input logic [WIDTH-1:0]             in,
 output logic [$clog2(WIDTH+1)-1: 0] out
 );

if (WIDTH == 1) begin
  assign out = in;
end else begin
  localparam HALF = WIDTH/2;
logic [HALF-1:0] lo;
logic [WIDTH-HALF-1:0] hi;

logic [$clog2(HALF+1)-1:0]       tmp_lo;
logic [$clog2(WIDTH-HALF+1)-1:0] tmp_hi;

  bit_cnt #(.WIDTH(HALF))      cnt_lo(.in(in[HALF-1:0])    , .out(tmp_lo));
  bit_cnt #(.WIDTH(WIDTH-HALF))cnt_hi(.in(in[WIDTH-1:HALF]), .out(tmp_hi));

  assign out = tmp_lo + tmp_hi;
end
endmodule

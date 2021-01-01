`default_nettype none

module tag_array
  #(parameter TAG_W = 24,
    parameter WORDS = 12)
  (
    input logic clk,
    input logic reset_n,
    input logic [WORDS-1: 0] addr,
    output logic [TAG_W-1:0] tag,
    output logic             tag_valid
  );

  logic [TAG_W-1:0]    tag_array[2**WORDS];
  logic [2**WORDS-1:0] tag_valids;

  always_ff @ (posedge clk, negedge reset_n) begin
    if (!reset_n) begin
      tag <= {TAG_W{1'b0}};
      tag_valid <= 1'b0;
    end else begin
      tag <= tag_array[addr[WORDS-1:0]];
      tag_valid <= tag_valids[addr[WORDS-1:0]];
    end
  end

endmodule

`default_nettype wire

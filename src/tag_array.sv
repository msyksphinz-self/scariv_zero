// `default_nettype none

module tag_array
  #(parameter TAG_W = 24,
    parameter WORDS = 12)
  (
    input logic i_clk,
    input logic i_reset_n,
    input logic [WORDS-1: 0] i_addr,
    output logic [TAG_W-1:0] o_tag,
    output logic             o_tag_valid
  );

  logic [TAG_W-1:0]    tag_array[2**WORDS];
  logic [2**WORDS-1:0] tag_valids;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      o_tag <= {TAG_W{1'b0}};
      o_tag_valid <= 1'b0;
    end else begin
      o_tag <= tag_array[i_addr[WORDS-1:0]];
      o_tag_valid <= tag_valids[i_addr[WORDS-1:0]];
    end
  end

endmodule

// `default_nettype wire

// `default_nettype none

module tag_array
  #(parameter TAG_W = 24,
    parameter WORDS = 32)
  (
    input logic                      i_clk,
    input logic                      i_reset_n,

    input logic                      i_tag_clear,

    input logic                      i_wr,
    input logic [$clog2(WORDS)-1: 0] i_addr,
    input logic [TAG_W-1:0]          i_tag,
    input logic                      i_tag_valid,
    output logic [TAG_W-1:0]         o_tag,
    output logic                     o_tag_valid
  );

logic [TAG_W-1:0]            r_tag_array[WORDS];
logic [WORDS-1:0]            r_tag_valids;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      o_tag_valid <= 1'b0;

      /* verilator lint_off WIDTHCONCAT */
      r_tag_valids <= {(WORDS){1'b0}};
    end else begin
      if (i_tag_clear) begin
        r_tag_valids <= 'h0;
      end else if (i_wr) begin
        r_tag_valids[i_addr] <= i_tag_valid;
      end else begin
        o_tag_valid <= r_tag_valids[i_addr];
      end
    end
  end // always_ff @ (posedge i_clk, negedge i_reset_n)


  always_ff @ (posedge i_clk) begin
    if (i_wr) begin
      r_tag_array[i_addr] <= i_tag;
    end
    o_tag <= r_tag_array[i_addr];
  end // always_ff @ (posedge i_clk, negedge i_reset_n)

endmodule

// `default_nettype wire

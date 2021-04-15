interface cre_ret_if #(MAX_INC = 2);

logic [$clog2(MAX_INC)-1: 0] credit_vals;
logic [$clog2(MAX_INC)-1: 0] return_vals;

modport master (
  output credit_vals,
  input  return_vals
);

modport slave (
  input  credit_vals,
  output return_vals
);

endinterface // cre_ret_if


module msrh_credit_return_master
  #(parameter MAX_CREDITS = 10)
(
 input logic i_clk,
 input logic i_reset_n,

 cre_ret_if.master cre_ret_if,

 input i_get_credit,
 input [$clog2(MAX_CREDITS)-1: 0] i_credit_val,

 output [$clog2(MAX_CREDITS)-1: 0] o_credits,
 output                            o_no_credits
 );

logic [$clog2(MAX_CREDITS)-1: 0] r_credits;
logic [$clog2(MAX_CREDITS)-1: 0] w_credits_next;
logic [$clog2(MAX_CREDITS)-1: 0] r_credit_inc;

assign w_credits_next = r_credits -
                        /* verilator lint_off WIDTH */
                        (|(cre_ret_if.credit_vals) ? cre_ret_if.credit_vals : 'h0) +
                        (|(cre_ret_if.return_vals) ? cre_ret_if.return_vals : 'h0);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_credits <= MAX_CREDITS;
    r_credit_inc <= 'h0;
  end else begin
    r_credit_inc <= i_get_credit ? i_credit_val : 'h0;
    r_credits <= w_credits_next;
  end
end

assign cre_ret_if.credit_vals = r_credit_inc;

assign o_credits    = r_credits;
assign o_no_credits = r_credits == 'h0;

endmodule // msrh_credit_return_master

module msrh_credit_return_slave
  #(parameter MAX_CREDITS = 10)
(
 input logic i_clk,
 input logic i_reset_n,

 cre_ret_if.slave cre_ret_if
 );

logic [$clog2(MAX_CREDITS)-1: 0] r_credits;
logic [$clog2(MAX_CREDITS)-1: 0] w_credits_next;

assign w_credits_next = r_credits +
                        ((|cre_ret_if.credit_vals) ? cre_ret_if.credit_vals : 'h0) -
                        ((|cre_ret_if.return_vals) ? cre_ret_if.return_vals : 'h0);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_credits <= 0;
  end else begin
    r_credits <= w_credits_next;
  end
end

endmodule // msrh_credit_return_slave

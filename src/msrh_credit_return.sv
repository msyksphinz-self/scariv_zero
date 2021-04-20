interface cre_ret_if #(MAX_INC = 2);

logic [$clog2(MAX_INC): 0] credit_vals;
logic [$clog2(MAX_INC): 0] return_vals;

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
 input [$clog2(MAX_CREDITS): 0] i_credit_val,

 output [$clog2(MAX_CREDITS): 0] o_credits,
 output                          o_no_credits
 );

logic [$clog2(MAX_CREDITS): 0] r_credits;
logic [$clog2(MAX_CREDITS): 0] w_credits_next;
logic [$clog2(MAX_CREDITS): 0] r_credit_inc;

logic                          w_no_credits;

/* verilator lint_off WIDTH */
assign w_no_credits = r_credits + cre_ret_if.return_vals < i_credit_val;
assign w_credits_next =  w_no_credits ? r_credits + cre_ret_if.return_vals :
                         r_credits - (i_get_credit ? i_credit_val : 'h0) + cre_ret_if.return_vals;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_credits <= MAX_CREDITS;
    r_credit_inc <= 'h0;
  end else begin
    r_credit_inc <= i_get_credit ? i_credit_val : 'h0;
    r_credits <= w_credits_next;
  end
end

/* verilator lint_off WIDTH */
assign cre_ret_if.credit_vals = r_credit_inc;

assign o_credits    = r_credits;
assign o_no_credits = w_no_credits;

endmodule // msrh_credit_return_master

module msrh_credit_return_slave
  #(parameter MAX_CREDITS = 10)
(
 input logic i_clk,
 input logic i_reset_n,

 input i_get_return,
 input [$clog2(MAX_CREDITS): 0] i_return_val,

 cre_ret_if.slave cre_ret_if
 );

logic [$clog2(MAX_CREDITS): 0] r_credits;
logic [$clog2(MAX_CREDITS): 0] w_credits_next;
logic [$clog2(MAX_CREDITS): 0] r_return_dec;

logic [$clog2(MAX_CREDITS): 0] w_credits_diff;

/* verilator lint_off WIDTH */
assign w_credits_diff = ((|cre_ret_if.credit_vals) ? cre_ret_if.credit_vals : 'h0) -
                        (i_get_return ? i_return_val : 'h0);

assign w_credits_next = r_credits + w_credits_diff;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_credits <= 0;
    r_return_dec <= 'h0;
  end else begin
    r_credits <= w_credits_next;
    r_return_dec <= i_get_return ? i_return_val : 'h0;
  end
end

assign cre_ret_if.return_vals = r_return_dec;

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (r_credits > MAX_CREDITS) begin
      $fatal(0, "Credits is bigger than initial value. r_credits = %d, must not be excced than %d\n",
             r_credits, MAX_CREDITS);
    end
  end
end
`endif // SIMULATION

endmodule // msrh_credit_return_slave

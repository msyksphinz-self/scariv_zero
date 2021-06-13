module inoutptr_var
  #(
    parameter SIZE = 32
    )
(
 input logic                     i_clk,
 input logic                     i_reset_n,

 input logic                     i_rollback,

 input logic                     i_in_valid,
 input logic [$clog2(SIZE)-1:0]  i_in_val,
 output logic [$clog2(SIZE)-1:0] o_in_ptr,
 input logic                     i_out_valid,
 input logic [$clog2(SIZE)-1:0]  i_out_val,
 output logic [$clog2(SIZE)-1:0] o_out_ptr
 );

logic [$clog2(SIZE)-1:0] r_inptr;
logic [$clog2(SIZE)-1:0] r_outptr;

logic [$clog2(SIZE)-1:0] w_inptr_next;
logic [$clog2(SIZE)-1:0] w_outptr_next;

/* verilator lint_off WIDTH */
assign w_inptr_next  = i_in_valid ? (r_inptr + i_in_val < SIZE ? r_inptr + i_in_val : r_inptr + i_in_val - SIZE)  :
                       r_inptr;
/* verilator lint_off WIDTH */
assign w_outptr_next = i_rollback  ? w_inptr_next :
                       i_out_valid ? (r_outptr + i_out_val < SIZE ? r_outptr + i_out_val : r_outptr + i_out_val - SIZE) :
                       r_outptr;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_inptr  <= 'h0;
    r_outptr <= 'h0;
  end else begin
    r_inptr  <= w_inptr_next;
    r_outptr <= w_outptr_next;
  end
end

assign o_in_ptr  = r_inptr;
assign o_out_ptr = r_outptr;

// `ifdef SIMULATION
// logic signed [$clog2(SIZE)+1: 0] r_sim_cnt;
// always_ff @ (posedge i_clk, negedge i_reset_n) begin
//   if (!i_reset_n) begin
//     r_sim_cnt <= 'h0;
//   end else begin
//     /* verilator lint_off WIDTH */
//     r_sim_cnt <= r_sim_cnt +
//                  (i_in_valid ? i_in_val : 'h0) -
//                  (i_out_valid ? i_out_val : 'h0);
//   end
//   if (r_sim_cnt < 0) begin
//     $fatal (0, "inoutptr_var must not be minus");
//   end
//   if (r_sim_cnt >= SIZE) begin
//     $fatal (0, "inoutptr_var must not be exceeded %d", SIZE);
//   end
// end
//
//`endif // SIMULATION

endmodule // inoutptr

// ------------------------------------------------------------------------
// NAME : scariv_freelist
// TYPE : module
// ------------------------------------------------------------------------
// Freelist for Physical ID
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_freelist
  #(
    parameter SIZE = 32,
    parameter WIDTH = 5,
    parameter INIT = 0
    )
(
 input logic              i_clk,
 input logic              i_reset_n,

 input logic              i_push,
 input logic [WIDTH-1:0]  i_push_id,

 input logic              i_pop,
 output logic [WIDTH-1:0] o_pop_id,

 output logic             o_is_empty
 );

(* mark_debug="true" *) (* dont_touch="true" *) logic [SIZE-1: 0][WIDTH-1: 0] r_freelist;

(* mark_debug="true" *) (* dont_touch="true" *) logic [$clog2(SIZE)-1:0]  r_head_ptr;
(* mark_debug="true" *) (* dont_touch="true" *) logic [$clog2(SIZE)-1:0]  r_tail_ptr;

(* mark_debug="true" *) (* dont_touch="true" *) logic [SIZE-1:0]          r_active_bits;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_ptr <= 'h0;
    r_tail_ptr <= 'h0;
    r_active_bits <= {SIZE{1'b1}};
    for (int i = 0; i < SIZE; i++) begin
      r_freelist[i] <= INIT + i;
    end
  end else begin
    if (i_push) begin
      if (r_tail_ptr == SIZE-1) begin
        r_tail_ptr <= 'h0;
      end else begin
        r_tail_ptr <= r_tail_ptr + 'h1;
      end
      r_active_bits[r_tail_ptr] <= 1'b1;
      r_freelist[r_tail_ptr] <= i_push_id;
    end
    if (i_pop) begin
      if (r_head_ptr == SIZE-1) begin
        r_head_ptr <= 'h0;
      end else begin
        r_head_ptr <= r_head_ptr + 'h1;
      end
      r_active_bits[r_head_ptr] <= 1'b0;
`ifdef SIMULATION
      // delete poped ID for debug
      r_freelist[r_head_ptr] <= 'h0;
`endif // SIMULATION
    end
  end
end

assign o_pop_id = r_freelist[r_head_ptr];

assign o_is_empty = ~(|r_active_bits);


// Debug signals to capture violation

(* mark_debug="true" *) (* dont_touch="true" *) logic [SIZE-1: 0][SIZE-1: 1] r_conflict;
(* mark_debug="true" *) (* dont_touch="true" *) logic [SIZE-1: 0]            w_line_conflict;
(* mark_debug="true" *) (* dont_touch="true" *) logic                        r_detect_conflict;
generate for (genvar y = 0; y < SIZE; y++) begin : y_confilct_loop
  assign w_line_conflict[y] = |r_conflict[y];
  for (genvar x = 1; x < SIZE; x++) begin : x_conflict_loop
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_conflict[y][x] <= 1'b0;
      end else begin
        if (x <= y) begin
          r_conflict[y][x] <= 1'b0;
        end else begin
          r_conflict[y][x] <= r_freelist[x] == r_freelist[y];
        end
      end
    end // always_ff @ (posedge i_clk, negedge i_reset_n)
  end // block: x_conflict_loop
end endgenerate
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_detect_conflict <= 1'b0;
  end else begin
    r_detect_conflict <= |w_line_conflict;
  end
end

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (o_is_empty && i_pop & ~i_push) begin
      $fatal(0, "When freelist is empty, i_pop must not be asserted");
    end
    if (r_detect_conflict) begin
      $fatal(0, "Resouce conflicted.");
    end
  end
end
`endif // SIMULATION

endmodule // scariv_freelist

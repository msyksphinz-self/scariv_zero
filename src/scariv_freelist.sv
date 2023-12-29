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

 // Update VLMUL size
 vlmul_upd_if.slave       vlmul_upd_if,

 input logic              i_push,
 input logic [WIDTH-1:0]  i_push_id,

 input logic              i_pop,
 output logic [WIDTH-1:0] o_pop_id,

 output logic             o_is_empty
 );

logic [WIDTH-1:0]         r_freelist[SIZE];

logic [$clog2(SIZE)-1:0]  r_head_ptr;
logic [$clog2(SIZE)-1:0]  r_tail_ptr;

logic [SIZE-1:0]          r_active_bits;

logic [$clog2(SIZE): 0]   r_ptr_limit;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ptr_limit <= SIZE;
  end else begin
    if (vlmul_upd_if.valid) begin
      case (vlmul_upd_if.vlmul)
        3'b000  : r_ptr_limit <= SIZE / 1;
        3'b001  : r_ptr_limit <= SIZE / 2;
        3'b010  : r_ptr_limit <= SIZE / 4;
        3'b011  : r_ptr_limit <= SIZE / 8;
        default : r_ptr_limit <= SIZE / 1;
      endcase // case (vlmul_upd_if.vlmul)
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)



always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_ptr <= 'h0;
    r_tail_ptr <= 'h0;
    r_active_bits <= {SIZE{1'b1}};
    for (int i = 0; i < SIZE; i++) begin
      /* verilator lint_off WIDTH */
      r_freelist[i] = INIT + i;
    end
  end else begin
    if (vlmul_upd_if.valid) begin
      case (vlmul_upd_if.vlmul)
        3'b000  : begin
          for (int i = 0; i < SIZE; i++) r_freelist[i] <= INIT + i;
        end
        3'b001  : begin
          for (int i = 0;      i < SIZE/2; i++) r_freelist[i] <= INIT + (i << 1);
          for (int i = SIZE/2; i < SIZE;   i++) r_freelist[i] <= 'h0;
        end
        3'b010  : begin
          for (int i = 0;      i < SIZE/4; i++) r_freelist[i] <= INIT + (i << 2);
          for (int i = SIZE/4; i < SIZE;   i++) r_freelist[i] <= 'h0;
        end
        3'b011  : begin
          for (int i = 0;      i < SIZE/8; i++) r_freelist[i] <= INIT + (i << 3);
          for (int i = SIZE/8; i < SIZE;   i++) r_freelist[i] <= 'h0;
        end
        default : begin
          for (int i = 0; i < SIZE; i++) begin
            r_freelist[i] <= INIT + i;
          end
        end
      endcase // case (vlmul_upd_if.vlmul)
      r_tail_ptr <= 'h0;
      r_head_ptr <= 'h0;
    end
    if (i_push) begin
      if (r_tail_ptr == r_ptr_limit-1) begin
        r_tail_ptr <= 'h0;
      end else begin
        r_tail_ptr <= r_tail_ptr + 'h1;
      end
      r_active_bits[r_tail_ptr] <= 1'b1;
      r_freelist[r_tail_ptr] <= i_push_id;
    end
    if (i_pop) begin
      if (r_head_ptr == r_ptr_limit-1) begin
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

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (o_is_empty && i_pop & ~i_push) begin
      $fatal(0, "When freelist is empty, i_pop must not be asserted");
    end
  end
end
`endif // SIMULATION

endmodule // scariv_freelist

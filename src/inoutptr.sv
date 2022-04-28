module inoutptr
  #(
    parameter SIZE = 32
    )
(
 input logic                     i_clk,
 input logic                     i_reset_n,

 input logic                     i_clear,

 input logic                     i_in_valid,
 output logic [$clog2(SIZE)-1:0] o_in_ptr,
 input logic                     i_out_valid,
 output logic [$clog2(SIZE)-1:0] o_out_ptr
 );

logic [$clog2(SIZE)-1:0] r_inptr;
logic [$clog2(SIZE)-1:0] r_outptr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_inptr  <= 'h0;
    r_outptr <= 'h0;
  end else begin
    if (i_clear) begin
      r_inptr  <= 'h0;
      r_outptr <= 'h0;
    end else begin
      if (i_in_valid) begin
        if (r_inptr == SIZE-1) begin
          r_inptr  <= 'h0;
        end else begin
          r_inptr  <= r_inptr + 'h1;
        end
      end
      if (i_out_valid) begin
        if (r_outptr == SIZE-1) begin
          r_outptr <= 'h0;
        end else begin
          r_outptr <= r_outptr + 'h1;
        end
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign o_in_ptr  = r_inptr;
assign o_out_ptr = r_outptr;

`ifdef SIMULATION
int num_counter;
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    num_counter <= 'h0;
  end else begin
    if (i_clear) begin
      num_counter <= 'h0;
    end else begin
      case ({i_in_valid, i_out_valid})
        2'b10 : num_counter <= num_counter + 1;
        2'b01 : num_counter <= num_counter - 1;
        default : num_counter <= num_counter;
      endcase // case ({i_in_valid, i_out_valid})
    end
    if (num_counter < 0) begin
      $display("%m inoutptr counter become minus. Invalid");
      $fatal(0, "%m inoutptr counter become minus. Invalid");
    end
    if (num_counter > SIZE) begin
      $display("%m inoutptr counter exceeded. Fatal");
      $fatal(0, "%m inoutptr counter exceeded. Fatal");
    end
  end
end

`endif // SIMULATION

endmodule // inoutptr

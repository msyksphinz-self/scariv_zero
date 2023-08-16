// ------------------------------------------------------------------------
// NAME : bit_clz_32
// TYPE : module
// ------------------------------------------------------------------------
// Count Leading Zero with 32-bit
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module bit_clz_32
  (
   input logic [31: 0] i_in,
   output logic [5: 0] o_out
   );

always_comb begin
  /* verilator lint_off CASEX */
  casex (i_in)
    'b1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h00;
    'b01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h01;
    'b001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h02;
    'b0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h03;
    'b0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h04;
    'b0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h05;
    'b0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h06;
    'b0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h07;
    'b0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h08;
    'b0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h09;
    'b0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0a;
    'b0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0b;
    'b0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0c;
    'b0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0d;
    'b0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx : o_out = 'h0e;
    'b0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx : o_out = 'h0f;
    'b0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx : o_out = 'h10;
    'b0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx : o_out = 'h11;
    'b0000_0000_0000_0000_001x_xxxx_xxxx_xxxx : o_out = 'h12;
    'b0000_0000_0000_0000_0001_xxxx_xxxx_xxxx : o_out = 'h13;
    'b0000_0000_0000_0000_0000_1xxx_xxxx_xxxx : o_out = 'h14;
    'b0000_0000_0000_0000_0000_01xx_xxxx_xxxx : o_out = 'h15;
    'b0000_0000_0000_0000_0000_001x_xxxx_xxxx : o_out = 'h16;
    'b0000_0000_0000_0000_0000_0001_xxxx_xxxx : o_out = 'h17;
    'b0000_0000_0000_0000_0000_0000_1xxx_xxxx : o_out = 'h18;
    'b0000_0000_0000_0000_0000_0000_01xx_xxxx : o_out = 'h19;
    'b0000_0000_0000_0000_0000_0000_001x_xxxx : o_out = 'h1a;
    'b0000_0000_0000_0000_0000_0000_0001_xxxx : o_out = 'h1b;
    'b0000_0000_0000_0000_0000_0000_0000_1xxx : o_out = 'h1c;
    'b0000_0000_0000_0000_0000_0000_0000_01xx : o_out = 'h1d;
    'b0000_0000_0000_0000_0000_0000_0000_001x : o_out = 'h1e;
    'b0000_0000_0000_0000_0000_0000_0000_0001 : o_out = 'h1f;
    'b0000_0000_0000_0000_0000_0000_0000_0000 : o_out = 'h20;
    default : o_out = 'h00;
  endcase // casex (i_in)
end // always_comb

endmodule // bit_clz_32

// ------------------------------------------------------------------------
// NAME : bit_clz_64
// TYPE : module
// ------------------------------------------------------------------------
// Count Leading Zero with 64-bit
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module bit_clz_64
  (
   input logic [63: 0] i_in,
   output logic [6: 0] o_out
   );

always_comb begin
  /* verilator lint_off CASEX */
  casex (i_in)
    64'b1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h00;
    64'b01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h01;
    64'b001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h02;
    64'b0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h03;
    64'b0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h04;
    64'b0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h05;
    64'b0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h06;
    64'b0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h07;
    64'b0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h08;
    64'b0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h09;
    64'b0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0a;
    64'b0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0b;
    64'b0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0c;
    64'b0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0d;
    64'b0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0e;
    64'b0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h0f;
    64'b0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h10;
    64'b0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h11;
    64'b0000_0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h12;
    64'b0000_0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h13;
    64'b0000_0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h14;
    64'b0000_0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h15;
    64'b0000_0000_0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h16;
    64'b0000_0000_0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h17;
    64'b0000_0000_0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h18;
    64'b0000_0000_0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h19;
    64'b0000_0000_0000_0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h1a;
    64'b0000_0000_0000_0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h1b;
    64'b0000_0000_0000_0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h1c;
    64'b0000_0000_0000_0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h1d;
    64'b0000_0000_0000_0000_0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h1e;
    64'b0000_0000_0000_0000_0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h1f;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h20;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h21;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h22;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h23;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h24;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h25;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h26;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h27;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h28;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h29;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h2a;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h2b;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx_xxxx : o_out = 'h2c;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx_xxxx : o_out = 'h2d;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_001x_xxxx_xxxx_xxxx_xxxx : o_out = 'h2e;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001_xxxx_xxxx_xxxx_xxxx : o_out = 'h2f;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1xxx_xxxx_xxxx_xxxx : o_out = 'h30;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_01xx_xxxx_xxxx_xxxx : o_out = 'h31;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_001x_xxxx_xxxx_xxxx : o_out = 'h32;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001_xxxx_xxxx_xxxx : o_out = 'h33;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1xxx_xxxx_xxxx : o_out = 'h34;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_01xx_xxxx_xxxx : o_out = 'h35;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_001x_xxxx_xxxx : o_out = 'h36;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001_xxxx_xxxx : o_out = 'h37;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1xxx_xxxx : o_out = 'h38;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_01xx_xxxx : o_out = 'h39;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_001x_xxxx : o_out = 'h3a;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001_xxxx : o_out = 'h3b;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1xxx : o_out = 'h3c;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_01xx : o_out = 'h3d;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_001x : o_out = 'h3e;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001 : o_out = 'h3f;
    64'b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 : o_out = 'h40;
    default : o_out = 'h00;
  endcase // casex (i_in)
end // always_comb

endmodule // bit_clz_64

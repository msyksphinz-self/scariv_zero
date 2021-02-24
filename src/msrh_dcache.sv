module msrh_dcache
  (
   input logic i_clk,
   input logic i_reset_n,

   l1d_if.slave l1d_if[msrh_pkg::LSU_INST_NUM]
   );

generate for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : port_loop
  assign l1d_if[p_idx].hit = 1'b0;
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      l1d_if[p_idx].miss <= 1'b0;
    end else begin
      l1d_if[p_idx].miss <= l1d_if[p_idx].valid;
    end
  end
end
endgenerate

endmodule // msrh_dcache

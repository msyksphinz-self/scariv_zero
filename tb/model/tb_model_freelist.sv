module tb_model_scariv;

logic w_clk;
assign w_clk = tb.w_clk;

import scariv_pkg::*;

// Model of FreeList
int freelist[DISP_SIZE][$];
initial begin
  for(integer d = 0; d < DISP_SIZE; d++) begin
    for(integer r = 0; r < RNID_SIZE; i++) begin
      freelist.push_back(d * RNID_SIZE + r + 32);
    end
  end
end


always_ff @ (negedge i_clk) begin
  if (tb.u_scariv_tile_wrapper.u_scariv_tile.u_scariv_rename.sc_dips.valid) begin

  end
end

endmodule // tb_model_scariv

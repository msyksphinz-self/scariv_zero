module mrh_alu
  #(
    parameter PORT_BASE = 0
    )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 input logic [mrh_pkg::DISP_SIZE-1: 0] disp_valid,
 disp_if.slave                         disp
);

mrh_pkg::disp_t w_disp_inst[mrh_pkg::DISP_SIZE];
mrh_pkg::disp_t disp_picked_inst[2];
logic [ 1: 0]   disp_picked_inst_valid;

generate for(genvar d_idx = 0; d_idx < mrh_pkg::DISP_SIZE; d_idx++) begin : d_loop
  assign w_disp_inst[d_idx] = disp.inst[d_idx];
end
endgenerate

generate for(genvar p_idx = 0; p_idx < 2; p_idx++) begin : pick_loop
  bit_pick_1_index
                     #(
                       .NUM(PORT_BASE + p_idx),
                       .SEL_WIDTH(mrh_pkg::DISP_SIZE),
                       .DATA_WIDTH ($size(mrh_pkg::disp_t))
                       )
  u_bit_pick_1_index
                     (
                      .i_valids (disp_valid),
                      .i_data   (w_disp_inst),
                      .o_valid  (disp_picked_inst_valid[p_idx]),
                      .o_data   (disp_picked_inst[p_idx])
                      );
end // block: d_loop
endgenerate

mrh_scheduler
  #(
    .ENTRY_SIZE(32),
    .IN_PORT_SIZE(2)
    )
u_mrh_scheduler
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .i_disp_valid (disp_picked_inst_valid),
   .i_disp_info  (disp_picked_inst)
   );


endmodule // mrh_alu

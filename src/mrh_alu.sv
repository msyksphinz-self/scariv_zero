module mrh_alu
  #(
    parameter PORT_BASE = 0
    )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 input logic [mrh_pkg::DISP_SIZE-1: 0] disp_valid,
 disp_if.slave                         disp,

 /* Forwarding path */
 input mrh_pkg::release_t        release_in[mrh_pkg::REL_BUS_SIZE],
 input mrh_pkg::target_t         target_in [mrh_pkg::TGT_BUS_SIZE],

 /* write output */
 output mrh_pkg::release_t        ex1_release_out,
 output mrh_pkg::target_t         ex3_target_out
);

mrh_pkg::disp_t w_disp_inst[mrh_pkg::DISP_SIZE];
mrh_pkg::disp_t disp_picked_inst[2];
logic [ 1: 0]   disp_picked_inst_valid;
mrh_pkg::issue_t w_rv0_issue;


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
   .i_disp_info  (disp_picked_inst),

   .release_in (release_in),

   .o_issue (w_rv0_issue)
   );


mrh_alu_pipe
  u_alu
    (
     .i_clk    (i_clk),
     .i_reset_n(i_reset_n),

     .rv0_issue  (w_rv0_issue),
     .target_in  (target_in  ),

     .ex1_release_out (ex1_release_out),
     .ex3_target_out  (ex3_target_out )
     );


endmodule // mrh_alu

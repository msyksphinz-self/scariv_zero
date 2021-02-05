module mrh_rename
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.slave disp
   );

logic [$clog2(mrh_pkg::RNID_SIZE)-1: 0] rd_id[mrh_pkg::DISP_SIZE];

logic [mrh_pkg::DISP_SIZE * 2-1: 0]     w_archreg_valid;
logic [ 4: 0]                           w_archreg[mrh_pkg::DISP_SIZE * 2];
logic [mrh_pkg::RNID_W-1: 0]            w_rnid[mrh_pkg::DISP_SIZE * 2];

logic [ 4: 0]                           w_update_arch_id [mrh_pkg::DISP_SIZE];
logic [mrh_pkg::RNID_W-1: 0]            w_update_rnid    [mrh_pkg::DISP_SIZE];


generate for (genvar d_idx = 0; d_idx < mrh_pkg::DISP_SIZE; d_idx++) begin : free_loop
  freelist
                             #(
                               .SIZE (mrh_pkg::FLIST_SIZE),
                               .WIDTH ($clog2(mrh_pkg::RNID_SIZE)),
                               .INIT (mrh_pkg::FLIST_SIZE * d_idx + 32)
                               )
  u_freelist
                             (
                              .i_clk     (i_clk ),
                              .i_reset_n (i_reset_n),

                              .i_push(disp.inst[d_idx].rd_valid),
                              .i_push_id(),

                              .i_pop(disp.inst[d_idx].rd_valid),
                              .o_pop_id(rd_id[d_idx])
                              );
end
endgenerate

generate for (genvar d_idx = 0; d_idx < mrh_pkg::DISP_SIZE; d_idx++) begin : src_rd_loop
  assign w_archreg_valid [d_idx*2 + 0] = disp.inst[d_idx].rs1_valid;
  assign w_archreg_valid [d_idx*2 + 1] = disp.inst[d_idx].rs2_valid;

  assign w_archreg [d_idx*2 + 0] = disp.inst[d_idx].rs1_regidx;
  assign w_archreg [d_idx*2 + 1] = disp.inst[d_idx].rs2_regidx;

  assign w_update_arch_id[d_idx] = 'h0;
  assign w_update_rnid   [d_idx] = 'h0;

end
endgenerate

mrh_rename_map u_mrh_rename_map
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_arch_valid (w_archreg_valid),
   .i_arch_id    (w_archreg),
   .o_rnid       (w_rnid),

   .i_update         ({mrh_pkg::DISP_SIZE{1'b0}}),
   .i_update_arch_id (w_update_arch_id),
   .i_update_rnid    (w_update_rnid   )
   );


endmodule // mrh_rename

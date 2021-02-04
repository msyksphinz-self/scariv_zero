module mrh_rename
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.slave disp
   );

logic [$clog2(mrh_pkg::RNID_SIZE)-1: 0] rd_id[mrh_pkg::DISP_SIZE];

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


endmodule // mrh_rename

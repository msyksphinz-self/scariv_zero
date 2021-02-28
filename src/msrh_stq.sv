module msrh_stq
  (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_pkg::DISP_SIZE-1:0] i_disp_valid,
    disp_if.slave                                 disp,

    output msrh_pkg::done_rpt_t                   o_done_report
   );

assign o_done_report.valid   = 1'b0;  // Temporary
assign o_done_report.cmt_id  = 'h0;   // Temporary
assign o_done_report.grp_id  = 'h0;   // Temporary
assign o_done_report.exc_vld = 'h0;   // Temporary

endmodule // msrh_stq

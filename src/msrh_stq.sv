module msrh_stq
  (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_pkg::DISP_SIZE-1:0] i_disp_valid,
    disp_if.slave                                 disp,

    output msrh_pkg::done_rpt_t                   o_done_report
   );

endmodule // msrh_stq

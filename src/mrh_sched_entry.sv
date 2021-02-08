module mrh_sched_entry
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic            i_put,
   input mrh_pkg::disp_t  i_put_data,

   output mrh_pkg::disp_t o_entry
   );

endmodule // mrh_sched_entry

module msrh_rn_map_queue
  import msrh_pkg::*;
  (
   input logic                i_clk,
   input logic                i_reset_n,

   input logic                i_load,
   input logic [RNID_W-1: 0]  i_rn_list[32],

   input logic                i_restore,
   output logic [RNID_W-1: 0] o_rn_list[32],

   output logic               o_full
   );

localparam MAP_QUEUE_SIZE = 8;

logic [$clog2(MAP_QUEUE_SIZE)-1: 0] w_in_ptr;
logic [$clog2(MAP_QUEUE_SIZE)-1: 0] w_out_ptr;

logic [RNID_W * 32 -1 : 0]         w_in_rn_list;
logic [RNID_W * 32 -1 : 0]         w_out_rn_list;

inoutptr #(.SIZE(MAP_QUEUE_SIZE)) u_inoutptr(.i_clk (i_clk), .i_reset_n (i_reset_n), .i_clear (1'b0),
                                             .i_in_vld  (i_load),    .o_in_ptr (w_in_ptr),
                                             .i_out_vld (i_restore), .o_out_ptr(w_out_ptr));

data_array
  #(
    .WIDTH(RNID_W * 32),
    .ADDR_W($clog2(MAP_QUEUE_SIZE))
    )
u_rn_map_array
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr  (i_load),
   .i_addr(i_load ? w_in_ptr : w_out_ptr),

   .o_data(w_out_rn_list),
   .i_be ({(RNID_W * 4){1'b1}}),
   .i_data (w_in_rn_list)
   );

generate for (genvar i = 0; i < 32; i++) begin : extract_loop
  assign w_in_rn_list[i * RNID_W +: RNID_W] = i_rn_list[i];
  assign o_rn_list[i] = w_out_rn_list[i * RNID_W +: RNID_W];
end
endgenerate

endmodule // msrh_rn_map_queue

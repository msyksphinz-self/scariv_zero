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

localparam MAP_QUEUE_SIZE = msrh_conf_pkg::CMT_ENTRY_SIZE;

logic [$clog2(MAP_QUEUE_SIZE)-1: 0] w_in_ptr;
logic [$clog2(MAP_QUEUE_SIZE)-1: 0] w_out_ptr;
logic [RNID_W-1: 0]                 r_rnid_list[MAP_QUEUE_SIZE][32];

logic [RNID_W * 32 -1 : 0]         w_in_rn_list;
logic [RNID_W * 32 -1 : 0]         w_out_rn_list;

inoutptr #(.SIZE(MAP_QUEUE_SIZE)) u_inoutptr(.i_clk (i_clk), .i_reset_n (i_reset_n), .i_clear (1'b0),
                                             .i_in_valid  (i_load),    .o_in_ptr (w_in_ptr),
                                             .i_out_valid (i_restore), .o_out_ptr(w_out_ptr));


always_ff @ (posedge i_clk) begin
  if (i_load) begin
    for(int i =  0; i < 32; i++) begin
      r_rnid_list[w_in_ptr][i] <= i_rn_list[i];
    end
  end
end

generate for (genvar i = 0; i < 32; i++) begin : extract_loop
  assign w_in_rn_list[i * RNID_W +: RNID_W] = i_rn_list[i];
  assign o_rn_list[i] = r_rnid_list[w_out_ptr][i];
end
endgenerate

endmodule // msrh_rn_map_queue

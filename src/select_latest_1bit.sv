module select_latest_1bit
  #(
    parameter SEL_WIDTH = 5,
    parameter KEY_WIDTH = 8
    )
(
 input logic [KEY_WIDTH-1: 0] i_cmp_key,
 input logic [SEL_WIDTH-1:0]  i_valid,
 input logic [KEY_WIDTH-1: 0] i_keys [SEL_WIDTH],
 input logic [SEL_WIDTH-1: 0] i_data,

 output logic                 o_valid,
 output logic                 o_data
 );


logic [0:0]                   w_data[SEL_WIDTH];
generate for (genvar i = 0; i < SEL_WIDTH; i++) begin
  assign w_data[i] = i_data[i];
end
endgenerate


select_latest
  #(
    .SEL_WIDTH(SEL_WIDTH),
    .KEY_WIDTH(KEY_WIDTH),
    .DATA_WIDTH(1)
    )
u_select_latest
  (
   .i_cmp_key (i_cmp_key),
   .i_valid (i_valid),
   .i_keys  (i_keys),
   .i_data  (w_data),

   .o_valid (o_valid),
   .o_data  (o_data)
   );


endmodule // select_latest_1bit

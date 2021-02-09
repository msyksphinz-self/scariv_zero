module select_latest
  #(
    parameter SEL_WIDTH = 5,
    parameter KEY_WIDTH = 8,
    parameter DATA_WIDTH = 32
    )
(
 input logic [KEY_WIDTH-1: 0]   i_cmp_key,
 input logic [SEL_WIDTH-1:0]    i_valid,
 input logic [KEY_WIDTH-1: 0]   i_keys [SEL_WIDTH],
 input logic [DATA_WIDTH-1: 0]  i_data [SEL_WIDTH],

 output logic                   o_valid,
 output logic [DATA_WIDTH-1: 0] o_data
 );


/* verilator lint_off UNOPTFLAT */
logic [DATA_WIDTH-1: 0]        data_tmp[SEL_WIDTH];
logic [SEL_WIDTH-1: 0]         valid_tmp;

assign data_tmp [0] = i_valid[0] && (i_keys[0] == i_cmp_key) ? i_data[0] : 'h0;
assign valid_tmp[0] = i_valid[0] && (i_keys[0] == i_cmp_key);

generate for (genvar i = 1; i < SEL_WIDTH; i++) begin
  always_comb begin
    if (i_valid[i] && i_keys[i] == i_cmp_key) begin
      data_tmp [i] = i_data[i];
      valid_tmp[i] = 1'b1;
    end else begin
      data_tmp [i] = data_tmp[i-1];
      valid_tmp[i] = valid_tmp[i-1];
    end // else: !if(i_valid[i] && i_keys[i] == i_cmp_key)
  end // always_comb
end
endgenerate

assign o_valid = valid_tmp[SEL_WIDTH-1];
assign o_data  = data_tmp [SEL_WIDTH-1];

endmodule // select_latest

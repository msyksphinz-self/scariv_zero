module select_oh #(
    parameter SEL_WIDTH  = 5,
    parameter KEY_WIDTH  = 8,
    parameter DATA_WIDTH = 32
) (
    input logic [KEY_WIDTH-1: 0]   i_cmp_key,
    input logic [SEL_WIDTH-1:0]    i_valid,
    input logic [KEY_WIDTH-1: 0]   i_keys [SEL_WIDTH],
    input logic [DATA_WIDTH-1: 0]  i_data [SEL_WIDTH],

    output logic                   o_valid,
    output logic [DATA_WIDTH-1: 0] o_data
);


  /* verilator lint_off UNOPTFLAT */
  logic [SEL_WIDTH-1:0] valid_tmp;

  generate
    for (genvar i = 0; i < SEL_WIDTH; i++) begin
      always_comb begin
        if (i_valid[i] && i_keys[i] == i_cmp_key) begin
          valid_tmp[i] = 1'b1;
        end else begin
          valid_tmp[i] = 1'b0;
        end
      end  // always_comb
    end
  endgenerate

  bit_oh_or #(
      .WIDTH(DATA_WIDTH),
      .WORDS(SEL_WIDTH)
  ) u_select_oh (
      .i_oh(valid_tmp),
      .i_data(i_data),
      .o_selected(o_data)
  );

  assign o_valid = |valid_tmp;

endmodule  // select_latest

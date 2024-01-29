/*
 * bit_multiple_min
 * Select
 */
module bit_multiple_age_min
  import scariv_pkg::*;
#(
  parameter WORDS=4
  )
(
 input logic [WORDS-1: 0] i_valids,
 input cmt_id_t           i_cmt_id[WORDS],
 input grp_id_t           i_grp_id[WORDS],

 output logic                      o_valid,
 output logic [$clog2(WORDS)-1: 0] o_min_idx
 );

function automatic logic [$clog2(WORDS)-1: 0] find_min_idx();
  logic [$clog2(WORDS)-1: 0] w_min_idx;
  cmt_id_t w_min_cmt_id;
  grp_id_t w_min_grp_id;
  logic                     w_min_valid;

  w_min_idx    = 0;
  w_min_valid  = i_valids[0];
  w_min_cmt_id = i_cmt_id[0];
  w_min_grp_id = i_grp_id[0];

  for (int i = 1; i < WORDS; i++) begin
    if (i_valids[i] & (~w_min_valid | id0_is_older_than_id1(i_cmt_id[i], i_grp_id[i], w_min_cmt_id, w_min_grp_id))) begin
      w_min_cmt_id = i_cmt_id[i];
      w_min_grp_id = i_grp_id[i];
      w_min_idx    = i;
      w_min_valid  = 1'b1;
    end
  end

  return w_min_idx;
endfunction //

assign o_valid = |i_valids;
assign o_min_idx = find_min_idx();

endmodule // bit_multiple_age_min


// if (WORDS == 1) begin
//   assign o_valid = |i_valids;
//
// end else begin : words_larger_2
//   localparam HALF = WORDS/2;
//   logic [HALF-1:0] lo;
//   logic [WORDS-HALF-1:0] hi;
//
//   logic       valid_lo, valid_hi;
//   logic [$clog2(HALF)-1:      0] tmp_lo;
//   logic [$clog2(WORDS-HALF)-1:0] tmp_hi;
//
//
//   bit_multiple_min
//     #(.WORDS(HALF))
//   u_min_lo
//     (
//      .i_valids(i_valids[HALF-1:0    ]), .i_cmt_id(i_cmt_id[HALF-1:0    ]), .i_grp_id(i_grp_id[HALF-1:0    ]),
//      .o_valid(valid_lo), .o_min_idx(tmp_lo)
//      );
//
//   bit_multiple_min
//     #(.WORDS(WORDS-HALF))
//   u_min_hi
//     (
//      .i_valids(i_valids[WORDS-1:HALF]), .i_cmt_id(i_cmt_id[WORDS-1:HALF]), .i_grp_id(i_grp_id[WORDS-1:HALF]),
//      .o_valid(valid_hi), .o_min_idx(tmp_hi)
//      );
//
//   /* verilator lint_off WORDS */
//   assign o_min_idx = ~valid_lo & ~valid_hi ? 'h0 :
//                       valid_lo & ~valid_hi ? tmp_lo :
//                      ~valid_lo &  valid_hi ? tmp_hi :
//                      tmp_lo < tmp_hi ? tmp_lo : tmp_hi;
// end // block: words_larger_2

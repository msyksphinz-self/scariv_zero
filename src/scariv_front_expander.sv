// ------------------------------------------------------------------------
// NAME : scariv_front_expander
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Frontend instruction expander from 16-bit to 32-bit
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_front_expander
  import scariv_pkg::*;
  import scariv_ic_pkg::*;
  import decoder_reg_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,
   input logic i_flush_valid,

   // input instruction from ICache
   input scariv_pkg::inst_buffer_in_t i_f2_inst,
   // output intruction decoded informations
   output scariv_front_pkg::inst_t[scariv_conf_pkg::ICACHE_DATA_W/16-1: 0] o_f2_expand_inst,
   output logic [riscv_pkg::VADDR_W-1:1]                                   o_f2_pc
   );

localparam inst_16b_w = scariv_conf_pkg::ICACHE_DATA_W/16;
localparam inst_32b_w = scariv_conf_pkg::ICACHE_DATA_W/32;

// 127 111  95  79  63  47  31  15  0
// +---+---+---+---+---+---+---+---+
// | 1 | 1 | 0 | 1 | 1 | 0 | 0 | 1 |  w_f2_inst_is_rvc
// +---+---+---+---+---+---+---+---+
//       |
// +---+---+---+---+---+---+---+---+
// | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 1 |  w_f2_inst_16bit_valid
// +---+---+---+---+---+---+---+---+

logic [inst_16b_w-1: 0] w_f2_inst_is_rvc;
// condition of w_f2_inst_16bit_valid[i]:
//   previous 16-bit group is higher poisition of RVI : inst_16bit_valid[i-1] == 1'b0
//   previous 16-bit group is RVC : w_f2_inst_is_rvc[i-1] == 1'b1
/* verilator lint_off UNOPTFLAT */
logic [inst_16b_w-1: 0] w_f2_inst_16bit_valid;
logic                   w_f2_fragmented;
logic                   r_f2_fragmented;
logic [15: 0]           r_f2_fragmented_inst;
logic [riscv_pkg::VADDR_W-1: 1] r_f2_fragmented_pc;

logic [inst_16b_w-1: 0] w_f2_inst_shifted_valid;
logic [scariv_conf_pkg::ICACHE_DATA_W-1: 0] w_f2_inst_shifted;

assign w_f2_inst_shifted_valid = {inst_16b_w{1'b1}} >>  i_f2_inst.pc[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1];
assign w_f2_inst_shifted       = i_f2_inst.inst  >> {i_f2_inst.pc[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1], 4'b0000};
// ---------------------------
// 16-bit instruction decoder
// ---------------------------
logic [31: 0]           w_f2_rvc_expanded_inst[inst_16b_w];
decoder_inst_cat_pkg::inst_cat_t    w_f2_rvc_cat[inst_16b_w];
decoder_inst_cat_pkg::inst_subcat_t w_f2_rvc_subcat[inst_16b_w];
generate for (genvar w_idx = 0; w_idx < inst_16b_w; w_idx++) begin : gen_is_RVC
  logic w_f2_inst_is_rvc_rough;
  assign w_f2_inst_is_rvc_rough = w_f2_inst_shifted[w_idx*16 +: 2] != 2'b11;

  if (w_idx == 0) begin : gen_idx_0
    assign w_f2_inst_16bit_valid[w_idx] = r_f2_fragmented ? 1'b0 : i_f2_inst.valid;
  end else if (w_idx == 1) begin : gen_idx_1
    assign w_f2_inst_16bit_valid[w_idx] = w_f2_inst_shifted_valid[1] &
                                          (r_f2_fragmented | w_f2_inst_is_rvc[0]);
  end else begin : gen_idx_non0
    assign w_f2_inst_16bit_valid[w_idx] = w_f2_inst_shifted_valid[w_idx] &
                                          ~w_f2_inst_16bit_valid[w_idx-1] | w_f2_inst_is_rvc[w_idx-1];
  end

  assign w_f2_inst_is_rvc[w_idx] = w_f2_inst_16bit_valid[w_idx] & w_f2_inst_is_rvc_rough;

  // Generate expanded instruction from RVC
  scariv_rvc_expander
  u_rvc_expander
    (
     .i_rvc_inst (w_f2_inst_shifted[w_idx*16 +: 16]),
     .out_32bit  (w_f2_rvc_expanded_inst[w_idx])
     );
  scariv_rvc_type_detector
  u_rvc_type_detector
    (
     .i_rvc_inst    (w_f2_inst_shifted[w_idx*16 +: 16]),
     .o_inst_cat    (w_f2_rvc_cat     [w_idx]),
     .o_inst_subcat (w_f2_rvc_subcat  [w_idx])
     );
end endgenerate

always_comb begin
  /* verilator lint_off CASEX */
  casex (w_f2_inst_shifted_valid)
    8'b1xxx_xxxx : w_f2_fragmented = ~(~w_f2_inst_16bit_valid[7] | w_f2_inst_is_rvc[7]);
    8'b01xx_xxxx : w_f2_fragmented = ~(~w_f2_inst_16bit_valid[6] | w_f2_inst_is_rvc[6]);
    8'b001x_xxxx : w_f2_fragmented = ~(~w_f2_inst_16bit_valid[5] | w_f2_inst_is_rvc[5]);
    8'b0001_xxxx : w_f2_fragmented = ~(~w_f2_inst_16bit_valid[4] | w_f2_inst_is_rvc[4]);
    8'b0000_1xxx : w_f2_fragmented = ~(~w_f2_inst_16bit_valid[3] | w_f2_inst_is_rvc[3]);
    8'b0000_01xx : w_f2_fragmented = ~(~w_f2_inst_16bit_valid[2] | w_f2_inst_is_rvc[2]);
    8'b0000_001x : w_f2_fragmented = ~(~w_f2_inst_16bit_valid[1] | w_f2_inst_is_rvc[1]);
    8'b0000_0001 : w_f2_fragmented = ~(~w_f2_inst_16bit_valid[0] | w_f2_inst_is_rvc[0]);
    default      : w_f2_fragmented = 1'b0;
  endcase // casex (w_f2_inst_shifted_valid)
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f2_fragmented <= 1'b0;
  end else begin
    if (i_flush_valid) begin
      r_f2_fragmented <= 1'b0;
    end else if (i_f2_inst.valid) begin
      r_f2_fragmented      <= w_f2_fragmented;
      r_f2_fragmented_pc   <= i_f2_inst.pc;
      r_f2_fragmented_inst <= i_f2_inst.inst[scariv_conf_pkg::ICACHE_DATA_W-1 -: 16];
    end
  end
end

// ---------------------------
// 32-bit instruction decoder
// ---------------------------
decoder_inst_cat_pkg::inst_cat_t    w_f2_rvi_cat   [inst_16b_w-1];
decoder_inst_cat_pkg::inst_subcat_t w_f2_rvi_subcat[inst_16b_w-1];
generate for (genvar w_idx = 0; w_idx < inst_16b_w-1; w_idx++) begin : gen_loop_RVI
  logic [31: 0] w_f2_inst_extracted;
  assign w_f2_inst_extracted = (w_idx == 0) & r_f2_fragmented ? {i_f2_inst.inst[15: 0], r_f2_fragmented_inst} :
                               w_f2_inst_shifted[w_idx*16 +: 32];

  decoder_inst_cat
  u_inst_cat
  (
   .inst        (w_f2_inst_extracted    ),
   .inst_cat    (w_f2_rvi_cat    [w_idx]),
   .inst_subcat (w_f2_rvi_subcat [w_idx])
   );
end endgenerate

`define ASSIGN_RVC_RVI(target,index) \
o_f2_expand_inst[target].valid          = i_f2_inst.valid & (w_f2_inst_is_rvc[index] ? w_f2_inst_shifted_valid[index] : &w_f2_inst_shifted_valid[index +: 2]); \
o_f2_expand_inst[target].inst           = w_f2_inst_is_rvc[index] ? w_f2_rvc_expanded_inst[index]       : w_f2_inst_shifted [index*16 +: 32]; \
o_f2_expand_inst[target].fragmented     = 1'b0; \
o_f2_expand_inst[target].cache_pos      = index; \
o_f2_expand_inst[target].rvc_inst_valid = w_f2_inst_is_rvc[index]; \
o_f2_expand_inst[target].rvc_inst       = w_f2_inst_is_rvc[index] ? w_f2_inst_shifted[index*16 +: 16] : w_f2_inst_shifted [index*16 +: 32]; \
o_f2_expand_inst[target].cat            = w_f2_inst_is_rvc[index] ? w_f2_rvc_cat     [index]          : w_f2_rvi_cat   [index]; \
o_f2_expand_inst[target].subcat         = w_f2_inst_is_rvc[index] ? w_f2_rvc_subcat  [index]          : w_f2_rvi_subcat[index];

`define ASSIGN_RVC(target,index) \
o_f2_expand_inst[target].valid          = i_f2_inst.valid & w_f2_inst_shifted_valid[index]; \
o_f2_expand_inst[target].inst           = w_f2_rvc_expanded_inst[index]; \
o_f2_expand_inst[target].fragmented     = 1'b0; \
o_f2_expand_inst[target].cache_pos      = index; \
o_f2_expand_inst[target].rvc_inst_valid = 1'b1; \
o_f2_expand_inst[target].rvc_inst       = w_f2_inst_shifted[index*16 +: 16]; \
o_f2_expand_inst[target].cat            = w_f2_rvc_cat          [index]; \
o_f2_expand_inst[target].subcat         = decoder_inst_cat_pkg::INST_SUBCAT__;

`define ASSIGN_RVI(target,index) \
o_f2_expand_inst[target].valid          = i_f2_inst.valid & w_f2_inst_shifted_valid[index]; \
o_f2_expand_inst[target].inst           = w_f2_inst_shifted [index*16 +: 32]; \
o_f2_expand_inst[target].fragmented     = 1'b0; \
o_f2_expand_inst[target].cache_pos      = index; \
o_f2_expand_inst[target].rvc_inst_valid = 1'b0; \
o_f2_expand_inst[target].cat            = w_f2_rvi_cat   [index]; \
o_f2_expand_inst[target].subcat         = w_f2_rvi_subcat[index];

`define ASSIGN_RVI_FRAGMENTED \
o_f2_expand_inst[0].valid          = i_f2_inst.valid; \
o_f2_expand_inst[0].inst           = {i_f2_inst.inst[15: 0], r_f2_fragmented_inst}; \
o_f2_expand_inst[0].fragmented     = 1'b1; \
o_f2_expand_inst[0].cache_pos      = 0; \
o_f2_expand_inst[0].rvc_inst_valid = 1'b0; \
o_f2_expand_inst[0].cat            = w_f2_rvi_cat   [0]; \
o_f2_expand_inst[0].subcat         = w_f2_rvi_subcat[0];

`define ASSIGN_ZERO(target) \
o_f2_expand_inst[target].valid  = 1'b0; \
o_f2_expand_inst[target].inst   = 'h0; \
o_f2_expand_inst[target].cat    = decoder_inst_cat_pkg::INST_CAT__; \
o_f2_expand_inst[target].subcat = decoder_inst_cat_pkg::INST_SUBCAT__;

logic [$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W)-1: 1] w_icache_pos_edge;
assign w_icache_pos_edge = scariv_lsu_pkg::ICACHE_DATA_B_W-1;

function automatic logic [ 1: 0] countones_2bit(logic [1:0] in);
  return in == 2'b00 ? 0 :
         (in == 2'b10) | (in == 2'b01) ? 1 :
         2;
endfunction // countones_2bit

function automatic logic [ 1: 0] countones_3bit(logic [2:0] in);
  return in[0] + in[1] + in[2];
endfunction // countones_3bit

function automatic logic [ 2: 0] countones_4bit(logic [3:0] in);
  return in[0] + in[1] + in[2] + in[3];
endfunction // countones_4bit

function automatic logic [ 2: 0] countones_5bit(logic [4:0] in);
  return in[0] + in[1] + in[2] + in[3] + in[4];
endfunction // countones_5bit

function automatic logic [ 2: 0] countones_6bit(logic [5:0] in);
  return in[0] + in[1] + in[2] + in[3] + in[4] + in[5];
endfunction // countones_6bit

function automatic logic [ 2: 0] countones_7bit(logic [6:0] in);
  return in[0] + in[1] + in[2] + in[3] + in[4] + in[5] + in[6];
endfunction // countones_7bit


generate if (scariv_conf_pkg::ICACHE_DATA_W == 128) begin : gen_rvc_rvi_selection
  always_comb begin
    if (w_f2_inst_is_rvc[0]) begin
      `ASSIGN_RVC(0, 0);
    end else if (r_f2_fragmented) begin
      `ASSIGN_RVI_FRAGMENTED;
    end else begin
      `ASSIGN_RVI(0, 0);
    end

    if (countones_2bit(w_f2_inst_is_rvc[1:0] | r_f2_fragmented) == 'h0) begin
      `ASSIGN_RVC_RVI(1, 2);
    end else if ((w_f2_inst_is_rvc[0] | r_f2_fragmented) == 'h1) begin // if ($countones(w_f2_inst_is_rvc[1:0]) == 'h0)
      `ASSIGN_RVC_RVI(1, 1);
    end // if ($countones(w_f2_inst_is_rvc[0]) == 'h1)

    if (countones_4bit(w_f2_inst_is_rvc[3:0] | r_f2_fragmented) == 'h0) begin
      `ASSIGN_RVC_RVI(2, 4);
    end else if (countones_3bit(w_f2_inst_is_rvc[2:0] | r_f2_fragmented) == 'h1) begin
      `ASSIGN_RVC_RVI(2, 3);
    end else if (/* countones_2bit(w_f2_inst_is_rvc[1:0] | r_f2_fragmented) == 'h2 */ &(w_f2_inst_is_rvc[1:0] | r_f2_fragmented)) begin
      `ASSIGN_RVC_RVI(2, 2);
    end else begin
      `ASSIGN_ZERO(2);
    end

    if (countones_6bit(w_f2_inst_is_rvc[5:0] | r_f2_fragmented) == 'h0) begin
      `ASSIGN_RVC_RVI(3, 6);
    end else if (countones_5bit(w_f2_inst_is_rvc[4:0] | r_f2_fragmented) == 'h1) begin
      `ASSIGN_RVC_RVI(3, 5);
    end else if (countones_4bit(w_f2_inst_is_rvc[3:0] | r_f2_fragmented) == 'h2) begin
      `ASSIGN_RVC_RVI(3, 4);
    end else if (/* countones_3bit(w_f2_inst_is_rvc[2:0] | r_f2_fragmented) == 'h3 */ &(w_f2_inst_is_rvc[2:0] | r_f2_fragmented)) begin
      `ASSIGN_RVC_RVI(3, 3);
    end else begin
      `ASSIGN_ZERO(3);
    end

    if (countones_7bit(w_f2_inst_is_rvc[6:0] | r_f2_fragmented) == 'h1 && w_f2_inst_is_rvc[7]) begin
      `ASSIGN_RVC (4, 7);
    end else if (countones_6bit(w_f2_inst_is_rvc[5:0] | r_f2_fragmented) == 'h2) begin
      `ASSIGN_RVC_RVI(4, 6);
    end else if (countones_5bit(w_f2_inst_is_rvc[4:0] | r_f2_fragmented) == 'h3) begin
      `ASSIGN_RVC_RVI(4, 5);
    end else if (/* countones_4bit(w_f2_inst_is_rvc[3:0] | r_f2_fragmented) == 'h4 */ &(w_f2_inst_is_rvc[3:0] | r_f2_fragmented)) begin
      `ASSIGN_RVC_RVI(4, 4);
    end else begin
      `ASSIGN_ZERO(4);
    end

    if (countones_7bit(w_f2_inst_is_rvc[6:0] | r_f2_fragmented) == 'h3 && w_f2_inst_is_rvc[7]) begin
      `ASSIGN_RVC(5, 7);
    end else if (countones_6bit(w_f2_inst_is_rvc[5:0] | r_f2_fragmented) == 'h4) begin
      `ASSIGN_RVC_RVI(5, 6);
    end else if (/* countones_5bit(w_f2_inst_is_rvc[4:0] | r_f2_fragmented) == 'h5 */ &(w_f2_inst_is_rvc[4:0] | r_f2_fragmented)) begin
      `ASSIGN_RVC_RVI(5, 5);
    end else begin
      `ASSIGN_ZERO(5);
    end

    if (countones_7bit(w_f2_inst_is_rvc[6:0] | r_f2_fragmented) == 'h5 && w_f2_inst_is_rvc[7]) begin
      `ASSIGN_RVC(6, 7);
    end else if (/* countones_6bit(w_f2_inst_is_rvc[5:0] | r_f2_fragmented) == 'h6 */ &(w_f2_inst_is_rvc[5:0] | r_f2_fragmented)) begin
      `ASSIGN_RVC_RVI(6, 6);
    end else begin
      `ASSIGN_ZERO(6);
    end

    if (/* countones_7bit(w_f2_inst_is_rvc[6:0] | r_f2_fragmented) == 'h7*/ &(w_f2_inst_is_rvc[6:0] | r_f2_fragmented)) begin
      `ASSIGN_RVC (7, 7);
    end else begin
      `ASSIGN_ZERO(7);
    end
  end // always_comb

  assign o_f2_pc         = i_f2_inst.pc;

end else begin // block: gen_rvc_rvi_selection
  always_comb begin
    $fatal ("ICache Block Size %d is not supported now", scariv_lsu_pkg::ICACHE_DATA_B_W);
  end
end endgenerate

endmodule // scariv_front_expander

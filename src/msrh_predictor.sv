module msrh_predictor
  (
   input logic i_clk,
   input logic i_reset_n,

   input msrh_lsu_pkg::ic_resp_t  i_s2_ic_resp,
   input logic                    i_inst_buf_ready,


   output logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] o_ras_idx

   );

typedef enum logic {
  RVC_CALL = 1'b0,
  STD_CALL = 1'b1
} call_size_t;

logic [ICACHE_DATA_B_W/2-1: 0]    w_rvc_call_be;
logic [ICACHE_DATA_B_W/2-1: 0]    w_std_call_be;
logic [ICACHE_DATA_B_W/2-1: 0]    w_call_be;
call_size_t w_call_size_array[ICACHE_DATA_B_W/2];

logic                             w_ras_upd_valid;
logic [ICACHE_DATA_B_W/2-1:0]     w_call_be_lsb;
call_size_t                       selected_call_size;

generate for (genvar c_idx = 0; c_idx < ICACHE_DATA_B_W / 2; c_idx++) begin : call_loop
  logic [15: 0] w_rvc_inst;
  logic         is_rvc_jal;
  logic         is_rvc_jalr;
  logic         rvc_call_be;
  assign w_rvc_inst = i_s2_ic_resp.data[c_idx*16 +: 16];
`ifdef RV32
  assign is_rvc_jal = (w_rvc_inst[1:0] == 2'b01) &
                      (w_rvc_inst[15:13] == 3'b001);
`else // RV32
  assign is_rvc_jal = 'b0;
`endif // RV32
  assign is_rvc_jalr = (w_rvc_inst[1:0] == 2'b10) &
                       (w_rvc_inst[15:12] == 4'b1001) &
                       (w_rvc_inst[11: 7] != 5'h0) &
                       (w_rvc_inst[ 6: 2] == 5'h0);
  assign w_rvc_call_be[c_idx] = is_rvc_jal | is_rvc_jalr;

  logic [31: 0]   w_std_inst;
  logic           is_std_jal;
  logic           is_std_jalr;
  logic           std_call_be;
  assign w_std_inst = i_s2_ic_resp.data[c_idx*16 +: 32];
  assign is_std_jal = (w_std_inst[ 6:0] == 7'b1101111) &
                      (w_std_inst[11:7] == 5'h1);
  assign is_std_jalr = (w_std_inst[ 6: 0] == 7'b1100111) &
                       (w_std_inst[14:12] == 3'b000) &
                       (w_std_inst[11: 7] == 5'h1);
  assign w_std_call_be[c_idx] = is_std_jal | is_std_jalr;

  assign w_call_be[c_idx] = (w_rvc_call_be[c_idx] | w_std_call_be[c_idx]) &
                            i_s2_ic_resp.valid &
                            i_s2_ic_resp.be[c_idx * 2];

  assign w_call_size_array[c_idx] = w_std_call_be[c_idx] ? STD_CALL : RVC_CALL;
end // block: rvc_jal_loop
endgenerate

assign w_ras_upd_valid = |w_call_be;

bit_extract_lsb #(.WIDTH(ICACHE_DATA_B_W/2)) call_be_lsb (.in(w_call_be), .out(w_call_be_lsb));

bit_oh_or #(.T(call_size_t), .WORDS(ICACHE_DATA_B_W/2))
select_call_size (.i_oh(w_call_be_lsb), .i_data(w_call_size_array), .o_selected(selected_call_size));
encoder #(.SIZE(ICACHE_DATA_B_W/2)) sel_encoder (.i_in(w_call_be_lsb), .o_out(w_call_be_enc));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_ras_idx <= 'h0;
  end else begin
    if (w_ras_upd_valid) begin
      o_ras_idx <= o_ras_idx + 'h1;
    end
  end
end

logic [riscv_pkg::PADDR_W-1: 1] ras_next_pc;
assign ras_next_pc = i_s2_ic_resp.addr + w_call_be_enc + selected_call_size == STD_CALL ? 2 : 1;

msrh_pred_ras
u_ras
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .i_wr_valid (w_ras_upd_valid),
   .i_wr_index (o_ras_idx),
   .i_wr_pa    (ras_next_pc),

   .i_rd_valid (),
   .i_rd_index (),
   .o_rd_pa    ()
   );


endmodule // msrh_predictor

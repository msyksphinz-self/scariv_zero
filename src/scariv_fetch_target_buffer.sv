// ------------------------------------------------------------------------
// NAME : scariv_fetch_target_buffer
// TYPE : module
// ------------------------------------------------------------------------
// Fetch Target Buffer :
// It predict next target block in single-cycle
// to provide fast instruction delivery
// "A Scalable Front-End Architecture for Fast Instruction Delivery"
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_fetch_target_buffer
  import scariv_pkg::*;
  import scariv_predict_pkg::*;
  import scariv_lsu_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic   i_f0_valid,
   input vaddr_t i_f0_pc,

   ubtb_search_if.master  f1_ubtb_predict_if,

   br_upd_if.slave br_upd_if
   );

typedef logic [riscv_pkg::VADDR_W-1:0] tag_t;

typedef struct packed {
  tag_t          pc_tag;
  logic          carry;
  logic [ 5: 0]  par_fallthrugh;
  logic [15: 0]  partial_target_vaddr;
  logic [ 1: 0]  branch_type;
  logic          oversize;
  logic [ 1: 0]  meta;
  logic [ 1: 0]  bimodal;
} ftb_entry_t;

localparam FTB_ENTRY_SIZE = 64;
localparam FTB_ENTRY_WAY_SIZE = 4;
localparam FTB_ENTRY_SIZE_PER_WAY = FTB_ENTRY_SIZE / FTB_ENTRY_WAY_SIZE;

logic [$clog2(FTB_ENTRY_SIZE_PER_WAY)-1: 0] w_f0_ftb_index;
assign w_f0_ftb_index = i_f0_pc[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W) +: $clog2(FTB_ENTRY_SIZE_PER_WAY)];

ftb_entry_t r_ftb_entries[FTB_ENTRY_SIZE_PER_WAY][FTB_ENTRY_WAY_SIZE];

ftb_entry_t w_f0_ftb_target_entries[FTB_ENTRY_WAY_SIZE];
logic [FTB_ENTRY_WAY_SIZE-1: 0]                 w_f0_tag_hit;
logic [FTB_ENTRY_WAY_SIZE-1: 0]                 w_f0_tag_taken;
logic [FTB_ENTRY_WAY_SIZE-1: 0]                 w_f0_tag_selected_oh;
ftb_entry_t w_f0_ftb_way_sel_entry;

generate for (genvar w_idx = 0; w_idx < FTB_ENTRY_WAY_SIZE; w_idx++) begin : f0_index_loop
  assign w_f0_ftb_target_entries[w_idx] = r_ftb_entries[w_f0_ftb_index][w_idx];

  assign w_f0_tag_hit[w_idx] = (w_f0_ftb_target_entries[w_idx].pc_tag[riscv_pkg::VADDR_W-1:$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)] ==
                                i_f0_pc                              [riscv_pkg::VADDR_W-1:$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)]) &
                               (w_f0_ftb_target_entries[w_idx].pc_tag[$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)-1: 0] >
                                i_f0_pc                              [$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)-1: 0]);
  assign w_f0_tag_taken[w_idx] = w_f0_tag_hit[w_idx] & w_f0_ftb_target_entries[w_idx].bimodal[1];
end endgenerate

bit_extract_lsb #(.WIDTH(FTB_ENTRY_WAY_SIZE)) u_f0_tag_hit_oh (.in(w_f0_tag_taken == 'h0 ? w_f0_tag_hit : w_f0_tag_taken), .out(w_f0_tag_selected_oh));
bit_oh_or #(.T(ftb_entry_t), .WORDS(FTB_ENTRY_WAY_SIZE)) f0_way_selected_entry(.i_oh(w_f0_tag_selected_oh), .i_data(w_f0_ftb_target_entries), .o_selected(w_f0_ftb_way_sel_entry));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    f1_ubtb_predict_if.predict_valid <= 1'b0;
  end else begin
    f1_ubtb_predict_if.predict_valid          <= |w_f0_tag_hit & i_f0_valid;
    f1_ubtb_predict_if.ubtb_info.taken        <= w_f0_ftb_way_sel_entry.bimodal[1];
    // f1_ubtb_predict_if.ubtb_info.pc_offset    <= w_f0_ftb_way_sel_entry.pc_tag[$clog2(FTB_ENTRY_SIZE_PER_WAY)-1: 0];
    f1_ubtb_predict_if.ubtb_info.pc_offset    <= w_f0_ftb_way_sel_entry.pc_tag[$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)-1: 0];
    f1_ubtb_predict_if.ubtb_info.target_vaddr <= {i_f0_pc[riscv_pkg::VADDR_W-1: 16], w_f0_ftb_way_sel_entry.partial_target_vaddr[15: 0]};
    // f1_ubtb_predict_if.bimodal      <= w_f0_ftb_way_sel_entry.bimodal;

// `ifdef SIMULATION
//     if (!$onehot0(w_f0_tag_hit)) begin
//       $fatal(0, "w_f0_tag_hit should be one-hot. Actually %b\n", w_f0_tag_hit);
//     end
// `endif // SIMULATION
  end
end


// -------
// Update
// -------
logic w_ftb_update_valid;
logic [$clog2(FTB_ENTRY_SIZE_PER_WAY)-1: 0] w_ftb_update_index;
logic [$clog2(FTB_ENTRY_WAY_SIZE)-1: 0]     w_ftb_update_way;
assign w_ftb_update_valid = br_upd_if.update & !br_upd_if.dead & ~(br_upd_if.is_call | br_upd_if.is_ret);
assign w_ftb_update_index = br_upd_if.basicblk_pc_vaddr[$clog2(scariv_lsu_pkg::ICACHE_DATA_B_W) +: $clog2(FTB_ENTRY_SIZE_PER_WAY)];
assign w_ftb_update_way = br_upd_if.pc_vaddr[2 +: $clog2(FTB_ENTRY_SIZE_PER_WAY)];
ftb_entry_t w_ftb_update_entry;
assign w_ftb_update_entry.partial_target_vaddr = br_upd_if.target_vaddr[15: 0];
scariv_pkg::vaddr_t pc_vaddr_b1;
assign pc_vaddr_b1 = br_upd_if.pc_vaddr + (br_upd_if.is_rvc ? 'h0 : 'h2);
assign w_ftb_update_entry.pc_tag               = pc_vaddr_b1;
assign w_ftb_update_entry.bimodal              = (((br_upd_if.bim_value == 2'b11) & !br_upd_if.mispredict &  br_upd_if.taken |
                                                   (br_upd_if.bim_value == 2'b00) & !br_upd_if.mispredict & !br_upd_if.taken)) ? br_upd_if.bim_value :
                                                 br_upd_if.taken ? br_upd_if.bim_value + 2'b01 :
                                                 br_upd_if.bim_value - 2'b01;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (w_ftb_update_valid) begin
    r_ftb_entries[w_ftb_update_index][w_ftb_update_way] <= w_ftb_update_entry;
  end
end


`ifdef SIMULATION

ftb_entry_t sim_ftb_entries_way0[FTB_ENTRY_SIZE_PER_WAY-1: 0];
generate for (genvar idx = 0; idx < FTB_ENTRY_SIZE_PER_WAY; idx++) begin
  assign sim_ftb_entries_way0[idx] = r_ftb_entries[idx][0];
end endgenerate

ftb_entry_t sim_ftb_entries_way1[FTB_ENTRY_SIZE_PER_WAY-1: 0];
generate for (genvar idx = 0; idx < FTB_ENTRY_SIZE_PER_WAY; idx++) begin
  assign sim_ftb_entries_way1[idx] = r_ftb_entries[idx][1];
end endgenerate

ftb_entry_t sim_ftb_entries_way2[FTB_ENTRY_SIZE_PER_WAY-1: 0];
generate for (genvar idx = 0; idx < FTB_ENTRY_SIZE_PER_WAY; idx++) begin
  assign sim_ftb_entries_way2[idx] = r_ftb_entries[idx][2];
end endgenerate

ftb_entry_t sim_ftb_entries_way3[FTB_ENTRY_SIZE_PER_WAY-1: 0];
generate for (genvar idx = 0; idx < FTB_ENTRY_SIZE_PER_WAY; idx++) begin
  assign sim_ftb_entries_way3[idx] = r_ftb_entries[idx][3];
end endgenerate

`endif // SIMULATION

endmodule // scariv_fetch_target_buffer

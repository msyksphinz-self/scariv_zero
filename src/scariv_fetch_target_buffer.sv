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

   output logic         o_f1_predict_valid,
   output logic         o_f1_predict_taken,
   output vaddr_t       o_f1_predict_target_vaddr,
   output logic [ 1: 0] o_f1_predict_bimodal,

   br_upd_if.slave br_upd_if
   );

typedef logic [riscv_pkg::VADDR_W-1:$clog2(FTB_ENTRY_SIZE_PER_WAY)] tag_t;

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
assign w_f0_ftb_index = i_f0_pc[1 +: $clog2(FTB_ENTRY_SIZE_PER_WAY)];

ftb_entry_t r_ftb_entries[FTB_ENTRY_SIZE_PER_WAY][FTB_ENTRY_WAY_SIZE];

ftb_entry_t w_f0_ftb_target_entries[FTB_ENTRY_WAY_SIZE];
logic [FTB_ENTRY_WAY_SIZE-1: 0]                 w_f0_tag_hit;
ftb_entry_t w_f0_ftb_way_sel_entry;

generate for (genvar w_idx = 0; w_idx < FTB_ENTRY_WAY_SIZE; w_idx++) begin : f0_index_loop
  assign w_f0_ftb_target_entries[w_idx] = r_ftb_entries[w_f0_ftb_index][w_idx];

  assign w_f0_tag_hit[w_idx] = w_f0_ftb_target_entries[w_idx].pc_tag == i_f0_pc[riscv_pkg::VADDR_W-1:$clog2(FTB_ENTRY_SIZE_PER_WAY)];
end endgenerate

bit_oh_or #(.T(ftb_entry_t), .WORDS(FTB_ENTRY_WAY_SIZE)) f0_way_selected_entry(.i_oh(w_f0_tag_hit), .i_data(w_f0_ftb_target_entries), .o_selected(w_f0_ftb_way_sel_entry));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_f1_predict_valid <= 1'b0;
  end else begin
    o_f1_predict_valid        <= |w_f0_tag_hit & i_f0_valid &
                                 (w_f0_ftb_way_sel_entry.pc_tag == i_f0_pc[riscv_pkg::VADDR_W-1:$clog2(FTB_ENTRY_SIZE_PER_WAY)]);
    o_f1_predict_taken        <= w_f0_ftb_way_sel_entry.bimodal[1];
    o_f1_predict_target_vaddr <= {i_f0_pc[riscv_pkg::VADDR_W-1: 16], w_f0_ftb_way_sel_entry.partial_target_vaddr[15: 0]};
    o_f1_predict_bimodal      <= w_f0_ftb_way_sel_entry.bimodal;
  end
end


// -------
// Update
// -------
logic w_ftb_update_valid;
logic [$clog2(FTB_ENTRY_SIZE_PER_WAY)-1: 0] w_ftb_update_index;
logic [$clog2(FTB_ENTRY_WAY_SIZE)-1: 0]     w_ftb_update_way;
assign w_ftb_update_valid = br_upd_if.update & !br_upd_if.dead & ~(br_upd_if.is_call | br_upd_if.is_ret);
assign w_ftb_update_index = br_upd_if.basicblk_pc_vaddr[1 +: $clog2(FTB_ENTRY_SIZE_PER_WAY)];
assign w_ftb_update_way = br_upd_if.pc_vaddr[1 +: $clog2(FTB_ENTRY_SIZE_PER_WAY)];
ftb_entry_t w_ftb_update_entry;
assign w_ftb_update_entry.partial_target_vaddr = br_upd_if.target_vaddr[15: 0];
assign w_ftb_update_entry.pc_tag               = br_upd_if.basicblk_pc_vaddr[riscv_pkg::VADDR_W-1:$clog2(FTB_ENTRY_SIZE_PER_WAY)];
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

`endif // SIMULATION

endmodule // scariv_fetch_target_buffer

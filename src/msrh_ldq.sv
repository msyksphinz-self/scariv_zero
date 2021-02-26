module msrh_ldq
  (
   input logic                           i_clk,
   input logic                           i_reset_n,

   input logic [msrh_pkg::DISP_SIZE-1:0] i_disp_valid,
                                         disp_if.slave disp,

   // Updates from LSU Pipeline EX1 stage
   input msrh_lsu_pkg::ex1_q_update_t        i_ex1_q_updates[msrh_pkg::LSU_INST_NUM],
   input logic [msrh_pkg::LSU_INST_NUM-1: 0] i_tlb_resolve,
   input msrh_lsu_pkg::ex2_q_update_t        i_ex2_q_updates[msrh_pkg::LSU_INST_NUM],

   input msrh_lsu_pkg::lrq_resolve_t     i_lrq_resolve,
   output                                msrh_pkg::done_rpt_t o_done_report
   );

typedef enum logic[2:0] { INIT = 0, RUN = 1, LRQ_HAZ = 2, STQ_HAZ = 3, TLB_HAZ = 4 } state_t;

typedef struct packed {
logic          is_valid;
logic          is_active;
logic [msrh_pkg::CMT_BLK_W-1:0] cmt_id;
logic [msrh_pkg::DISP_SIZE-1:0] grp_id;
  state_t state;
logic [riscv_pkg::VADDR_W-1: 0] vaddr;

} ldq_entry_t;

function ldq_entry_t assign_ldq_disp (msrh_pkg::disp_t in,
                                      logic [msrh_pkg::CMT_BLK_W-1: 0] cmt_id,
                                      logic [msrh_pkg::DISP_SIZE-1: 0] grp_id);
  ldq_entry_t ret;

  ret.is_valid  = 1'b1;
  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;
  ret.state     = INIT;
  ret.vaddr     = 'h0;
  ret.is_active = 1'b0;

  return ret;
endfunction // assign_ldq_disp


ldq_entry_t r_ldq_entries[msrh_lsu_pkg::LDQ_SIZE];

msrh_pkg::disp_t disp_picked_inst[msrh_pkg::MEM_DISP_SIZE];
logic [msrh_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
logic [msrh_pkg::DISP_SIZE-1:0] disp_picked_grp_id[msrh_pkg::MEM_DISP_SIZE];

msrh_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(msrh_pkg::MEM_DISP_SIZE)
    )
u_msrh_disp_pickup
  (
   .i_disp_valid (i_disp_valid),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

//
// LDQ Pointer
//
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_in_ptr;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_out_ptr;
logic                                        w_in_vld;
logic                                        w_out_vld;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1:0]         w_load_valid;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_disp_picked_num;

assign w_in_vld  = |disp_picked_inst_valid;
assign w_out_vld = o_done_report.valid;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(msrh_pkg::LRQ_ENTRY_SIZE)) cnt_disp_vld(.in({{(msrh_pkg::LRQ_ENTRY_SIZE-msrh_pkg::MEM_DISP_SIZE){1'b0}}, disp_picked_inst_valid}), .out(w_disp_picked_num));
inoutptr_var #(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                          .i_in_vld (w_in_vld ), .i_in_val (w_disp_picked_num), .o_in_ptr (w_in_ptr ),
                                                          .i_out_vld(w_out_vld), .i_out_val('h0), .o_out_ptr(w_out_ptr));

generate for (genvar l_idx = 0; l_idx < msrh_lsu_pkg::LDQ_SIZE; l_idx++) begin : ldq_loop
  logic [msrh_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  msrh_pkg::disp_t           w_disp_entry;
  logic [msrh_pkg::DISP_SIZE-1: 0] w_disp_grp_id;
  for (genvar i_idx = 0; i_idx < msrh_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    assign w_input_valid[i_idx] = disp_picked_inst_valid[i_idx] & (w_in_ptr + i_idx == l_idx);
  end

  bit_oh_or #(.WIDTH($size(msrh_pkg::disp_t)), .WORDS(msrh_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(disp_picked_inst),   .o_selected(w_disp_entry));
  bit_oh_or #(.WIDTH(msrh_pkg::DISP_SIZE),     .WORDS(msrh_pkg::MEM_DISP_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(disp_picked_grp_id), .o_selected(w_disp_grp_id));

  // Selection of EX1 Update signal
  msrh_lsu_pkg::ex1_q_update_t w_ex1_q_updates;
  logic w_ex1_q_valid;
  ex1_update_select u_ex1_update_select (.i_ex1_q_updates(i_ex1_q_updates), .cmt_id(r_ldq_entries[l_idx].cmt_id), .grp_id(r_ldq_entries[l_idx].grp_id),
                                         .o_ex1_q_valid(w_ex1_q_valid), .o_ex1_q_updates(w_ex1_q_updates));

  // Selection of EX1 Update signal
  msrh_lsu_pkg::ex2_q_update_t w_ex2_q_updates;
  logic w_ex2_q_valid;
  ex2_update_select u_ex2_update_select (.i_ex2_q_updates(i_ex2_q_updates), .ldq_index(l_idx[$clog2(msrh_lsu_pkg::LDQ_SIZE)-1:0]), .o_ex2_q_valid(w_ex2_q_valid), .o_ex2_q_updates(w_ex2_q_updates));

  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] r_lrq_hazard_index;

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ldq_entries[l_idx].state <= INIT;
      r_lrq_hazard_index <= 'h0;
    end else begin
      case (r_ldq_entries[l_idx].state)
        INIT :
          if (w_in_vld) begin
            r_ldq_entries[l_idx] <= assign_ldq_disp(w_disp_entry, disp.cmt_id, w_disp_grp_id);
          end else if (w_ex1_q_valid) begin
            r_ldq_entries[l_idx].state <= w_ex1_q_updates.hazard_vld ? TLB_HAZ : RUN;
            r_ldq_entries[l_idx].vaddr <= w_ex1_q_updates.vaddr;
          end
        TLB_HAZ : begin
          if (|i_tlb_resolve) begin
            r_ldq_entries[l_idx].state <= RUN;
          end
        end
        RUN : begin
          if (w_ex2_q_valid) begin
            r_ldq_entries[l_idx].state <= (w_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_CONFLICT ||
                                           w_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_FULL     ||
                                           w_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_ASSIGNED) ? LRQ_HAZ :
                                          INIT;
            r_lrq_hazard_index <= w_ex2_q_updates.lrq_index_oh;
          end
        end
        LRQ_HAZ : begin
          if (i_lrq_resolve.valid && i_lrq_resolve.resolve_index == r_lrq_hazard_index) begin
            r_ldq_entries[l_idx].state <= RUN;
          end
        end
      endcase // case (r_ldq_entries[l_idx].state)
    end
  end

end
endgenerate

endmodule // msrh_ldq

module ex1_update_select
  (
   input                                  msrh_lsu_pkg::ex1_q_update_t i_ex1_q_updates[msrh_pkg::LSU_INST_NUM],
   input logic [msrh_pkg::CMT_BLK_W-1: 0] cmt_id,
   input logic [msrh_pkg::DISP_SIZE-1: 0] grp_id,
   output                                 o_ex1_q_valid,
   output                                 msrh_lsu_pkg::ex1_q_update_t o_ex1_q_updates
   );

logic [msrh_pkg::LSU_INST_NUM-1: 0] w_ex1_update_match;

for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : ex1_update_loop
  assign w_ex1_update_match[p_idx] = i_ex1_q_updates[p_idx].update &&
                                     i_ex1_q_updates[p_idx].cmt_id == cmt_id &&
                                     i_ex1_q_updates[p_idx].grp_id == grp_id;
end

assign o_ex1_q_valid = |w_ex1_update_match;
bit_oh_or #(.WIDTH($size(msrh_lsu_pkg::ex1_q_update_t)), .WORDS(msrh_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(w_ex1_update_match), .i_data(i_ex1_q_updates), .o_selected(o_ex1_q_updates));

endmodule // ex1_update_select


module ex2_update_select
  (
   input                                             msrh_lsu_pkg::ex2_q_update_t i_ex2_q_updates[msrh_pkg::LSU_INST_NUM],
   input logic [$clog2(msrh_lsu_pkg::LDQ_SIZE)-1: 0] ldq_index,
   output                                            o_ex2_q_valid,
   output                                            msrh_lsu_pkg::ex2_q_update_t o_ex2_q_updates
   );

logic [msrh_pkg::LSU_INST_NUM-1: 0] w_ex2_update_match;

for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : ex2_update_loop
  assign w_ex2_update_match[p_idx] = i_ex2_q_updates[p_idx].update &&
                                     i_ex2_q_updates[p_idx].index == ldq_index;
end

assign o_ex2_q_valid = |w_ex2_update_match;
bit_oh_or #(.WIDTH($size(msrh_lsu_pkg::ex2_q_update_t)), .WORDS(msrh_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(w_ex2_update_match), .i_data(i_ex2_q_updates), .o_selected(o_ex2_q_updates));

endmodule // ex2_update_select

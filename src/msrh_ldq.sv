module msrh_ldq
  (
   input logic                           i_clk,
   input logic                           i_reset_n,

   input logic [msrh_pkg::DISP_SIZE-1:0] i_disp_valid,
   disp_if.slave disp,

   // Updates from LSU Pipeline EX1 stage
   input msrh_lsu_pkg::ex1_q_update_t        i_ex1_q_updates[msrh_pkg::LSU_INST_NUM],
   // Updates from LSU Pipeline EX2 stage
   input logic [msrh_pkg::LSU_INST_NUM-1: 0] i_tlb_resolve,
   input msrh_lsu_pkg::ex2_q_update_t        i_ex2_q_updates[msrh_pkg::LSU_INST_NUM],

   output logic [msrh_pkg::LSU_INST_NUM-1: 0] o_ldq_replay_valid,
   output msrh_pkg::issue_t                   o_ldq_replay_issue [msrh_pkg::LSU_INST_NUM],
   output logic [msrh_lsu_pkg::LDQ_SIZE-1: 0] o_ldq_replay_index_oh[msrh_pkg::LSU_INST_NUM],

   input msrh_lsu_pkg::lrq_resolve_t     i_lrq_resolve,

   input logic [msrh_pkg::LSU_INST_NUM-1: 0] i_ex3_done,

   output                                msrh_pkg::done_rpt_t o_done_report
   );

typedef enum logic[2:0] { INIT = 0, EX2_RUN = 1, LRQ_HAZ = 2, STQ_HAZ = 3, TLB_HAZ = 4, READY = 5, EX3_DONE = 6 } state_t;

typedef struct packed {
  logic          is_valid;
  logic [msrh_pkg::LSU_INST_NUM-1: 0]  pipe_sel_idx_oh;
  msrh_pkg::issue_t inst;
  logic [msrh_pkg::CMT_BLK_W-1:0] cmt_id;
  logic [msrh_pkg::DISP_SIZE-1:0] grp_id;
  state_t state;
  logic [riscv_pkg::VADDR_W-1: 0] vaddr;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_haz_index_oh;
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

  return ret;
endfunction // assign_ldq_disp


ldq_entry_t r_ldq_entries[msrh_lsu_pkg::LDQ_SIZE];

msrh_pkg::disp_t disp_picked_inst[msrh_conf_pkg::MEM_DISP_SIZE];
logic [msrh_conf_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
logic [msrh_pkg::DISP_SIZE-1:0] disp_picked_grp_id[msrh_conf_pkg::MEM_DISP_SIZE];

logic [msrh_lsu_pkg::LDQ_SIZE-1: 0] w_rerun_request[msrh_pkg::LSU_INST_NUM];
logic [msrh_lsu_pkg::LDQ_SIZE-1: 0] w_rerun_request_oh[msrh_pkg::LSU_INST_NUM];
logic [msrh_pkg::LSU_INST_NUM-1: 0] w_rerun_request_rev_oh[msrh_lsu_pkg::LDQ_SIZE] ;

//
// Done Selection
//
ldq_entry_t w_ldq_done_entry;
logic [msrh_lsu_pkg::LDQ_SIZE-1:0]  w_ldq_done_oh;

msrh_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(msrh_conf_pkg::MEM_DISP_SIZE)
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
logic [$clog2(msrh_lsu_pkg::LDQ_SIZE)-1:0] w_in_ptr;
logic [$clog2(msrh_lsu_pkg::LDQ_SIZE)-1:0] w_out_ptr;
logic                                        w_in_vld;
logic                                        w_out_vld;
logic [msrh_lsu_pkg::LDQ_SIZE-1:0]         w_load_valid;
logic [$clog2(msrh_lsu_pkg::LDQ_SIZE):0]   w_disp_picked_num;

assign w_in_vld  = |disp_picked_inst_valid;
assign w_out_vld = o_done_report.valid;

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(msrh_lsu_pkg::LDQ_SIZE)) cnt_disp_vld(.in({{(msrh_lsu_pkg::LDQ_SIZE-msrh_conf_pkg::MEM_DISP_SIZE){1'b0}}, disp_picked_inst_valid}), .out(w_disp_picked_num));
inoutptr_var #(.SIZE(msrh_lsu_pkg::LDQ_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                        .i_in_vld (w_in_vld ), .i_in_val (w_disp_picked_num[$clog2(msrh_lsu_pkg::LDQ_SIZE)-1: 0]), .o_in_ptr (w_in_ptr ),
                                                        .i_out_vld(w_out_vld), .i_out_val('h1), .o_out_ptr(w_out_ptr));

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (w_disp_picked_num[$clog2(msrh_lsu_pkg::LDQ_SIZE)]) begin
      $fatal("w_disp_picked_num MSB == 1, too much requests inserted\n");
    end
  end
end
`endif // SIMULATION

generate for (genvar l_idx = 0; l_idx < msrh_lsu_pkg::LDQ_SIZE; l_idx++) begin : ldq_loop
  logic [msrh_conf_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  msrh_pkg::disp_t           w_disp_entry;
  logic [msrh_pkg::DISP_SIZE-1: 0] w_disp_grp_id;
  logic [msrh_pkg::LSU_INST_NUM-1: 0] r_ex2_ldq_entries_recv;
  logic                               w_lrq_is_hazard;
  logic                               w_lrq_is_assigned;
  logic                               w_lrq_resolve_match;
  assign w_lrq_is_hazard = w_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_CONFLICT ||
                           w_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_FULL;
  assign w_lrq_is_assigned = w_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_ASSIGNED;
  assign w_lrq_resolve_match = w_ex2_q_updates.hazard_typ == msrh_lsu_pkg::LRQ_CONFLICT &
                               i_lrq_resolve.valid &
                               (i_lrq_resolve.resolve_index_oh == w_ex2_q_updates.lrq_index_oh);

  for (genvar i_idx = 0; i_idx < msrh_conf_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    assign w_input_valid[i_idx] = disp_picked_inst_valid[i_idx] & (w_in_ptr + i_idx == l_idx);
  end

  bit_oh_or #(.WIDTH($size(msrh_pkg::disp_t)), .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(disp_picked_inst),   .o_selected(w_disp_entry));
  bit_oh_or #(.WIDTH(msrh_pkg::DISP_SIZE),     .WORDS(msrh_conf_pkg::MEM_DISP_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(disp_picked_grp_id), .o_selected(w_disp_grp_id));

  // Selection of EX1 Update signal
  msrh_lsu_pkg::ex1_q_update_t w_ex1_q_updates;
  logic [msrh_pkg::LSU_INST_NUM-1: 0] w_ex1_q_valid;
  ex1_update_select u_ex1_update_select (.i_ex1_q_updates(i_ex1_q_updates), .cmt_id(r_ldq_entries[l_idx].cmt_id), .grp_id(r_ldq_entries[l_idx].grp_id),
                                         .o_ex1_q_valid(w_ex1_q_valid), .o_ex1_q_updates(w_ex1_q_updates));

  // Selection of EX1 Update signal
  msrh_lsu_pkg::ex2_q_update_t w_ex2_q_updates;
  logic w_ex2_q_valid;
  ex2_update_select u_ex2_update_select (.i_ex2_q_updates(i_ex2_q_updates),
                                         .q_index(l_idx[$clog2(msrh_lsu_pkg::LDQ_SIZE)-1:0]),
                                         .i_ex2_recv(r_ex2_ldq_entries_recv),
                                         .o_ex2_q_valid(w_ex2_q_valid), .o_ex2_q_updates(w_ex2_q_updates));

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ldq_entries[l_idx].is_valid <= 1'b0;
      r_ldq_entries[l_idx].state <= INIT;
      r_ldq_entries[l_idx].lrq_haz_index_oh <= 'h0;
      r_ex2_ldq_entries_recv <= 'h0;
    end else begin
      case (r_ldq_entries[l_idx].state)
        INIT :
          if (|w_input_valid) begin
            r_ldq_entries[l_idx] <= assign_ldq_disp(w_disp_entry, disp.cmt_id, w_disp_grp_id);
          end else if (|w_ex1_q_valid) begin
            r_ldq_entries[l_idx].state           <= w_ex1_q_updates.hazard_vld ? TLB_HAZ : EX2_RUN;
            r_ldq_entries[l_idx].vaddr           <= w_ex1_q_updates.vaddr;
            r_ldq_entries[l_idx].pipe_sel_idx_oh <= w_ex1_q_updates.pipe_sel_idx_oh;
            r_ldq_entries[l_idx].inst            <= w_ex1_q_updates.inst;

            for (int p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
              r_ex2_ldq_entries_recv[p_idx] <= w_ex1_q_valid[p_idx] & !i_ex1_q_updates[p_idx].hazard_vld;
            end
          end
        TLB_HAZ : begin
          if (|i_tlb_resolve) begin
            r_ldq_entries[l_idx].state <= READY;
          end
        end
        EX2_RUN : begin
          if (w_ex2_q_valid) begin
            r_ldq_entries[l_idx].state <= w_ex2_q_updates.hazard_typ == msrh_lsu_pkg::L1D_CONFLICT ? READY :
                                          w_lrq_resolve_match ? READY :
                                          w_lrq_is_hazard ? LRQ_HAZ :
                                          w_lrq_is_assigned ? READY : // When LRQ Assigned, LRQ index return is zero so rerun and ge LRQ index.
                                          EX3_DONE;
            r_ldq_entries[l_idx].lrq_haz_index_oh <= w_ex2_q_updates.lrq_index_oh;
`ifdef SIMULATION
            if (!i_reset_n) begin
            end else begin
              if (w_lrq_is_assigned & w_ex2_q_updates.lrq_index_oh != 0) begin
                $fatal ("When LRQ is assigned, LRQ index ID must be zero\n");
              end
              if (w_lrq_is_hazard & !$onehot0(w_ex2_q_updates.lrq_index_oh)) begin
                $fatal ("lrq_index_oh must be one hot but actually %x\n", w_ex2_q_updates.lrq_index_oh);
              end
            end
`endif // SIMULATION
            r_ex2_ldq_entries_recv     <= 'h0;
          end
        end
        LRQ_HAZ : begin
          if (i_lrq_resolve.valid && i_lrq_resolve.resolve_index_oh == r_ldq_entries[l_idx].lrq_haz_index_oh) begin
            r_ldq_entries[l_idx].state <= READY;
          end
        end
        READY : begin
          if (|w_rerun_request_rev_oh[l_idx]) begin
            r_ldq_entries[l_idx].state <= INIT;
          end
        end
        STQ_HAZ : begin
        end
        EX3_DONE : begin
          if (w_ldq_done_oh[l_idx]) begin
            r_ldq_entries[l_idx].is_valid <= 1'b0;
            r_ldq_entries[l_idx].state <= INIT;
          end
        end
        default : begin
          $fatal ("This state sholudn't be reached.\n");
        end
      endcase // case (r_ldq_entries[l_idx].state)
    end
  end

  for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
    assign w_rerun_request[p_idx][l_idx] = r_ldq_entries[l_idx].state == READY &&
                                           r_ldq_entries[l_idx].pipe_sel_idx_oh[p_idx];
  end
end
endgenerate

// replay logic
generate for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
  assign o_ldq_replay_valid[p_idx] = |w_rerun_request[p_idx];
  ldq_entry_t w_ldq_replay_entry;

  bit_extract_lsb #(.WIDTH(msrh_lsu_pkg::LDQ_SIZE)) u_bit_req_sel (.in(w_rerun_request[p_idx]), .out(w_rerun_request_oh[p_idx]));
  bit_oh_or #(.WIDTH($size(ldq_entry_t)), .WORDS(msrh_lsu_pkg::LDQ_SIZE)) select_rerun_oh  (.i_oh(w_rerun_request_oh[p_idx]), .i_data(r_ldq_entries), .o_selected(w_ldq_replay_entry));

  assign o_ldq_replay_issue[p_idx] = w_ldq_replay_entry.inst;

  assign o_ldq_replay_index_oh[p_idx] = w_rerun_request_oh[p_idx];

  for (genvar l_idx = 0; l_idx < msrh_lsu_pkg::LDQ_SIZE; l_idx++) begin : ldq_loop
    assign w_rerun_request_rev_oh[l_idx][p_idx] = w_rerun_request_oh[p_idx][l_idx];
  end
end
endgenerate

// ===============
// done logic
// ===============
generate for (genvar l_idx = 0; l_idx < msrh_lsu_pkg::LDQ_SIZE; l_idx++) begin : done_loop
  assign w_ldq_done_oh[l_idx] = r_ldq_entries[l_idx].state == EX3_DONE && (w_out_ptr == l_idx);
end
endgenerate
bit_oh_or #(.WIDTH($size(ldq_entry_t)), .WORDS(msrh_lsu_pkg::LDQ_SIZE)) select_rerun_oh  (.i_oh(w_ldq_done_oh), .i_data(r_ldq_entries), .o_selected(w_ldq_done_entry));

assign o_done_report.valid   = |w_ldq_done_oh;
assign o_done_report.cmt_id  = w_ldq_done_entry.cmt_id;
assign o_done_report.grp_id  = w_ldq_done_entry.grp_id;
assign o_done_report.exc_vld = 'h0;   // Temporary

endmodule // msrh_ldq

module ex1_update_select
  (
   input                                  msrh_lsu_pkg::ex1_q_update_t i_ex1_q_updates[msrh_pkg::LSU_INST_NUM],
   input logic [msrh_pkg::CMT_BLK_W-1: 0] cmt_id,
   input logic [msrh_pkg::DISP_SIZE-1: 0] grp_id,
   output [msrh_pkg::LSU_INST_NUM-1: 0]   o_ex1_q_valid,
   output                                 msrh_lsu_pkg::ex1_q_update_t o_ex1_q_updates
   );

logic [msrh_pkg::LSU_INST_NUM-1: 0] w_ex1_update_match;

for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : ex1_update_loop
  assign o_ex1_q_valid[p_idx] = i_ex1_q_updates[p_idx].update &&
                                i_ex1_q_updates[p_idx].cmt_id == cmt_id &&
                                i_ex1_q_updates[p_idx].grp_id == grp_id;
end

bit_oh_or #(.WIDTH($size(msrh_lsu_pkg::ex1_q_update_t)), .WORDS(msrh_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(o_ex1_q_valid), .i_data(i_ex1_q_updates), .o_selected(o_ex1_q_updates));

endmodule // ex1_update_select


module ex2_update_select
  (
   input                                             msrh_lsu_pkg::ex2_q_update_t i_ex2_q_updates[msrh_pkg::LSU_INST_NUM],
   input logic [$clog2(msrh_lsu_pkg::LDQ_SIZE)-1: 0] q_index,
   input logic [msrh_pkg::LSU_INST_NUM-1: 0]         i_ex2_recv,
   output                                            o_ex2_q_valid,
   output                                            msrh_lsu_pkg::ex2_q_update_t o_ex2_q_updates
   );

logic [msrh_pkg::LSU_INST_NUM-1: 0] w_ex2_update_match;

for (genvar p_idx = 0; p_idx < msrh_pkg::LSU_INST_NUM; p_idx++) begin : ex2_update_loop
  assign w_ex2_update_match[p_idx] = (i_ex2_q_updates[p_idx].update &&
                                      i_ex2_q_updates[p_idx].index_oh[q_index]) |
                                     i_ex2_recv[p_idx];
end

assign o_ex2_q_valid = |w_ex2_update_match;
bit_oh_or #(.WIDTH($size(msrh_lsu_pkg::ex2_q_update_t)), .WORDS(msrh_pkg::LSU_INST_NUM)) bit_oh_update (.i_oh(w_ex2_update_match), .i_data(i_ex2_q_updates), .o_selected(o_ex2_q_updates));

endmodule // ex2_update_select

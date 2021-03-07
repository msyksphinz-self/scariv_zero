module msrh_scheduler
  #(
    parameter type_t = msrh_pkg::issue_t,
    parameter ENTRY_SIZE = 32,
    parameter IN_PORT_SIZE = 2
    )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 input logic [IN_PORT_SIZE-1: 0]       i_disp_valid,
 input logic [msrh_pkg::CMT_BLK_W-1:0] i_cmt_id,
 input logic [msrh_pkg::DISP_SIZE-1:0] i_grp_id[IN_PORT_SIZE],
                                       msrh_pkg::disp_t i_disp_info[IN_PORT_SIZE],

 /* Forwarding path */
 input                                 msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],

 output                                msrh_pkg::issue_t o_issue,
 output [ENTRY_SIZE-1:0]               o_iss_index_oh,

 input logic                           i_ex0_rs_conflicted,
 input logic [ENTRY_SIZE-1: 0]         i_ex0_rs_conf_index_oh,

 input logic                           i_pipe_done,
 input logic [ENTRY_SIZE-1:0]          i_done_index,

 output                                msrh_pkg::done_rpt_t o_done_report
 );

logic [ENTRY_SIZE-1:0] w_entry_valid;
logic [ENTRY_SIZE-1:0] w_entry_ready;
logic [ENTRY_SIZE-1:0] w_picked_inst_oh;

type_t w_entry[ENTRY_SIZE];

logic [$clog2(IN_PORT_SIZE): 0] w_input_vld_cnt;
logic [$clog2(ENTRY_SIZE)-1: 0] r_entry_in_ptr;
logic [$clog2(ENTRY_SIZE)-1: 0] r_entry_out_ptr;

logic [ENTRY_SIZE-1:0]          w_entry_done;
logic [msrh_pkg::CMT_BLK_W-1:0] w_entry_cmt_id [ENTRY_SIZE];
logic [msrh_pkg::DISP_SIZE-1:0] w_entry_grp_id [ENTRY_SIZE];

/* verilator lint_off WIDTH */
bit_cnt #(.WIDTH(IN_PORT_SIZE)) u_input_vld_cnt (.in(i_disp_valid), .out(w_input_vld_cnt));
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry_in_ptr <= 'h0;
  end else begin
    if (|i_disp_valid) begin
      r_entry_in_ptr <= r_entry_in_ptr + w_input_vld_cnt; /* verilator lint_off WIDTH */
    end
  end
end


generate for (genvar s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin : entry_loop
  logic [IN_PORT_SIZE-1: 0] w_input_valid;
  msrh_pkg::disp_t           w_disp_entry;
  logic [msrh_pkg::DISP_SIZE-1: 0] w_disp_grp_id;
  for (genvar i_idx = 0; i_idx < IN_PORT_SIZE; i_idx++) begin : in_loop
    assign w_input_valid[i_idx] = i_disp_valid[i_idx] & (r_entry_in_ptr + i_idx == s_idx);
  end

  bit_oh_or #(.WIDTH($size(msrh_pkg::disp_t)), .WORDS(IN_PORT_SIZE)) bit_oh_entry (.i_oh(w_input_valid), .i_data(i_disp_info), .o_selected(w_disp_entry));
  bit_oh_or #(.WIDTH(msrh_pkg::DISP_SIZE), .WORDS(IN_PORT_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(i_grp_id), .o_selected(w_disp_grp_id));

  msrh_sched_entry
    u_sched_entry(
                  .i_clk    (i_clk    ),
                  .i_reset_n(i_reset_n),

                  .i_put      (|w_input_valid),

                  .i_cmt_id   (i_cmt_id  ),
                  .i_grp_id   (w_disp_grp_id  ),
                  .i_put_data (w_disp_entry  ),

                  .o_entry_valid(w_entry_valid[s_idx]),
                  .o_entry_ready(w_entry_ready[s_idx]),
                  .o_entry(w_entry[s_idx]),

                  .i_ex0_rs_conflicted    (i_ex0_rs_conflicted &
                                           i_ex0_rs_conf_index_oh[s_idx]),

                  .i_early_wr(i_early_wr),

                  .i_pipe_done (i_pipe_done & i_done_index[s_idx]),

                  .i_entry_picked (w_picked_inst_oh[s_idx]),
                  .o_entry_done (w_entry_done[s_idx]),
                  .o_cmt_id (w_entry_cmt_id[s_idx]),
                  .o_grp_id (w_entry_grp_id[s_idx])
                  );

end
endgenerate

bit_extract_lsb #(.WIDTH(ENTRY_SIZE)) u_pick_rdy_inst(.in(w_entry_valid & w_entry_ready), .out(w_picked_inst_oh));
bit_oh_or #(.WIDTH($size(type_t)), .WORDS(ENTRY_SIZE)) u_picked_inst (.i_oh(w_picked_inst_oh), .i_data(w_entry), .o_selected(o_issue));
assign o_iss_index_oh = w_picked_inst_oh;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry_out_ptr <= 'h0;
  end else begin
    if (w_entry_ready[r_entry_out_ptr]) begin
      r_entry_out_ptr <= r_entry_out_ptr + 1'b1;
    end
  end
end

bit_oh_or #(.WIDTH(msrh_pkg::CMT_BLK_W), .WORDS(ENTRY_SIZE)) bit_oh_entry  (.i_oh(w_entry_done), .i_data(w_entry_cmt_id), .o_selected(o_done_report.cmt_id));
bit_oh_or #(.WIDTH(msrh_pkg::DISP_SIZE), .WORDS(ENTRY_SIZE)) bit_oh_grp_id (.i_oh(w_entry_done), .i_data(w_entry_grp_id), .o_selected(o_done_report.grp_id));

assign o_done_report.valid = |w_entry_done;
assign o_done_report.exc_vld = 1'b0;

`ifdef SIMULATION
typedef struct packed {
  type_t entry;
  msrh_pkg::sched_state_t state;
} entry_ptr_t;

function void dump_entry_json(int fp, entry_ptr_t entry, int index);

  $fwrite(fp, "    \"msrh_sched_entry[%d]\" : {", index);
  $fwrite(fp, "       valid : \"%d\, ", entry.entry.valid);
  $fwrite(fp, "       pc_addr : \"%d\, ", entry.entry.pc_addr);
  $fwrite(fp, "       inst : \"%d\, ", entry.entry.inst);

  $fwrite(fp, "       cmt_id : \"%d\, ", entry.entry.cmt_id);
  $fwrite(fp, "       grp_id : \"%d\, ", entry.entry.grp_id);

  $fwrite(fp, "       state : \"%s\, ", entry.state == msrh_pkg::INIT ? "INIT" :
                                        entry.state == msrh_pkg::WAIT ? "WAIT" :
                                        entry.state == msrh_pkg::ISSUED ? "ISSUED" :
                                        entry.state == msrh_pkg::DONE ? "DONE" : "x");
  $fwrite(fp, "    }\n");

endfunction // dump_json

entry_ptr_t w_entry_ptr[ENTRY_SIZE];
generate for (genvar s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin : entry_loop_ptr
  assign w_entry_ptr[s_idx].entry = entry_loop[s_idx].u_sched_entry.r_entry;
  assign w_entry_ptr[s_idx].state = entry_loop[s_idx].u_sched_entry.r_state;
end
endgenerate

function void dump_json(int fp, int index);
  $fwrite(fp, "  \"msrh_scheduler[%d]\" : {\n", index);
  for (int s_idx = 0; s_idx < ENTRY_SIZE; s_idx++) begin
    dump_entry_json (fp, w_entry_ptr[s_idx], s_idx);
  end
  $fwrite(fp, "  }\n");
endfunction // dump_json
`endif // SIMULATION

endmodule // msrh_scheduler

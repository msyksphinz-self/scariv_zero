module msrh_lsu_pipe
  #(
    parameter LSU_PIPE_IDX = 0,
    parameter RV_ENTRY_SIZE = 32
    )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 input                                 msrh_pkg::issue_t i_rv0_issue,
 input [RV_ENTRY_SIZE-1: 0]            i_rv0_index_oh,

 output logic                          o_ex0_rs_conflicted,
 output logic [RV_ENTRY_SIZE-1: 0]     o_ex0_rs_conf_index_oh,

 input                                 msrh_pkg:: issue_t i_ex0_replay_issue,
 input [msrh_lsu_pkg::MEM_Q_SIZE-1: 0] i_ex0_replay_index_oh,

 output logic                          o_ex1_tlb_miss_hazard,
 output logic                          o_ex2_l1d_miss_hazard,

                                       regread_if.master ex1_regread_rs1,
                                       regread_if.master ex1_regread_rs2,

 output                                msrh_pkg::early_wr_t o_ex1_early_wr,
 output                                msrh_pkg::phy_wr_t o_ex3_phy_wr,

                                       l1d_rd_if.master ex1_l1d_rd_if,
 output logic                          o_ex2_l1d_mispredicted,

                                       l1d_lrq_if.master l1d_lrq_if,

 // Feedbacks to LDQ / STQ
 output                                msrh_lsu_pkg::ex1_q_update_t o_ex1_q_updates,
 output logic                          o_tlb_resolve,
 output                                msrh_lsu_pkg::ex2_q_update_t o_ex2_q_updates,

 output logic                          o_ex3_done
);

//
// EX0 stage
//
msrh_pkg::issue_t                      r_ex0_rs_issue, w_ex0_issue_next;
logic [msrh_lsu_pkg::MEM_Q_SIZE-1: 0]         r_ex0_rs_index_oh;

// Selected signal
msrh_pkg::issue_t                      w_ex0_issue;
logic [msrh_lsu_pkg::MEM_Q_SIZE-1: 0]  w_ex0_index_oh;

//
// EX1 stage
//
msrh_pkg::issue_t                      r_ex1_issue, w_ex1_issue_next;
logic [msrh_lsu_pkg::MEM_Q_SIZE-1: 0]  r_ex1_index_oh;

logic [riscv_pkg::VADDR_W-1: 0]        w_ex1_vaddr;
msrh_lsu_pkg::tlb_req_t                w_ex1_tlb_req;
msrh_lsu_pkg::tlb_resp_t               w_ex1_tlb_resp;

//
// EX2 stage
//
msrh_pkg::issue_t                     r_ex2_issue, w_ex2_issue_next;
logic [msrh_lsu_pkg::MEM_Q_SIZE-1: 0] r_ex2_index_oh;
logic [riscv_pkg::PADDR_W-1: 0]       r_ex2_paddr;

//
// EX3 stage
//
msrh_pkg::issue_t                  r_ex3_issue, w_ex3_issue_next;
logic [riscv_pkg::XLEN_W-1: 0]     r_ex3_aligned_data;

//
// Pipeline Logic
//
always_comb begin
  w_ex1_issue_next   = w_ex0_issue;

  w_ex2_issue_next       = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & !w_ex1_tlb_resp.miss;

  w_ex3_issue_next       = r_ex2_issue;
  w_ex3_issue_next.valid = r_ex2_issue.valid & ex1_l1d_rd_if.hit;
end


always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex0_rs_issue   <= 'h0;
    r_ex0_rs_index_oh <= 'h0;

    r_ex1_issue   <= 'h0;
    r_ex1_index_oh   <= 'h0;

    r_ex2_issue     <= 'h0;
    r_ex2_index_oh     <= 'h0;
  end else begin
    r_ex0_rs_issue  <= i_rv0_issue;
    r_ex0_rs_index_oh <= i_rv0_index_oh;

    r_ex1_issue     <= w_ex1_issue_next;
    r_ex1_index_oh  <= w_ex0_index_oh;

    r_ex2_issue     <= w_ex2_issue_next;
    r_ex2_index_oh  <= r_ex1_index_oh;

    r_ex3_issue     <= w_ex3_issue_next;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


// TLB
tlb
  #(
    .USING_VM(1'b1)
    )
u_tlb
(
 .i_clk    (i_clk),
 .i_reset_n(i_reset_n),

 .i_tlb_req (w_ex1_tlb_req ),
 .o_tlb_resp(w_ex1_tlb_resp),

 .o_tlb_update(o_tlb_resolve)
 );


//
// EX0 stage pipeline
//
// Pipe selection
assign w_ex0_issue = i_ex0_replay_issue.valid ? i_ex0_replay_issue    : r_ex0_rs_issue;
assign w_ex0_index_oh = i_ex0_replay_issue.valid ? i_ex0_replay_index_oh : 'h0;
assign o_ex0_rs_conflicted    = i_ex0_replay_issue.valid & r_ex0_rs_issue.valid;
assign o_ex0_rs_conf_index_oh = r_ex0_rs_index_oh;

//
// EX1 stage pipeline
//

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rs1_valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rs1_rnid;

assign ex1_regread_rs2.valid = r_ex1_issue.valid & r_ex1_issue.rs2_valid;
assign ex1_regread_rs2.rnid  = r_ex1_issue.rs2_rnid;

assign w_ex1_vaddr = ex1_regread_rs1.data[riscv_pkg::VADDR_W-1:0] + (r_ex1_issue.cat == msrh_pkg::CAT_ST ?
                                                                     {{(riscv_pkg::VADDR_W-12){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:25], r_ex1_issue.inst[11: 7]} :
                                                                     {{(riscv_pkg::VADDR_W-12){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:20]});
assign w_ex1_tlb_req.cmd   = msrh_lsu_pkg::M_XRD;
assign w_ex1_tlb_req.vaddr = w_ex1_vaddr;

assign o_ex1_early_wr.valid   = r_ex1_issue.valid & r_ex1_issue.rd_valid;
assign o_ex1_early_wr.rd_rnid = r_ex1_issue.rd_rnid;
assign o_ex1_early_wr.rd_type = msrh_pkg::GPR;

assign o_ex1_tlb_miss_hazard = 1'b0;

// Interface to EX1 updates
assign o_ex1_q_updates.update     = r_ex1_issue.valid;
assign o_ex1_q_updates.inst       = r_ex1_issue;
assign o_ex1_q_updates.pipe_sel_idx_oh = 1 << LSU_PIPE_IDX;
assign o_ex1_q_updates.cmt_id     = r_ex1_issue.cmt_id;
assign o_ex1_q_updates.grp_id     = r_ex1_issue.grp_id;
assign o_ex1_q_updates.hazard_vld = w_ex1_tlb_resp.miss;
assign o_ex1_q_updates.index_oh   = r_ex1_index_oh;
assign o_ex1_q_updates.vaddr      = w_ex1_vaddr;
assign o_ex1_q_updates.paddr      = ex1_l1d_rd_if.paddr;
assign o_ex1_q_updates.st_data_vld = r_ex1_issue.rs2_ready;
assign o_ex1_q_updates.st_data    = ex1_regread_rs2.data;

// Interface to L1D cache
assign ex1_l1d_rd_if.valid = r_ex1_issue.valid & !w_ex1_tlb_resp.miss;
assign ex1_l1d_rd_if.paddr = {w_ex1_tlb_resp.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)],
                           {$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W){1'b0}}};

//
// EX2 stage pipeline
//
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_paddr <= 'h0;
  end else begin
    r_ex2_paddr <= w_ex1_tlb_resp.paddr;
  end
end

assign o_ex2_l1d_mispredicted = r_ex2_issue.valid & (ex1_l1d_rd_if.miss | ex1_l1d_rd_if.conflict);
assign l1d_lrq_if.load              = o_ex2_l1d_mispredicted;
assign l1d_lrq_if.req_payload.paddr = r_ex2_paddr;

// Interface to EX2 updates
assign o_ex2_q_updates.update     = r_ex2_issue.valid;
assign o_ex2_q_updates.hazard_typ = o_ex2_l1d_mispredicted ?
                                    (ex1_l1d_rd_if.conflict ? msrh_lsu_pkg::L1D_CONFLICT :
                                     l1d_lrq_if.resp_payload.conflict ? msrh_lsu_pkg::LRQ_CONFLICT : msrh_lsu_pkg::LRQ_ASSIGNED) :
                                    msrh_lsu_pkg::NONE;
assign o_ex2_q_updates.lrq_index_oh = l1d_lrq_if.resp_payload.lrq_index_oh;
assign o_ex2_q_updates.index_oh     = r_ex2_index_oh;


//
// EX3 stage pipeline
//
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_aligned_data <= 'h0;
  end else begin
    r_ex3_aligned_data <= ex1_l1d_rd_if.data[{r_ex2_paddr[$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)-1:3], 3'b000, 3'b000} +: riscv_pkg::XLEN_W]; // if size = 8B
  end
end

assign o_ex3_done = r_ex3_issue.valid;

assign o_ex3_phy_wr.valid   = r_ex3_issue.valid & r_ex3_issue.rd_valid;
assign o_ex3_phy_wr.rd_rnid = r_ex3_issue.rd_rnid;
assign o_ex3_phy_wr.rd_type = r_ex3_issue.rd_type;
assign o_ex3_phy_wr.rd_data = r_ex3_aligned_data;


endmodule // msrh_lsu_pipe

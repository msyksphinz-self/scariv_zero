module msrh_lsu_pipe
  import decoder_lsu_ctrl_pkg::*;
  import msrh_lsu_pkg::*;
#(
  parameter LSU_PIPE_IDX = 0,
  parameter RV_ENTRY_SIZE = 32
  )
(
 input logic                           i_clk,
 input logic                           i_reset_n,

 /* CSR information */
 csr_info_if.slave                     csr_info,
 /* SFENCE update information */
 sfence_if.slave                       sfence_if,

 input msrh_pkg::issue_t               i_rv0_issue,
 input [RV_ENTRY_SIZE-1: 0]            i_rv0_index_oh,

 input msrh_pkg::mispred_t             i_mispred_lsu[msrh_conf_pkg::LSU_INST_NUM],

 output logic                          o_ex0_rs_conflicted,
 output logic [RV_ENTRY_SIZE-1: 0]     o_ex0_rs_conf_index_oh,

 input msrh_pkg:: issue_t              i_ex0_replay_issue,
 input [MEM_Q_SIZE-1: 0]               i_ex0_replay_index_oh,

 output logic                          o_ex1_tlb_miss_hazard,
 output logic                          o_ex2_l1d_miss_hazard,

 regread_if.                           master ex1_regread_rs1,
 regread_if.                           master ex1_regread_rs2,

 output                                msrh_pkg::early_wr_t o_ex1_early_wr,
 output                                msrh_pkg::phy_wr_t   o_ex3_phy_wr,

 l1d_rd_if.master                      ex1_l1d_rd_if,
 output msrh_pkg::mispred_t            o_ex2_mispred,

 // Forwarding checker
 fwd_check_if.master                   ex2_fwd_check_if,
 fwd_check_if.master                   stbuf_fwd_check_if,
 ldq_haz_check_if.master               ldq_haz_check_if,
 lrq_haz_check_if.master               lrq_haz_check_if,

 l1d_lrq_if.master                     l1d_lrq_if,

 // Feedbacks to LDQ / STQ
 output ex1_q_update_t                 o_ex1_q_updates,
 output logic                          o_tlb_resolve,
 output ex2_q_update_t                 o_ex2_q_updates,

 done_if.master                        ex3_done_if,

 // Page Table Walk I/O
 tlb_ptw_if.master ptw_if
);

`include "msrh_csr_def.svh"

typedef struct packed {
  size_t  size;
  sign_t  sign;
  op_t    op;
} lsu_pipe_ctrl_t;


//
// EX0 stage
//
msrh_pkg::issue_t                     r_ex0_rs_issue, w_ex0_issue_next;
logic [MEM_Q_SIZE-1: 0] r_ex0_rs_index_oh;

// Selected signal
msrh_pkg::issue_t                      w_ex0_issue;
logic [MEM_Q_SIZE-1: 0]  w_ex0_index_oh;
lsu_pipe_ctrl_t                        w_ex0_pipe_ctrl;

//
// EX1 stage
//
msrh_pkg::issue_t                      r_ex1_issue, w_ex1_issue_next;
logic [MEM_Q_SIZE-1: 0]  r_ex1_index_oh;

logic [riscv_pkg::VADDR_W-1: 0]        w_ex1_vaddr;
tlb_req_t                w_ex1_tlb_req;
tlb_resp_t               w_ex1_tlb_resp;
lsu_pipe_ctrl_t                        r_ex1_pipe_ctrl;

logic                                  w_ex1_rs1_lsu_mispred;
logic                                  w_ex1_rs2_lsu_mispred;
logic                                  w_ex1_rs1_mispred;
logic                                  w_ex1_rs2_mispred;

//
// EX2 stage
//
msrh_pkg::issue_t                     r_ex2_issue, w_ex2_issue_next;
logic [MEM_Q_SIZE-1: 0]               r_ex2_index_oh;
logic [riscv_pkg::PADDR_W-1: 0]       r_ex2_paddr;
lsu_pipe_ctrl_t                       r_ex2_pipe_ctrl;
logic [riscv_pkg::XLEN_W-1: 0]        w_ex2_data_tmp;
logic [riscv_pkg::XLEN_W-1: 0]        w_ex2_data_sign_ext;
logic                                 w_ex2_l1d_mispredicted;
logic                                 r_ex2_tlb_miss;

//
// EX3 stage
//
msrh_pkg::issue_t                  r_ex3_issue, w_ex3_issue_next;
logic [riscv_pkg::XLEN_W-1: 0]     r_ex3_aligned_data;
logic                              r_ex3_mis_valid;

//
// Pipeline Logic
//
always_comb begin
  w_ex1_issue_next   = w_ex0_issue;

  w_ex2_issue_next       = r_ex1_issue;
  w_ex2_issue_next.valid = r_ex1_issue.valid & !w_ex1_tlb_resp.miss;

  w_ex3_issue_next       = r_ex2_issue;
  w_ex3_issue_next.valid = r_ex2_pipe_ctrl.op == OP_LOAD ? !w_ex2_l1d_mispredicted & !ex1_l1d_rd_if.s1_conflict :
                           r_ex2_issue.valid;
end


always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex0_rs_issue   <= 'h0;
    r_ex0_rs_index_oh <= 'h0;

    r_ex1_issue   <= 'h0;
    r_ex1_index_oh   <= 'h0;

    r_ex2_issue     <= 'h0;
    r_ex2_index_oh  <= 'h0;
    r_ex2_tlb_miss  <= 1'b0;
  end else begin
    r_ex0_rs_issue  <= i_rv0_issue;
    r_ex0_rs_index_oh <= i_rv0_index_oh;

    r_ex1_issue     <= w_ex1_issue_next;
    r_ex1_index_oh  <= w_ex0_index_oh;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;

    r_ex2_issue     <= w_ex2_issue_next;
    r_ex2_index_oh  <= r_ex1_index_oh;
    r_ex2_pipe_ctrl <= r_ex1_pipe_ctrl;
    r_ex2_tlb_miss  <= r_ex1_issue.valid & w_ex1_tlb_resp.miss;

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

 .i_kill(1'b0),
 .sfence_if(sfence_if),

 .i_status_prv(csr_info.mstatus[`MSTATUS_MPRV] ? csr_info.mstatus[`MSTATUS_MPP] : csr_info.priv),
 .i_csr_status(csr_info.mstatus),
 .i_csr_satp  (csr_info.satp   ),

 .i_tlb_req (w_ex1_tlb_req ),
 .o_tlb_ready(),
 .o_tlb_resp(w_ex1_tlb_resp),

 .o_tlb_update(o_tlb_resolve),
 .o_tlb_resp_miss (),

 .ptw_if (ptw_if)
 );


decoder_lsu_ctrl
u_decoder_ls_ctrl
  (
   .inst (w_ex0_issue.inst    ),
   .size (w_ex0_pipe_ctrl.size),
   .sign (w_ex0_pipe_ctrl.sign),
   .op   (w_ex0_pipe_ctrl.op  )
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

assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[0].valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rd_regs[0].rnid;

assign ex1_regread_rs2.valid = r_ex1_issue.valid & r_ex1_issue.rd_regs[1].valid;
assign ex1_regread_rs2.rnid  = r_ex1_issue.rd_regs[1].rnid;

assign w_ex1_vaddr = ex1_regread_rs1.data[riscv_pkg::VADDR_W-1:0] + (r_ex1_issue.cat == decoder_inst_cat_pkg::INST_CAT_ST ?
                                                                     {{(riscv_pkg::VADDR_W-12){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:25], r_ex1_issue.inst[11: 7]} :
                                                                     {{(riscv_pkg::VADDR_W-12){r_ex1_issue.inst[31]}}, r_ex1_issue.inst[31:20]});
assign w_ex1_tlb_req.valid       = r_ex1_issue.valid;
assign w_ex1_tlb_req.cmd         = r_ex1_pipe_ctrl.op == OP_LOAD ? M_XRD : M_XWR;
assign w_ex1_tlb_req.vaddr       = w_ex1_vaddr;
assign w_ex1_tlb_req.size        =
`ifdef RV64
                                   r_ex1_pipe_ctrl.size == SIZE_DW ? 8 :
`endif // RV64
                                   r_ex1_pipe_ctrl.size == SIZE_W  ? 4 :
                                   r_ex1_pipe_ctrl.size == SIZE_H  ? 2 :
                                   r_ex1_pipe_ctrl.size == SIZE_B  ? 1 : 0;
assign w_ex1_tlb_req.passthrough = 1'b0;

select_mispred_bus rs1_mispred_select
(
 .i_entry_rnid (r_ex1_issue.rd_regs[0].rnid),
 .i_entry_type (r_ex1_issue.rd_regs[0].typ),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_ex1_rs1_lsu_mispred)
 );


select_mispred_bus rs2_mispred_select
(
 .i_entry_rnid (r_ex1_issue.rd_regs[1].rnid),
 .i_entry_type (r_ex1_issue.rd_regs[1].typ),
 .i_mispred    (i_mispred_lsu),

 .o_mispred    (w_ex1_rs2_lsu_mispred)
 );

assign w_ex1_rs1_mispred = r_ex1_issue.rd_regs[0].valid & r_ex1_issue.rd_regs[0].predict_ready ? w_ex1_rs1_lsu_mispred : 1'b0;
assign w_ex1_rs2_mispred = r_ex1_issue.rd_regs[1].valid & r_ex1_issue.rd_regs[1].predict_ready ? w_ex1_rs2_lsu_mispred : 1'b0;

assign o_ex1_early_wr.valid       = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid & !w_ex1_tlb_resp.miss &
                                    ~w_ex1_rs1_mispred & ~w_ex1_rs2_mispred;
assign o_ex1_early_wr.rd_rnid     = r_ex1_issue.wr_reg.rnid;
assign o_ex1_early_wr.rd_type     = msrh_pkg::GPR;
assign o_ex1_early_wr.may_mispred = r_ex1_issue.valid & r_ex1_issue.wr_reg.valid;
assign o_ex1_tlb_miss_hazard      = r_ex1_issue.valid & w_ex1_tlb_resp.miss;

logic w_ex1_ld_except_valid;
logic w_ex1_st_except_valid;
logic r_ex2_except_valid;
msrh_pkg::except_t w_ex1_tlb_except_type;

assign w_ex1_ld_except_valid = (r_ex1_pipe_ctrl.op == OP_LOAD) &
                               (w_ex1_tlb_resp.pf.ld | w_ex1_tlb_resp.ae.ld | w_ex1_tlb_resp.ma.ld);
assign w_ex1_st_except_valid = (r_ex1_pipe_ctrl.op == OP_STORE) &
                               (w_ex1_tlb_resp.pf.st | w_ex1_tlb_resp.ae.st | w_ex1_tlb_resp.ma.st);
assign w_ex1_tlb_except_type = w_ex1_tlb_resp.ma.ld ? msrh_pkg::LOAD_ADDR_MISALIGN :
                               w_ex1_tlb_resp.pf.ld ? msrh_pkg::LOAD_PAGE_FAULT    :  // PF<-->AE priority is opposite, TLB generate
                               w_ex1_tlb_resp.ae.ld ? msrh_pkg::LOAD_ACC_FAULT     :  // PF and AE same time, PF is at first
                               w_ex1_tlb_resp.ma.st ? msrh_pkg::STAMO_ADDR_MISALIGN:
                               w_ex1_tlb_resp.pf.st ? msrh_pkg::STAMO_PAGE_FAULT   :  // PF and AE same time, PF is at first
                               w_ex1_tlb_resp.ae.st ? msrh_pkg::STAMO_ACC_FAULT    :  // PF<-->AE priority is opposite, TLB generate
                               msrh_pkg::except_t'('h0);

// Interface to EX1 updates
assign o_ex1_q_updates.update     = r_ex1_issue.valid;
// assign o_ex1_q_updates.inst       = r_ex1_issue;
// assign o_ex1_q_updates.pipe_sel_idx_oh = 1 << LSU_PIPE_IDX;
assign o_ex1_q_updates.cmt_id     = r_ex1_issue.cmt_id;
assign o_ex1_q_updates.grp_id     = r_ex1_issue.grp_id;
assign o_ex1_q_updates.hazard_valid = w_ex1_tlb_resp.miss;
assign o_ex1_q_updates.tlb_except_valid = !w_ex1_tlb_resp.miss & (w_ex1_ld_except_valid | w_ex1_st_except_valid);
assign o_ex1_q_updates.tlb_except_type  = w_ex1_tlb_except_type;
assign o_ex1_q_updates.index_oh   = r_ex1_index_oh;
assign o_ex1_q_updates.vaddr      = w_ex1_vaddr;
assign o_ex1_q_updates.paddr      = w_ex1_tlb_resp.paddr;
assign o_ex1_q_updates.st_data_valid = r_ex1_issue.rd_regs[1].ready;
assign o_ex1_q_updates.st_data     = ex1_regread_rs2.data;
assign o_ex1_q_updates.size        = r_ex1_pipe_ctrl.size;

`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    // if (o_ex1_q_updates.update &
    //     !$onehot(o_ex1_q_updates.pipe_sel_idx_oh)) begin
    //   $fatal(0, "LSU Pipeline : o_ex1_q_updates.pipe_sel_idx_oh should be one-hot Value=%x\n",
    //          o_ex1_q_updates.pipe_sel_idx_oh);
    // end
    if (o_ex1_q_updates.update &
        !$onehot0(o_ex1_q_updates.index_oh)) begin
      $fatal(0, "LSU Pipeline : o_ex1_q_updates.index_oh should be one-hot. Value=%x\n",
             o_ex1_q_updates.index_oh);
    end
  end
end
`endif // SIMULATION


// Interface to L1D cache
assign ex1_l1d_rd_if.s0_valid = r_ex1_issue.valid & (r_ex1_pipe_ctrl.op == OP_LOAD) & !w_ex1_tlb_resp.miss;
assign ex1_l1d_rd_if.s0_paddr = {w_ex1_tlb_resp.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)],
                                 {$clog2(DCACHE_DATA_B_W){1'b0}}};
assign ex1_l1d_rd_if.s0_h_pri = 1'b0;

//
// EX2 stage pipeline
//
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex2_paddr <= 'h0;
  end else begin
    r_ex2_paddr <= w_ex1_tlb_resp.paddr;
    r_ex2_except_valid <= w_ex1_ld_except_valid | w_ex1_st_except_valid;
  end
end

assign w_ex2_l1d_mispredicted       = r_ex2_issue.valid &
                                      (r_ex2_pipe_ctrl.op == OP_LOAD) &
                                      ex1_l1d_rd_if.s1_miss &
                                      ~ex1_l1d_rd_if.s1_conflict &
                                      (ex2_fwd_check_if.fwd_dw != gen_dw(r_ex2_pipe_ctrl.size, r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:0]));
                                      /* !ex2_fwd_check_if.fwd_valid; */
assign l1d_lrq_if.load              = w_ex2_l1d_mispredicted & !r_ex2_tlb_miss & !r_ex2_except_valid & !(ex1_l1d_rd_if.s1_conflict | ex1_l1d_rd_if.s1_hit);
assign l1d_lrq_if.req_payload.paddr = r_ex2_paddr;
// L1D replace information
assign l1d_lrq_if.req_payload.evict_valid = ex1_l1d_rd_if.s1_replace_valid;
assign l1d_lrq_if.req_payload.evict_payload.way   = ex1_l1d_rd_if.s1_replace_way;


// Interface to EX2 updates
assign o_ex2_q_updates.update     = r_ex2_issue.valid;
assign o_ex2_q_updates.hazard_typ = lrq_haz_check_if.ex2_evict_haz_valid ? LRQ_EVICT_CONFLICT :
                                    ex1_l1d_rd_if.s1_conflict            ? L1D_CONFLICT :
                                    l1d_lrq_if.load ?
                                    (l1d_lrq_if.resp_payload.conflict    ? LRQ_CONFLICT :
                                     l1d_lrq_if.resp_payload.full        ? LRQ_FULL     :
                                     LRQ_ASSIGNED) :
                                    NONE;
assign o_ex2_q_updates.lrq_index_oh = lrq_haz_check_if.ex2_evict_haz_valid ? lrq_haz_check_if.ex2_evict_entry_idx :
                                      l1d_lrq_if.resp_payload.lrq_index_oh;
assign o_ex2_q_updates.index_oh     = r_ex2_index_oh;

// ---------------------
// Misprediction Update
// ---------------------
always_comb begin
  o_ex2_mispred.mis_valid = w_ex2_l1d_mispredicted | r_ex2_tlb_miss | ex1_l1d_rd_if.s1_conflict | lrq_haz_check_if.ex2_evict_haz_valid;
  o_ex2_mispred.rd_type   = r_ex2_issue.wr_reg.typ;
  o_ex2_mispred.rd_rnid   = r_ex2_issue.wr_reg.rnid;
end


`ifdef SIMULATION
always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (o_ex2_q_updates.update &
        (r_ex2_pipe_ctrl.op == OP_LOAD) &
        (o_ex2_q_updates.hazard_typ == LRQ_CONFLICT) &
        !$onehot(o_ex2_q_updates.lrq_index_oh)) begin
      $fatal(0, "LSU Pipeline : o_ex2_q_updates.lrq_index_oh should be one-hot. Value=%x\n",
             o_ex2_q_updates.lrq_index_oh);
    end
    if (o_ex2_q_updates.update &
        (r_ex2_pipe_ctrl.op == OP_LOAD) &
        (o_ex2_q_updates.hazard_typ == LRQ_ASSIGNED) &
        !$onehot(o_ex2_q_updates.lrq_index_oh)) begin
      $fatal(0, "LSU Pipeline : o_ex2_q_updates.lrq_index_oh should be one-hot. Value=%x\n",
             o_ex2_q_updates.lrq_index_oh);
    end
  end // if (i_reset_n)
end
`endif // SIMULATION

// Forwarding check
assign ex2_fwd_check_if.valid  = r_ex2_issue.valid & (r_ex2_issue.cat == decoder_inst_cat_pkg::INST_CAT_LD);
assign ex2_fwd_check_if.cmt_id = r_ex2_issue.cmt_id;
assign ex2_fwd_check_if.grp_id = r_ex2_issue.grp_id;
assign ex2_fwd_check_if.paddr  = r_ex2_paddr;
assign ex2_fwd_check_if.paddr_dw = gen_dw(r_ex2_pipe_ctrl.size, r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:0]);

assign stbuf_fwd_check_if.valid  = r_ex2_issue.valid & (r_ex2_issue.cat == decoder_inst_cat_pkg::INST_CAT_LD);
assign stbuf_fwd_check_if.cmt_id = r_ex2_issue.cmt_id;
assign stbuf_fwd_check_if.grp_id = r_ex2_issue.grp_id;
assign stbuf_fwd_check_if.paddr  = r_ex2_paddr;
assign stbuf_fwd_check_if.paddr_dw = gen_dw(r_ex2_pipe_ctrl.size, r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:0]);

// LDQ Speculative Load Hazard Check
assign ldq_haz_check_if.ex2_valid  = r_ex2_issue.valid & (r_ex2_issue.cat == decoder_inst_cat_pkg::INST_CAT_ST);
assign ldq_haz_check_if.ex2_paddr  = r_ex2_paddr;
assign ldq_haz_check_if.ex2_cmt_id = r_ex2_issue.cmt_id;
assign ldq_haz_check_if.ex2_grp_id = r_ex2_issue.grp_id;
assign ldq_haz_check_if.ex2_size   = r_ex2_pipe_ctrl.size;

// LRQ Hazard Check
assign lrq_haz_check_if.ex2_valid  = r_ex2_issue.valid & (r_ex2_issue.cat == decoder_inst_cat_pkg::INST_CAT_LD);
assign lrq_haz_check_if.ex2_paddr  = r_ex2_paddr;

logic [riscv_pkg::XLEN_W/8-1: 0]                  w_ex2_fwd_dw;
logic [riscv_pkg::XLEN_W-1: 0]                    w_ex2_fwd_aligned_data;
logic [riscv_pkg::XLEN_W-1: 0]                    w_ex2_fwd_final_data;

always_comb begin
  case (r_ex2_pipe_ctrl.size)
`ifdef RV64
    SIZE_DW : begin
      w_ex2_fwd_dw           = ex2_fwd_check_if.fwd_dw;
      w_ex2_fwd_aligned_data = ex2_fwd_check_if.fwd_data;
    end
`endif // RV64
    SIZE_W  : begin
`ifdef RV32
      w_ex2_fwd_dw           = ex2_fwd_check_if.fwd_dw;
      w_ex2_fwd_aligned_data = ex2_fwd_check_if.fwd_data;
`else // RV32
      w_ex2_fwd_dw           = ex2_fwd_check_if.fwd_dw >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1], 2'b00};
      w_ex2_fwd_aligned_data = ex2_fwd_check_if.fwd_data >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1], 2'b00, 3'b000};
`endif // RV32
    end
    SIZE_H  : begin
      w_ex2_fwd_dw           = ex2_fwd_check_if.fwd_dw >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:1], 1'b0};
      w_ex2_fwd_aligned_data = ex2_fwd_check_if.fwd_data >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:1], 1'b0, 3'b000};
    end
    SIZE_B  : begin
      w_ex2_fwd_dw           = ex2_fwd_check_if.fwd_dw >>  r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:0];
      w_ex2_fwd_aligned_data = ex2_fwd_check_if.fwd_data >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:0], 3'b000};
    end
    default : begin
      w_ex2_fwd_dw = 'h0;
      w_ex2_fwd_aligned_data = 'h0;
    end
  endcase // case (r_ex2_pipe_ctrl.size)
end


logic [riscv_pkg::XLEN_W/8-1: 0]                  w_stbuf_fwd_dw;
logic [riscv_pkg::XLEN_W-1: 0]                    w_stbuf_fwd_aligned_data;

always_comb begin
  case (r_ex2_pipe_ctrl.size)
`ifdef RV64
    SIZE_DW : begin
      w_stbuf_fwd_dw           = stbuf_fwd_check_if.fwd_dw;
      w_stbuf_fwd_aligned_data = stbuf_fwd_check_if.fwd_data;
    end
`endif // RV64
    SIZE_W  : begin
`ifdef RV32
      w_stbuf_fwd_dw           = stbuf_fwd_check_if.fwd_dw;
      w_stbuf_fwd_aligned_data = stbuf_fwd_check_if.fwd_data;
`else // RV32
      w_stbuf_fwd_dw           = stbuf_fwd_check_if.fwd_dw >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1], 2'b00};
      w_stbuf_fwd_aligned_data = stbuf_fwd_check_if.fwd_data >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1], 2'b00, 3'b000};
`endif // RV32
    end
    SIZE_H  : begin
      w_stbuf_fwd_dw           = stbuf_fwd_check_if.fwd_dw >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:1], 1'b0};
      w_stbuf_fwd_aligned_data = stbuf_fwd_check_if.fwd_data >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:1], 1'b0, 3'b000};
    end
    SIZE_B  : begin
      w_stbuf_fwd_dw           = stbuf_fwd_check_if.fwd_dw >>  r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:0];
      w_stbuf_fwd_aligned_data = stbuf_fwd_check_if.fwd_data >> {r_ex2_paddr[$clog2(riscv_pkg::XLEN_W/8)-1:0], 3'b000};
    end
    default : begin
      w_stbuf_fwd_dw = 'h0;
      w_stbuf_fwd_aligned_data = 'h0;
    end
  endcase // case (r_ex2_pipe_ctrl.size)
end

logic [riscv_pkg::XLEN_W-1: 0] w_ex2_l1d_data;
assign w_ex2_l1d_data = ex1_l1d_rd_if.s1_data[{r_ex2_paddr[$clog2(DCACHE_DATA_B_W)-1:0], 3'b000} +: riscv_pkg::XLEN_W];

generate for (genvar b_idx = 0; b_idx < riscv_pkg::XLEN_W / 8; b_idx++) begin
  assign w_ex2_fwd_final_data[b_idx*8 +: 8] = w_ex2_fwd_dw  [b_idx] ? w_ex2_fwd_aligned_data  [b_idx*8 +: 8] :
                                              w_stbuf_fwd_dw[b_idx] ? w_stbuf_fwd_aligned_data[b_idx*8 +: 8] :
                                                                      w_ex2_l1d_data          [b_idx*8 +: 8];
end
endgenerate

always_comb begin
  case(r_ex2_pipe_ctrl.size)
`ifdef RV64
    SIZE_DW : w_ex2_data_tmp = w_ex2_fwd_final_data;
`endif // RV64
    SIZE_W  : w_ex2_data_tmp = {{(riscv_pkg::XLEN_W-32){1'b0}}, w_ex2_fwd_final_data[31: 0]};
    SIZE_H  : w_ex2_data_tmp = {{(riscv_pkg::XLEN_W-16){1'b0}}, w_ex2_fwd_final_data[15: 0]};
    SIZE_B  : w_ex2_data_tmp = {{(riscv_pkg::XLEN_W- 8){1'b0}}, w_ex2_fwd_final_data[ 7: 0]};
    default : w_ex2_data_tmp = 'h0;
  endcase // case (r_ex2_pipe_ctrl.size)
  if (r_ex2_pipe_ctrl.sign == SIGN_S) begin
    case(r_ex2_pipe_ctrl.size)
      SIZE_W  : w_ex2_data_sign_ext = {{(riscv_pkg::XLEN_W-32){w_ex2_data_tmp[31]}}, w_ex2_data_tmp[31: 0]};
      SIZE_H  : w_ex2_data_sign_ext = {{(riscv_pkg::XLEN_W-16){w_ex2_data_tmp[15]}}, w_ex2_data_tmp[15: 0]};
      SIZE_B  : w_ex2_data_sign_ext = {{(riscv_pkg::XLEN_W- 8){w_ex2_data_tmp[ 7]}}, w_ex2_data_tmp[ 7: 0]};
      default : w_ex2_data_sign_ext = w_ex2_data_tmp;
    endcase // case (r_ex2_pipe_ctrl.size)
  end else begin
    w_ex2_data_sign_ext = w_ex2_data_tmp;
  end
end // always_comb

//
// EX3 stage pipeline
//
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex3_aligned_data <= 'h0;
    r_ex3_mis_valid <= 1'b0;
  end else begin
    r_ex3_aligned_data <= w_ex2_data_sign_ext;
    r_ex3_mis_valid <= o_ex2_mispred.mis_valid;
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign ex3_done_if.done          = r_ex3_issue.valid;
assign ex3_done_if.index_oh      = 'h0;
assign ex3_done_if.except_valid  = 1'b0;
assign ex3_done_if.except_type   = msrh_pkg::except_t'('h0);
assign ex3_done_if.another_flush_valid  = ldq_haz_check_if.ex3_haz_valid;
assign ex3_done_if.another_flush_cmt_id = ldq_haz_check_if.ex3_haz_cmt_id;
assign ex3_done_if.another_flush_grp_id = ldq_haz_check_if.ex3_haz_grp_id;

assign o_ex3_phy_wr.valid   = r_ex3_issue.valid &
                              r_ex3_issue.wr_reg.valid & (r_ex3_issue.wr_reg.regidx != 'h0) &
                              ~r_ex3_mis_valid;
assign o_ex3_phy_wr.rd_rnid = r_ex3_issue.wr_reg.rnid;
assign o_ex3_phy_wr.rd_type = r_ex3_issue.wr_reg.typ;
assign o_ex3_phy_wr.rd_data = r_ex3_aligned_data;


endmodule // msrh_lsu_pipe

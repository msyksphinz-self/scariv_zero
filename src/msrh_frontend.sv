// ------------------------------------------------------------------------
// NAME : MRSH Frontend Instruction Fetcher
// TYPE : module
// ------------------------------------------------------------------------
// Frontend Instruction Fetcher and Predictor
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_frontend
  import msrh_pkg::*;
  import msrh_predict_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 /* SFENCE update information */
 sfence_if.slave  sfence_if,
  /* FENCE.I update */
  input logic     i_fence_i,

 l2_req_if.master ic_l2_req,
 l2_resp_if.slave ic_l2_resp,

 // PC Update from Committer
 input commit_blk_t i_commit,
 // Branch Tag Update Signal
 br_upd_if.slave              br_upd_if,

 /* CSR information */
 csr_info_if.slave           csr_info,
 /* Interrupt Request information */
 interrupt_if.slave          int_if,

 // Dispatch Info
 disp_if.master    iq_disp,

 // For checking RAS updates
 disp_if.watch     sc_disp,
 output logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] o_sc_ras_index,
 output logic [riscv_pkg::VADDR_W-1: 0]                    o_sc_ras_vaddr,

 // Fetch Target Queue
 br_upd_if.master  br_upd_fe_if,

 // Page Table Walk I/O
 tlb_ptw_if.master ptw_if
);

// ==============
// s0 stage
// ==============

typedef enum logic [ 2: 0]  {
  INIT = 0,
  FETCH_REQ = 1,
  WAIT_TLB_FILL = 2,
  WAIT_IC_FILL = 3,
  WAIT_IBUF_FREE = 4,
  WAIT_FLUSH_FREE = 5
} if_sm_t;

if_sm_t  r_if_state;
if_sm_t  w_if_state_next;

logic  r_s0_valid;
logic [riscv_pkg::VADDR_W-1:0]  r_s0_vaddr;
logic [riscv_pkg::VADDR_W-1:0]  w_s0_vaddr_next;
logic [riscv_pkg::VADDR_W-1:0]  w_s0_vaddr;
logic                           w_s0_predicted;
msrh_lsu_pkg::tlb_req_t         w_s0_tlb_req;
msrh_lsu_pkg::tlb_resp_t        w_s0_tlb_resp;
msrh_lsu_pkg::ic_req_t          w_s0_ic_req;
logic                           w_s0_ic_ready;
logic [riscv_pkg::VADDR_W-1: 0] w_s0_vaddr_flush_next;

// ==============
// s1 stage
// ==============

logic                          r_s1_valid;
logic                          w_s1_inst_valid;
logic                          r_s1_clear;
logic                          r_s1_predicted;
logic [riscv_pkg::VADDR_W-1:0] r_s1_vaddr;
logic [riscv_pkg::PADDR_W-1:0] r_s1_paddr;
logic                          r_s1_tlb_miss;
logic                          r_s1_tlb_except_valid;
except_t             r_s1_tlb_except_cause;

logic [riscv_pkg::VADDR_W-1: 0] w_s1_btb_target_vaddr;

logic                           w_s1_predict_valid;
logic [riscv_pkg::VADDR_W-1: 0] w_s1_predict_target_vaddr;

// ==============
// s2 stage
// ==============

logic                           w_s2_inst_valid;
logic                           r_s2_valid;
logic                           r_s2_clear;
logic                           r_s2_predicted;
logic [riscv_pkg::VADDR_W-1:0]  r_s2_vaddr;
msrh_lsu_pkg::ic_resp_t         w_s2_ic_resp;
logic                           w_s2_ic_miss;
logic [riscv_pkg::VADDR_W-1: 0] w_s2_ic_miss_vaddr;
logic                           r_s2_tlb_miss;
logic                           r_s2_tlb_except_valid;
except_t              r_s2_tlb_except_cause;

logic                           w_s2_predict_valid;
logic [riscv_pkg::VADDR_W-1: 0] w_s2_predict_target_vaddr;

logic                           w_s2_inst_buffer_load_valid;

// =======================
// Predictors
// =======================

btb_update_if w_btb_update_if ();
btb_search_if w_btb_search_if ();

bim_update_if w_bim_update_if ();
bim_search_if w_bim_search_if ();

ras_search_if w_ras_search_if ();

`ifdef SIMULATION
logic [riscv_pkg::PADDR_W-1:0]  r_s2_paddr;
`endif // SIMULATION

br_upd_if  br_upd_fe_tmp_if();

// ==============
// TLB
// ==============
logic                           w_tlb_ready;

// ==============
// Commiter PC
// ==============
logic                           w_commit_flush;
logic                           w_br_flush;
logic                           w_flush_valid;

logic                           r_flush_valid;
logic [CMT_ID_W-1:0]            r_flush_cmt_id;
logic [msrh_conf_pkg::DISP_SIZE-1:0] r_flush_grp_id;

logic                           w_flush_valid_next;
logic [CMT_ID_W-1:0]            w_flush_cmt_id_next;
logic [msrh_conf_pkg::DISP_SIZE-1:0] w_flush_grp_id_next;

logic                           w_existed_flush_is_older;

logic                           w_inst_buffer_ready;


logic                           w_ic_refill_wakeup;
logic                           w_tlb_refill_wakeup;
logic                           w_ibuf_refill_wakeup;
logic                           w_flush_haz_clear;

logic                           w_is_ftq_empty;
logic                           r_br_wait_ftq_free;
logic                           w_br_wait_ftq_free;

logic                           w_s0_req_ready;
assign w_s0_req_ready = w_s0_ic_ready & w_tlb_ready;
assign w_ic_refill_wakeup    = (r_if_state == WAIT_IC_FILL ) & w_s0_req_ready;
assign w_tlb_refill_wakeup   = (r_if_state == WAIT_TLB_FILL) & w_s0_req_ready;
assign w_ibuf_refill_wakeup  = (r_if_state == WAIT_IBUF_FREE ) & w_inst_buffer_ready & w_s0_req_ready;
assign w_flush_haz_clear     = (r_if_state == WAIT_FLUSH_FREE) & w_s0_req_ready &
                               (r_br_wait_ftq_free ? w_is_ftq_empty : 1'b1);

always_comb begin
  if (i_commit.commit & int_if.m_external_int_valid) begin
    /* verilator lint_off WIDTHCONCAT */
    w_s0_vaddr_flush_next = {csr_info.mtvec [riscv_pkg::VADDR_W-1: 1], 1'b0} + {riscv_common_pkg::MACHINE_EXTERNAL_INT, 2'b00};
  end else if (i_commit.commit & int_if.s_external_int_valid) begin
    /* verilator lint_off WIDTHCONCAT */
    w_s0_vaddr_flush_next = {csr_info.mtvec [riscv_pkg::VADDR_W-1: 1], 1'b0} + {riscv_common_pkg::SUPER_EXTERNAL_INT, 2'b00};
  end else if (i_commit.commit & int_if.m_timer_int_valid   ) begin
    /* verilator lint_off WIDTHCONCAT */
    w_s0_vaddr_flush_next = {csr_info.mtvec [riscv_pkg::VADDR_W-1: 1], 1'b0} + {riscv_common_pkg::MACHINE_TIMER_INT, 2'b00};
  end else if (i_commit.commit & int_if.s_timer_int_valid   ) begin
    /* verilator lint_off WIDTHCONCAT */
    w_s0_vaddr_flush_next = {csr_info.mtvec [riscv_pkg::VADDR_W-1: 1], 1'b0} + {riscv_common_pkg::SUPER_TIMER_INT, 2'b00};
  end else if (i_commit.commit & int_if.m_software_int_valid) begin
    /* verilator lint_off WIDTHCONCAT */
    w_s0_vaddr_flush_next = {csr_info.mtvec [riscv_pkg::VADDR_W-1: 1], 1'b0} + {riscv_common_pkg::MACHINE_SOFT_INT, 2'b00};
  end else if (i_commit.commit & int_if.s_software_int_valid) begin
    /* verilator lint_off WIDTHCONCAT */
    w_s0_vaddr_flush_next = {csr_info.mtvec [riscv_pkg::VADDR_W-1: 1], 1'b0} + {riscv_common_pkg::SUPER_SOFT_INT, 2'b00};
  end else if (is_flushed_commit(i_commit)) begin
    case (i_commit.except_type)
      SILENT_FLUSH   : w_s0_vaddr_flush_next = i_commit.epc + 4;
      ANOTHER_FLUSH  : w_s0_vaddr_flush_next = i_commit.epc;
      MRET           : w_s0_vaddr_flush_next = csr_info.mepc [riscv_pkg::VADDR_W-1: 0];
      SRET           : w_s0_vaddr_flush_next = csr_info.sepc [riscv_pkg::VADDR_W-1: 0];
      URET           : w_s0_vaddr_flush_next = csr_info.uepc [riscv_pkg::VADDR_W-1: 0];
      ECALL_M        :
        if (csr_info.medeleg[ECALL_M]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      ECALL_S        :
        if (csr_info.medeleg[ECALL_S]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      ECALL_U        :
        if (csr_info.medeleg[ECALL_U]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      INST_ACC_FAULT :
        if (csr_info.medeleg[INST_ACC_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      LOAD_ACC_FAULT :
        if (csr_info.medeleg[LOAD_ACC_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      STAMO_ACC_FAULT :
        if (csr_info.medeleg[STAMO_ACC_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      INST_PAGE_FAULT :
        if (csr_info.medeleg[INST_PAGE_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      LOAD_PAGE_FAULT :
        if (csr_info.medeleg[LOAD_PAGE_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      STAMO_PAGE_FAULT :
        if (csr_info.medeleg[STAMO_PAGE_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      INST_ADDR_MISALIGN :
        if (csr_info.medeleg[INST_ADDR_MISALIGN]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      LOAD_ADDR_MISALIGN :
        if (csr_info.medeleg[LOAD_ADDR_MISALIGN]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      STAMO_ADDR_MISALIGN :
        if (csr_info.medeleg[STAMO_ADDR_MISALIGN]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      ILLEGAL_INST        :
        if (csr_info.medeleg[ECALL_M]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      default           : begin
        w_s0_vaddr_flush_next = 'h0;
`ifdef SIMULATION
        $fatal (0, "This exception not supported now : %d", i_commit.except_type);
`endif // SIMULATION
      end
    endcase // case (i_commit.except_type)
  end else if (br_upd_fe_if.update & ~br_upd_fe_if.dead & br_upd_fe_if.mispredict) begin
    w_s0_vaddr_flush_next = br_upd_fe_if.target_vaddr;
  end else begin // if (|(i_commit.except_valid & ~i_commit.dead_id))
    w_s0_vaddr_flush_next = 'h0;
  end // else: !if(|(i_commit.except_valid & ~i_commit.dead_id))
end // always_comb


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_if_state <= INIT;

    r_s0_valid <= 1'b0;
    /* verilator lint_off WIDTH */
    r_s0_vaddr <= PC_INIT_VAL;
    r_br_wait_ftq_free <= 1'b0;
  end else begin
    r_if_state <= w_if_state_next;
    r_s0_valid <= 1'b1;
    r_s0_vaddr <= w_s0_vaddr_next;
    r_br_wait_ftq_free <= w_br_wait_ftq_free;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


logic w_s0_update_cond_0, w_s0_update_cond_1;
assign w_s0_update_cond_0 = (w_s0_ic_req.valid & w_s0_ic_ready & w_tlb_ready);
assign w_s0_update_cond_1 = w_if_state_next == FETCH_REQ;

always_comb begin
  w_s0_vaddr_next = r_s0_vaddr;
  w_if_state_next = r_if_state;
  w_br_wait_ftq_free = r_br_wait_ftq_free;

  case (r_if_state)
    INIT : begin
      w_if_state_next = FETCH_REQ;
    end
    FETCH_REQ : begin
      if (w_flush_valid) begin
        if (!w_s0_req_ready | w_br_flush & !w_is_ftq_empty) begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
          w_if_state_next = WAIT_FLUSH_FREE;
          w_br_wait_ftq_free = w_br_flush & !w_is_ftq_empty;
        end else begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        end
      end else if (r_s2_tlb_miss & !r_s2_clear) begin
        w_if_state_next = WAIT_TLB_FILL;
        w_s0_vaddr_next = r_s2_vaddr;
      end else if (w_s2_ic_miss & !r_s2_clear) begin
        w_if_state_next = WAIT_IC_FILL;
        w_s0_vaddr_next = w_s2_ic_miss_vaddr;
      end else if (w_s2_ic_resp.valid & ~w_inst_buffer_ready) begin
        if (r_s2_clear) begin
          // Vaddr at S2 stage is no more used, Stall vaddr
          w_s0_vaddr_next = r_s0_vaddr;
        end else begin
          // Retry from S2 stage Vaddr
          w_s0_vaddr_next = {w_s2_ic_resp.vaddr, 1'b0};
          w_if_state_next = WAIT_IBUF_FREE;
        end
      end else if (w_s2_predict_valid & !r_s2_clear) begin
        w_s0_vaddr_next = (w_s2_predict_target_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
      end else if (w_s1_predict_valid & !r_s1_clear) begin
        w_s0_vaddr_next = (w_s1_predict_target_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
      end else begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
      end
    end
    WAIT_IC_FILL : begin
      if (w_flush_valid) begin
        if (!w_ic_refill_wakeup | w_br_flush & !w_is_ftq_empty) begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
          w_if_state_next = WAIT_FLUSH_FREE;
          w_br_wait_ftq_free = w_br_flush & !w_is_ftq_empty;
        end else begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          w_if_state_next = FETCH_REQ;
        end
      end else if (w_ic_refill_wakeup) begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        w_if_state_next = FETCH_REQ;
      end
    end
    WAIT_TLB_FILL : begin
      if (w_flush_valid) begin
        if (!w_tlb_refill_wakeup | w_br_flush & !w_is_ftq_empty) begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
          w_if_state_next = WAIT_FLUSH_FREE;
          w_br_wait_ftq_free = w_br_flush & !w_is_ftq_empty;
        end else begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          w_if_state_next = FETCH_REQ;
        end
      end else if (w_tlb_refill_wakeup) begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        w_if_state_next = FETCH_REQ;
      end
    end
    WAIT_IBUF_FREE : begin
      if (w_flush_valid) begin
        if (!w_ibuf_refill_wakeup | w_br_flush & !w_is_ftq_empty) begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
          w_if_state_next = WAIT_FLUSH_FREE;
        end else begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          w_if_state_next = FETCH_REQ;
        end
      end else if (w_ibuf_refill_wakeup) begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        w_if_state_next = FETCH_REQ;
      end
    end
    WAIT_FLUSH_FREE : begin
      if (w_flush_valid & !w_existed_flush_is_older) begin
        if (w_flush_haz_clear) begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          w_if_state_next = FETCH_REQ;
        end else begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
        end
      end else if (w_flush_haz_clear) begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        w_if_state_next = FETCH_REQ;
      end
    end
    default : begin
    end
  endcase // case (r_if_state)

end


assign w_commit_flush  = is_flushed_commit(i_commit);

assign w_br_flush      = br_upd_fe_if.update & ~br_upd_fe_if.dead & br_upd_fe_if.mispredict;
assign w_flush_valid   = w_commit_flush | w_br_flush;

assign w_flush_valid_next  = w_commit_flush | w_br_flush;
assign w_flush_cmt_id_next = w_commit_flush ? i_commit.cmt_id       : br_upd_fe_if.cmt_id;
assign w_flush_grp_id_next = w_commit_flush ? i_commit.except_valid : br_upd_fe_if.grp_id;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_flush_valid  <= 1'b0;
    r_flush_cmt_id <= 'h0;
    r_flush_grp_id <= 'h0;
  end else begin
    if (w_flush_valid_next) begin
      r_flush_valid  <= w_flush_valid_next;
      r_flush_cmt_id <= w_flush_cmt_id_next;
      r_flush_grp_id <= w_flush_grp_id_next;
    end
  end
end

assign w_existed_flush_is_older = inst0_older (r_flush_valid,      r_flush_cmt_id,      r_flush_grp_id,
                                               w_flush_valid_next, w_flush_cmt_id_next, w_flush_grp_id_next);


assign {w_s0_predicted, w_s0_vaddr} = w_flush_valid ? {1'b0, w_s0_vaddr_flush_next} :
                                      r_s2_valid & ~r_s2_clear & w_s2_predict_valid ? {1'b1, w_s2_predict_target_vaddr} :
                                      r_s1_valid & ~r_s1_clear & w_s1_predict_valid ? {1'b0, w_s1_predict_target_vaddr} :
                                      {1'b0, r_s0_vaddr};

assign w_s0_tlb_req.valid = w_s0_ic_req.valid;
assign w_s0_tlb_req.vaddr = w_s0_vaddr;
assign w_s0_tlb_req.cmd   = msrh_lsu_pkg::M_XRD;
assign w_s0_tlb_req.size  = 'h0;
assign w_s0_tlb_req.passthrough  = 1'b0;

logic w_s0_tlb_resp_miss;

tlb u_tlb
  (
   .i_clk      (i_clk),
   .i_reset_n  (i_reset_n),

   .i_kill (1'b0),
   .sfence_if(sfence_if),

   .i_status_prv(csr_info.priv),
   .i_csr_status(csr_info.mstatus),
   .i_csr_satp(csr_info.satp),
   .ptw_if(ptw_if),

   .i_tlb_req  (w_s0_tlb_req ),
   .o_tlb_ready (w_tlb_ready),
   .o_tlb_resp (w_s0_tlb_resp),

   .o_tlb_update (),
   .o_tlb_resp_miss (w_s0_tlb_resp_miss)
   );

// s0 --> s1
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_valid <= 1'b0;
    r_s1_clear <= 1'b0;
    r_s1_predicted <= 1'b0;
    r_s1_vaddr <= 'h0;
    r_s1_paddr <= 'h0;
    r_s1_tlb_miss <= 'h0;
    r_s1_tlb_except_valid <= 1'b0;
  end else begin
    r_s1_valid <= r_s0_valid & w_s0_ic_req.valid;
    r_s1_clear <= ~w_flush_valid & w_s2_inst_buffer_load_valid & ~w_inst_buffer_ready;
    r_s1_predicted <= w_s0_predicted;
    r_s1_vaddr <= w_s0_vaddr;
    r_s1_paddr <= w_s0_tlb_resp.paddr;
    r_s1_tlb_miss <= /* w_s0_tlb_resp.miss*/ w_s0_tlb_resp_miss & r_s0_valid & w_s0_ic_req.valid;
    r_s1_tlb_except_valid <= w_s0_tlb_resp.pf.inst |
                             w_s0_tlb_resp.ae.inst |
                             w_s0_tlb_resp.ma.inst;
    r_s1_tlb_except_cause <= w_s0_tlb_resp.pf.inst ? INST_PAGE_FAULT :
                             w_s0_tlb_resp.ae.inst ? INST_ACC_FAULT  :
                             INST_ADDR_MISALIGN;  // w_s0_tlb_resp.ma.inst

  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


// s1 --> s2
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_valid <= 1'b0;
    r_s2_clear <= 1'b0;
    r_s2_vaddr <= 'h0;
    r_s2_predicted <= 1'b0;
    r_s2_tlb_miss         <= 1'b0;
    r_s2_tlb_except_valid <= 1'b0;
    r_s2_tlb_except_cause <= except_t'(0);
`ifdef SIMULATION
    r_s2_paddr <= 'h0;
`endif // SIMULATION
  end else begin
    r_s2_valid <= r_s1_valid;
    r_s2_clear <= r_s1_clear | w_s2_predict_valid & ~r_s1_predicted |
                  ~w_flush_valid & w_s2_inst_buffer_load_valid & ~w_inst_buffer_ready;
    r_s2_predicted <= r_s1_predicted;
    r_s2_vaddr <= r_s1_vaddr;
    r_s2_tlb_miss         <= r_s1_tlb_miss;
    r_s2_tlb_except_valid <= w_flush_valid ? 1'b0 : r_s1_tlb_except_valid;
    r_s2_tlb_except_cause <= r_s1_tlb_except_cause;
`ifdef SIMULATION
    r_s2_paddr <= r_s1_paddr;
`endif // SIMULATION
  end
end


assign w_s0_ic_req.valid = (r_if_state != INIT) & (w_if_state_next == FETCH_REQ);

assign w_s0_ic_req.vaddr = w_s0_vaddr;

assign w_s2_inst_valid = w_s2_ic_resp.valid & !r_s2_clear & !r_s2_tlb_miss;
assign w_s1_inst_valid = r_s1_valid         & !r_s1_clear & !r_s1_tlb_miss;

msrh_icache u_msrh_icache
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   // flushing is first entry is enough, other killing time, no need to flush
   .i_flush_valid (w_flush_valid),

   .i_fence_i (i_fence_i),

   .i_s0_req (w_s0_ic_req),
   .o_s0_ready(w_s0_ic_ready),


   .i_s1_paddr (r_s1_paddr),
   .i_s1_kill  (r_s1_tlb_miss | r_s2_tlb_miss | r_s1_tlb_except_valid),

   .o_s2_resp (w_s2_ic_resp),

   .ic_l2_req  (ic_l2_req ),
   .ic_l2_resp (ic_l2_resp),

   .o_s2_miss       (w_s2_ic_miss      ),
   .o_s2_miss_vaddr (w_s2_ic_miss_vaddr)
   );

assign w_s2_inst_buffer_load_valid = (r_if_state == FETCH_REQ) &
                                     (w_s2_inst_valid  |
                                      (r_s2_valid & ~r_s2_tlb_miss & r_s2_tlb_except_valid));

`ifdef SIMULATION
logic [riscv_pkg::PADDR_W-1: 0] w_s2_ic_resp_debug_addr;
assign w_s2_ic_resp_debug_addr = {w_s2_ic_resp.vaddr, 1'b0};
`endif // SIMULATION

msrh_inst_buffer
u_msrh_inst_buffer
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),
   // flushing is first entry is enough, other killing time, no need to flush
   .i_flush_valid (w_flush_valid),

   .i_s2_inst_valid       (w_s2_inst_buffer_load_valid),
   .bim_search_if         (w_bim_search_if),
   .btb_search_if         (w_btb_search_if),
   .ras_search_if         (w_ras_search_if),

   .i_commit (i_commit),

   .o_inst_ready   (w_inst_buffer_ready),
   .i_inst_pc      (w_s2_ic_resp.vaddr),
   .i_inst_in      (w_s2_ic_resp.data),
   .i_inst_byte_en (w_s2_ic_resp.be),
   .i_inst_tlb_except_valid (r_s2_tlb_except_valid),
   .i_inst_tlb_except_cause (r_s2_tlb_except_cause),

   .iq_disp        (iq_disp)
   );


// =======================
// Fetch Target Queue
// =======================
msrh_ftq u_ftq
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_commit (i_commit),

   .o_is_ftq_empty (w_is_ftq_empty),

   .sc_disp (sc_disp),
   .br_upd_if (br_upd_if),

   .br_upd_fe_if (br_upd_fe_tmp_if)
   );

br_upd_if_buf u_br_upd_if_buf (.slave_if (br_upd_fe_tmp_if), .master_if (br_upd_fe_if));

// =======================
// Predictors
// =======================
assign w_btb_search_if.s0_valid       = w_s0_ic_req.valid;
assign w_btb_search_if.s0_pc_vaddr    = w_s0_vaddr;

assign w_btb_update_if.valid          = br_upd_if.update & ~br_upd_if.dead & ~br_upd_if.is_ret;
assign w_btb_update_if.pc_vaddr       = br_upd_if.pc_vaddr;
assign w_btb_update_if.target_vaddr   = br_upd_if.target_vaddr;
assign w_btb_update_if.is_call        = br_upd_if.is_call;
assign w_btb_update_if.is_ret         = br_upd_if.is_ret;
assign w_btb_update_if.is_rvc         = br_upd_if.is_rvc;

assign w_bim_search_if.s0_valid       = w_s0_ic_req.valid;
assign w_bim_search_if.s0_pc_vaddr    = w_s0_vaddr;
// assign w_bim_search_if.s1_bim_value   = ;

assign w_bim_update_if.valid          = br_upd_if.update & ~br_upd_if.dead;
assign w_bim_update_if.pc_vaddr       = br_upd_if.pc_vaddr;
assign w_bim_update_if.hit            = ~br_upd_if.mispredict;
assign w_bim_update_if.taken          = br_upd_if.taken;
assign w_bim_update_if.bim_value      = br_upd_if.bim_value;
assign w_bim_update_if.is_rvc         = br_upd_if.is_rvc;

logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] w_s1_btb_bim_hit_array;
assign w_s1_btb_bim_hit_array = w_btb_search_if.s1_hit & w_bim_search_if.s1_pred_taken;

assign w_s1_predict_valid = w_s1_inst_valid &
                            ((|w_s1_btb_bim_hit_array) |   // from BIM and BTB
                             (|w_ras_search_if.s1_is_ret));  // from RAS
assign w_s1_predict_target_vaddr = |w_ras_search_if.s1_is_ret ? {w_ras_search_if.s1_ras_vaddr, 1'b0} :
                                   w_s1_btb_target_vaddr;

assign w_s2_predict_valid        = |w_ras_search_if.s2_is_ret;  // from RAS
assign w_s2_predict_target_vaddr = {w_ras_search_if.s2_ras_vaddr, 1'b0};


msrh_predictor u_predictor
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .sc_disp   (sc_disp),
   .o_sc_ras_index  (o_sc_ras_index),
   .o_sc_ras_vaddr (o_sc_ras_vaddr),

   .i_s1_valid   (w_s1_inst_valid),
   .i_s2_valid   (w_s2_inst_valid),

   .i_s2_ic_resp (w_s2_ic_resp),

   .update_btb_if (w_btb_update_if),
   .search_btb_if (w_btb_search_if),
   .o_s1_btb_target_vaddr (w_s1_btb_target_vaddr),

   .update_bim_if (w_bim_update_if),
   .search_bim_if (w_bim_search_if),

   .ras_search_if (w_ras_search_if),

   .br_upd_fe_if (br_upd_fe_tmp_if)
   );

endmodule // msrh_frontend

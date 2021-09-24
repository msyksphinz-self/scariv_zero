// ------------------------------------------------------------------------
// NAME : MRSH Frontend Instruction Fetcher
// TYPE : module
// ------------------------------------------------------------------------
// Frontend Instruction Fetcher and Predictor
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_frontend
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
 input msrh_pkg::commit_blk_t i_commit,
 // Branch Tag Update Signal
 br_upd_if.slave              br_upd_if,

  /* CSR information */
  csr_info_if.slave           csr_info,

 // Dispatch Info
 disp_if.master    iq_disp,
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
msrh_lsu_pkg::tlb_req_t         w_s0_tlb_req;
msrh_lsu_pkg::tlb_resp_t        w_s0_tlb_resp;
msrh_lsu_pkg::ic_req_t          w_s0_ic_req;
logic                           w_s0_ic_ready;
logic [riscv_pkg::VADDR_W-1: 0] w_s0_vaddr_flush_next;

// ==============
// s1 stage
// ==============

logic                          r_s1_valid;
logic                          r_s1_clear;
logic [riscv_pkg::VADDR_W-1:0] r_s1_vaddr;
logic [riscv_pkg::PADDR_W-1:0] r_s1_paddr;
logic                          r_s1_tlb_miss;
logic                          r_s1_tlb_except_valid;
msrh_pkg::except_t             r_s1_tlb_except_cause;

// ==============
// s2 stage
// ==============

logic                           w_s2_inst_valid;
logic                           r_s2_valid;
logic                           r_s2_clear;
logic [riscv_pkg::VADDR_W-1:0]  r_s2_vaddr;
msrh_lsu_pkg::ic_resp_t         w_s2_ic_resp;
logic                           w_s2_ic_miss;
logic [riscv_pkg::VADDR_W-1: 0] w_s2_ic_miss_vaddr;
logic                           r_s2_tlb_miss;
logic                           r_s2_tlb_except_valid;
msrh_pkg::except_t              r_s2_tlb_except_cause;
`ifdef SIMULATION
logic [riscv_pkg::PADDR_W-1:0]  r_s2_paddr;
`endif // SIMULATION

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

logic                           w_inst_buffer_ready;


logic                           w_ic_refill_wakeup;
logic                           w_tlb_refill_wakeup;
logic                           w_ibuf_refill_wakeup;
logic                           w_flush_haz_clear;

logic                           w_s0_req_ready;
assign w_s0_req_ready = w_s0_ic_ready & w_tlb_ready;
assign w_ic_refill_wakeup    = (r_if_state == WAIT_IC_FILL ) & w_s0_req_ready;
assign w_tlb_refill_wakeup   = (r_if_state == WAIT_TLB_FILL) & w_s0_req_ready;
assign w_ibuf_refill_wakeup  = (r_if_state == WAIT_IBUF_FREE ) & w_inst_buffer_ready & w_s0_req_ready;
assign w_flush_haz_clear     = (r_if_state == WAIT_FLUSH_FREE) & w_s0_req_ready;

always_comb begin
  if (i_commit.commit & |(i_commit.except_valid & ~i_commit.dead_id)) begin
    case (i_commit.except_type)
      msrh_pkg::SILENT_FLUSH   : w_s0_vaddr_flush_next = i_commit.epc + 4;
      msrh_pkg::MRET           : w_s0_vaddr_flush_next = csr_info.mepc [riscv_pkg::VADDR_W-1: 0];
      msrh_pkg::SRET           : w_s0_vaddr_flush_next = csr_info.sepc [riscv_pkg::VADDR_W-1: 0];
      msrh_pkg::URET           : w_s0_vaddr_flush_next = csr_info.uepc [riscv_pkg::VADDR_W-1: 0];
      msrh_pkg::ECALL_M        :
        if (csr_info.medeleg[msrh_pkg::ECALL_M]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::ECALL_S        :
        if (csr_info.medeleg[msrh_pkg::ECALL_S]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::ECALL_U        :
        if (csr_info.medeleg[msrh_pkg::ECALL_U]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::INST_ACC_FAULT :
        if (csr_info.medeleg[msrh_pkg::INST_ACC_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::LOAD_ACC_FAULT :
        if (csr_info.medeleg[msrh_pkg::LOAD_ACC_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::STAMO_ACC_FAULT :
        if (csr_info.medeleg[msrh_pkg::STAMO_ACC_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::INST_PAGE_FAULT :
        if (csr_info.medeleg[msrh_pkg::INST_PAGE_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::LOAD_PAGE_FAULT :
        if (csr_info.medeleg[msrh_pkg::LOAD_PAGE_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::STAMO_PAGE_FAULT :
        if (csr_info.medeleg[msrh_pkg::STAMO_PAGE_FAULT]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::INST_ADDR_MISALIGN :
        if (csr_info.medeleg[msrh_pkg::INST_ADDR_MISALIGN]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::LOAD_ADDR_MISALIGN :
        if (csr_info.medeleg[msrh_pkg::LOAD_ADDR_MISALIGN]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::STAMO_ADDR_MISALIGN :
        if (csr_info.medeleg[msrh_pkg::STAMO_ADDR_MISALIGN]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      msrh_pkg::ILLEGAL_INST        :
        if (csr_info.medeleg[msrh_pkg::ECALL_M]) begin
          w_s0_vaddr_flush_next = csr_info.stvec[riscv_pkg::VADDR_W-1: 0];
        end else begin
          w_s0_vaddr_flush_next = csr_info.mtvec[riscv_pkg::VADDR_W-1: 0];
        end
      default           : begin
        w_s0_vaddr_flush_next = 'h0;
`ifdef SIMULATION
        $fatal (0, "This exception not supported now");
`endif // SIMULATION
      end
    endcase // case (i_commit.except_type)
  end else if (br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict) begin
    w_s0_vaddr_flush_next = br_upd_if.target_vaddr;
  end else begin // if (|(i_commit.except_valid & ~i_commit.dead_id))
    w_s0_vaddr_flush_next = 'h0;
  end // else: !if(|(i_commit.except_valid & ~i_commit.dead_id))
end // always_comb


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_if_state <= INIT;

    r_s0_valid <= 1'b0;
    /* verilator lint_off WIDTH */
    r_s0_vaddr <= msrh_pkg::PC_INIT_VAL;
  end else begin
    r_if_state <= w_if_state_next;
    r_s0_valid <= 1'b1;
    r_s0_vaddr <= w_s0_vaddr_next;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


logic w_s0_update_cond_0, w_s0_update_cond_1;
assign w_s0_update_cond_0 = (w_s0_ic_req.valid & w_s0_ic_ready & w_tlb_ready);
assign w_s0_update_cond_1 = w_if_state_next == FETCH_REQ;

always_comb begin
  w_s0_vaddr_next = r_s0_vaddr;
  w_if_state_next = r_if_state;

  case (r_if_state)
    INIT : begin
      w_if_state_next = FETCH_REQ;
    end
    FETCH_REQ : begin
      if (w_flush_valid) begin
        if (w_s0_req_ready) begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        end else begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
          w_if_state_next = WAIT_FLUSH_FREE;
        end
      end else if (r_s2_tlb_miss & !r_s2_clear) begin
        w_if_state_next = WAIT_TLB_FILL;
        w_s0_vaddr_next = r_s2_vaddr;
      end else if (w_s2_ic_miss & !r_s2_clear) begin
        w_if_state_next = WAIT_IC_FILL;
        w_s0_vaddr_next = w_s2_ic_miss_vaddr;
      end else if (w_s2_ic_resp.valid & !w_inst_buffer_ready) begin
        w_s0_vaddr_next = {w_s2_ic_resp.addr, 1'b0};
        w_if_state_next = WAIT_IBUF_FREE;
      end else begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
      end
    end
    WAIT_IC_FILL : begin
      if (w_flush_valid) begin
        if (w_ic_refill_wakeup) begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          w_if_state_next = FETCH_REQ;
        end else begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
          w_if_state_next = WAIT_FLUSH_FREE;
        end
      end else if (w_ic_refill_wakeup) begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        w_if_state_next = FETCH_REQ;
      end
    end
    WAIT_TLB_FILL : begin
      if (w_flush_valid) begin
        if (w_tlb_refill_wakeup) begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          w_if_state_next = FETCH_REQ;
        end else begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
          w_if_state_next = WAIT_FLUSH_FREE;
        end
      end else if (w_tlb_refill_wakeup) begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        w_if_state_next = FETCH_REQ;
      end
    end
    WAIT_IBUF_FREE : begin
      if (w_flush_valid) begin
        if (w_ibuf_refill_wakeup) begin
          w_s0_vaddr_next = (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                            (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          w_if_state_next = FETCH_REQ;
        end else begin
          w_s0_vaddr_next = w_s0_vaddr_flush_next;
          w_if_state_next = WAIT_FLUSH_FREE;
        end
      end else if (w_ibuf_refill_wakeup) begin
        w_s0_vaddr_next = (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
        w_if_state_next = FETCH_REQ;
      end
    end
    WAIT_FLUSH_FREE : begin
      if (w_flush_valid) begin
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


assign w_commit_flush = msrh_pkg::is_flushed_commit(i_commit);
assign w_br_flush     = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_flush_valid  = w_commit_flush | w_br_flush;
assign w_s0_vaddr     = w_flush_valid ? w_s0_vaddr_flush_next : r_s0_vaddr;

assign w_s0_tlb_req.valid = w_s0_ic_req.valid;
assign w_s0_tlb_req.vaddr = w_s0_vaddr;
assign w_s0_tlb_req.cmd   = msrh_lsu_pkg::M_XRD;
assign w_s0_tlb_req.size  = 'h0;
assign w_s0_tlb_req.passthrough  = 1'b0;

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

   .o_tlb_update ()
   );

// s0 --> s1
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_valid <= 1'b0;
    r_s1_vaddr <= 'h0;
    r_s1_paddr <= 'h0;
    r_s1_tlb_miss <= 'h0;
    r_s1_tlb_except_valid <= 1'b0;
  end else begin
    r_s1_valid <= r_s0_valid & w_s0_ic_req.valid;
    r_s1_clear <= w_s2_ic_resp.valid & ~w_inst_buffer_ready;
    r_s1_vaddr <= w_s0_vaddr;
    r_s1_paddr <= w_s0_tlb_resp.paddr;
    r_s1_tlb_miss <= w_s0_tlb_resp.miss & r_s0_valid & w_s0_ic_req.valid /* & w_tlb_ready */;
    r_s1_tlb_except_valid <= w_s0_tlb_resp.pf.inst |
                             w_s0_tlb_resp.ae.inst |
                             w_s0_tlb_resp.ma.inst;
    r_s1_tlb_except_cause <= w_s0_tlb_resp.pf.inst ? msrh_pkg::INST_PAGE_FAULT :
                             w_s0_tlb_resp.ae.inst ? msrh_pkg::INST_ACC_FAULT  :
                             msrh_pkg::INST_ADDR_MISALIGN;  // w_s0_tlb_resp.ma.inst

  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


// s1 --> s2
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_valid <= 1'b0;
    r_s2_clear <= 1'b0;
    r_s2_vaddr <= 'h0;
    r_s2_tlb_miss         <= 1'b0;
    r_s2_tlb_except_valid <= 1'b0;
    r_s2_tlb_except_cause <= msrh_pkg::except_t'(0);
`ifdef SIMULATION
    r_s2_paddr <= 'h0;
`endif // SIMULATION
  end else begin
    r_s2_valid <= r_s1_valid;
    r_s2_clear <= r_s1_clear;
    r_s2_vaddr <= r_s1_vaddr;
    r_s2_tlb_miss         <= r_s1_tlb_miss        ;
    r_s2_tlb_except_valid <= w_flush_valid ? 1'b0 : r_s1_tlb_except_valid;
    r_s2_tlb_except_cause <= r_s1_tlb_except_cause;
`ifdef SIMULATION
    r_s2_paddr <= r_s1_paddr;
`endif // SIMULATION
  end
end


assign w_s0_ic_req.valid = ((r_if_state == FETCH_REQ) & !(w_s2_ic_resp.valid & !w_inst_buffer_ready) &
                            !r_s1_tlb_miss & !r_s2_tlb_miss)  |
                           w_ic_refill_wakeup | w_tlb_refill_wakeup | w_ibuf_refill_wakeup | w_flush_haz_clear;

assign w_s0_ic_req.vaddr = w_s0_vaddr;

assign w_s2_inst_valid = w_s2_ic_resp.valid & !r_s2_clear & !r_s2_tlb_miss;

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

logic w_inst_buffer_load_valid;
assign w_inst_buffer_load_valid = (r_if_state == FETCH_REQ) &
                                  (w_s2_inst_valid  |
                                   (r_s2_valid & ~r_s2_tlb_miss & r_s2_tlb_except_valid));

`ifdef SIMULATION
logic [riscv_pkg::PADDR_W-1: 0] w_s2_ic_resp_debug_addr;
assign w_s2_ic_resp_debug_addr = {w_s2_ic_resp.addr, 1'b0};
`endif // SIMULATION


msrh_inst_buffer
u_msrh_inst_buffer
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),
   // flushing is first entry is enough, other killing time, no need to flush
   .i_flush_valid (w_flush_valid),

   .i_inst_valid (w_inst_buffer_load_valid),

   .i_commit (i_commit),

   .o_inst_ready   (w_inst_buffer_ready),
   .i_inst_pc      (w_s2_ic_resp.addr),
   .i_inst_in      (w_s2_ic_resp.data),
   .i_inst_byte_en (w_s2_ic_resp.be),
   .i_inst_tlb_except_valid (r_s2_tlb_except_valid),
   .i_inst_tlb_except_cause (r_s2_tlb_except_cause),

   .iq_disp        (iq_disp)
   );

// =======================
// Predictors
// =======================
btb_update_if w_btb_update_if ();
btb_search_if w_btb_search_if ();

bim_update_if w_bim_update_if ();
bim_search_if w_bim_search_if ();

assign w_btb_search_if.s0_valid       = w_s0_ic_req.valid;
assign w_btb_search_if.s0_pc_vaddr    = w_s0_vaddr;
// assign w_btb_search_if.s1_hit         = ;
// assign w_btb_search_if.s1_target_addr = ;

assign w_btb_update_if.valid          = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_btb_update_if.pc_vaddr       = {br_upd_if.pc_vaddr[riscv_pkg::VADDR_W-1: $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W)],
                                         {$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W){1'b0}}};
assign w_btb_update_if.target_vaddr   = br_upd_if.target_vaddr;

assign w_bim_search_if.s0_valid       = w_s0_ic_req.valid;
assign w_bim_search_if.s0_pc_vaddr    = w_s0_vaddr;
// assign w_bim_search_if.s1_bim_value   = ;

assign w_bim_update_if.valid          = br_upd_if.update & ~br_upd_if.dead;
assign w_bim_update_if.pc_vaddr       = {br_upd_if.pc_vaddr[riscv_pkg::VADDR_W-1: $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W)],
                                         {$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W){1'b0}}};
assign w_bim_update_if.hit            = br_upd_if.update & ~br_upd_if.dead & ~br_upd_if.mispredict;
// assign w_bim_update_if.bim_value      = ;

msrh_predictor u_predictor
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .update_btb_if (w_btb_update_if),
   .search_btb_if (w_btb_search_if),

   .update_bim_if (w_bim_update_if),
   .search_bim_if (w_bim_search_if),

   .i_commit (i_commit)
   );


endmodule // msrh_frontend

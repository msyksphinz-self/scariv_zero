module msrh_frontend
(
 input logic i_clk,
 input logic i_reset_n,

 l2_req_if.master ic_l2_req,
 l2_resp_if.slave ic_l2_resp,

 // PC Update from Committer
 input msrh_pkg::commit_blk_t i_commit,

  /* CSR information */
  csr_info_if.slave           csr_info,

 // Dispatch Info
 disp_if.master iq_disp
);

// ==============
// s0 stage
// ==============

typedef enum logic [ 1: 0] {
  INIT = 0,
  ISSUED = 1,
  WAIT_RD = 2,
  WAIT_FB_FREE = 3
} if_sm_t;

if_sm_t  r_if_state;
if_sm_t  w_if_state_next;

logic  r_s0_valid;
logic [riscv_pkg::VADDR_W-1:0]  r_s0_vaddr;
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
logic [riscv_pkg::PADDR_W-1:0] r_s1_paddr;
logic                          r_s1_tlb_miss;

// ==============
// s2 stage
// ==============

logic                          w_s2_inst_valid;
logic                          r_s2_valid;
logic                          r_s2_clear;
msrh_lsu_pkg::ic_resp_t        w_s2_ic_resp;
logic                          w_s2_ic_miss;
logic [riscv_pkg::VADDR_W-1: 0] w_s2_ic_miss_vaddr;


// ==============
// Commiter PC
// ==============
logic                           w_commit_upd_pc;
logic                           w_commit_flush_valid;

logic                           w_inst_buffer_ready;

assign w_s0_vaddr_flush_next = i_commit.except_valid ?
                               (i_commit.except_type == msrh_pkg::MRET    ? csr_info.mepc [riscv_pkg::VADDR_W-1: 0] :
                                i_commit.except_type == msrh_pkg::ECALL_M ? csr_info.mtvec[riscv_pkg::VADDR_W-1: 0] :
                                'h0) :
                               i_commit.upd_pc_vaddr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_if_state <= INIT;

    r_s0_valid <= 1'b0;
    /* verilator lint_off WIDTH */
    r_s0_vaddr <= msrh_pkg::PC_INIT_VAL;
  end else begin
    r_s0_valid <= 1'b1;
    r_if_state <= w_if_state_next;

    if (w_commit_upd_pc) begin
      if (w_s0_ic_req.valid & w_s0_ic_ready) begin
        r_s0_vaddr <= (w_s0_vaddr_flush_next & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                      (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
      end else begin
        r_s0_vaddr <= w_s0_vaddr_flush_next;
      end
    end else begin
      case (r_if_state)
        ISSUED : begin
          if (w_s2_ic_miss & !r_s2_clear) begin
            r_s0_vaddr <= w_s2_ic_miss_vaddr;
          end else if (w_s2_inst_valid & !w_inst_buffer_ready) begin
            r_s0_vaddr <= {w_s2_ic_resp.addr, 1'b0};
          end else begin
            r_s0_vaddr <= (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          end
        end
        WAIT_RD : begin
          if (w_s0_ic_ready) begin
            r_s0_vaddr <= (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          end
        end
        WAIT_FB_FREE : begin
          if (w_inst_buffer_ready & w_s0_ic_ready) begin
            r_s0_vaddr <= (r_s0_vaddr & ~((1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W))-1)) +
                          (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
          end
        end
        default : begin end
      endcase // case (r_if_state)
    end // else: !if(w_commit_upd_pc)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

always_comb begin
  w_if_state_next = r_if_state;
  case (r_if_state)
    INIT : begin
      w_if_state_next = ISSUED;
    end
    ISSUED : begin
      if (w_s2_ic_miss & !r_s2_clear) begin
        w_if_state_next = WAIT_RD;
      end else if (!w_inst_buffer_ready) begin
        w_if_state_next = WAIT_FB_FREE;
      end
    end
    WAIT_RD : begin
      if (w_s0_ic_ready) begin
        w_if_state_next = ISSUED;
      end
    end
    WAIT_FB_FREE : begin
      if (w_inst_buffer_ready & w_s0_ic_ready) begin
        w_if_state_next = ISSUED;
      end
    end
  endcase // case (r_if_state)
end


assign w_s0_vaddr = w_commit_upd_pc ? w_s0_vaddr_flush_next : r_s0_vaddr;
assign w_commit_upd_pc = i_commit.commit & i_commit.upd_pc_valid & !i_commit.all_dead;
assign w_commit_flush_valid = i_commit.commit &
                              i_commit.flush_valid &
                              !i_commit.all_dead;

assign w_s0_tlb_req.vaddr = w_s0_vaddr;
assign w_s0_tlb_req.cmd   = msrh_lsu_pkg::M_XRD;

tlb u_tlb
  (
   .i_clk      (i_clk),
   .i_reset_n  (i_reset_n),

   .i_kill (1'b0),

   .i_sfence (1'b0),
   .i_status_prv(),
   .i_csr_satp(),
   .ptw_if(),

   .i_tlb_req  (w_s0_tlb_req ),
   .o_tlb_ready (),
   .o_tlb_resp (w_s0_tlb_resp),

   .o_tlb_update ()
   );

// s0 --> s1
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_valid <= 1'b0;
    r_s1_paddr <= 'h0;
    r_s1_tlb_miss <= 'h0;
  end else begin
    r_s1_valid <= r_s0_valid;
    r_s1_clear <= w_s2_ic_resp.valid & ~w_inst_buffer_ready;
    r_s1_paddr <= w_s0_tlb_resp.paddr;
    r_s1_tlb_miss <= w_s0_tlb_resp.miss;
  end
end

// s1 --> s2
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_valid <= 1'b0;
    r_s2_clear <= 1'b0;
  end else begin
    r_s2_valid <= r_s1_valid;
    r_s2_clear <= r_s1_clear;
  end
end


assign w_s0_ic_req.valid = ((r_if_state == ISSUED) & !(w_s2_ic_resp.valid & !w_inst_buffer_ready))  |
                           ((r_if_state == WAIT_RD) & w_s0_ic_ready) |
                           ((r_if_state == WAIT_FB_FREE) & w_inst_buffer_ready & w_s0_ic_ready);
assign w_s0_ic_req.vaddr = w_s0_vaddr;

assign w_s2_inst_valid = w_s2_ic_resp.valid & !r_s1_clear & !r_s2_clear;

msrh_icache u_msrh_icache
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   // flushing is first entry is enough, other killing time, no need to flush
   .i_flush_valid (w_commit_flush_valid),

   .i_s0_req (w_s0_ic_req),
   .o_s0_ready(w_s0_ic_ready),


   .i_s1_paddr (r_s1_paddr),
   .i_s1_tlb_miss (r_s1_tlb_miss),

   .o_s2_resp (w_s2_ic_resp),

   .ic_l2_req  (ic_l2_req ),
   .ic_l2_resp (ic_l2_resp),

   .o_s2_miss       (w_s2_ic_miss      ),
   .o_s2_miss_vaddr (w_s2_ic_miss_vaddr)
   );

msrh_inst_buffer
u_msrh_inst_buffer
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),
   // flushing is first entry is enough, other killing time, no need to flush
   .i_flush_valid (w_commit_flush_valid),

   .i_inst_valid (w_s2_inst_valid),

   .i_commit (i_commit),

   .o_inst_ready   (w_inst_buffer_ready),
   .i_inst_pc      (w_s2_ic_resp.addr),
   .i_inst_in      (w_s2_ic_resp.data),
   .i_inst_byte_en (w_s2_ic_resp.be),

   .iq_disp        (iq_disp)
   );

endmodule // msrh_frontend

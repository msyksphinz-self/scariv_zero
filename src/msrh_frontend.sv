module msrh_frontend
(
 input logic i_clk,
 input logic i_reset_n,

 l2_req_if.master ic_l2_req,
 l2_resp_if.slave ic_l2_resp,

 // PC Update from Committer
 input msrh_pkg::commit_blk_t i_commit,

 // Dispatch Info
 disp_if.master s3_disp
);

// ==============
// s0 stage
// ==============

logic        r_s0_valid;
logic [riscv_pkg::VADDR_W-1:0] r_s0_vaddr;

msrh_lsu_pkg::tlb_req_t           w_s0_tlb_req;
msrh_lsu_pkg::tlb_resp_t          w_s0_tlb_resp;
msrh_lsu_pkg::ic_req_t            w_s0_ic_req;
logic                          w_s0_ic_ready;


// ==============
// s1 stage
// ==============

logic [riscv_pkg::PADDR_W-1:0] r_s1_paddr;
logic                          r_s1_tlb_miss;

// ==============
// s2 stage
// ==============

msrh_lsu_pkg::ic_resp_t w_s2_ic_resp;
logic                          w_s2_ic_miss;
logic [riscv_pkg::VADDR_W-1: 0] w_s2_ic_miss_vaddr;


// ==============
// Commiter PC
// ==============
logic                           w_commit_upd_pc;
logic                           r_new_commit_upd_pc_wait_vld;
logic [riscv_pkg::VADDR_W-1: 0] r_new_commit_upd_pc;

logic                           r_ic_resp_would_be_killed;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s0_valid <= 1'b0;
    /* verilator lint_off WIDTH */
    r_s0_vaddr <= msrh_pkg::PC_INIT_VAL;
  end else begin
    r_s0_valid <= 1'b1;
    if (w_s2_ic_miss) begin
      r_s0_vaddr <= w_s2_ic_miss_vaddr;
    end else if (w_s0_ic_ready & w_s0_ic_req.valid) begin
      if (r_new_commit_upd_pc_wait_vld) begin
        r_s0_vaddr <= r_new_commit_upd_pc;
      end else if (w_commit_upd_pc) begin
        r_s0_vaddr <= i_commit.upd_pc_vaddr;
      end else begin
        r_s0_vaddr <= r_s0_vaddr + (1 << $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W));
      end
    end
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign w_commit_upd_pc = i_commit.commit & i_commit.upd_pc_vld;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_new_commit_upd_pc_wait_vld <= 1'b0;
    r_new_commit_upd_pc          <= 'h0;

    r_ic_resp_would_be_killed    <= 1'b0;
  end else begin
    if (w_commit_upd_pc & !w_s0_ic_ready) begin
      r_new_commit_upd_pc_wait_vld <= 1'b1;
      r_new_commit_upd_pc          <= i_commit.upd_pc_vaddr;
    end else if (w_s0_ic_ready) begin
      r_new_commit_upd_pc_wait_vld <= 1'b0;
    end

    if (w_commit_upd_pc & !w_s0_ic_ready) begin
      r_ic_resp_would_be_killed    <= 1'b1;
    end else if (w_s2_ic_resp.valid) begin
      r_ic_resp_would_be_killed    <= 1'b0;
    end
  end
end

assign w_s0_tlb_req.vaddr = r_s0_vaddr;
assign w_s0_tlb_req.cmd   = msrh_lsu_pkg::M_XRD;

tlb u_tlb
  (
   .i_clk      (i_clk),
   .i_reset_n  (i_reset_n),

   .i_tlb_req  (w_s0_tlb_req ),
   .o_tlb_resp (w_s0_tlb_resp),

   .o_tlb_update ()
   );

// s0 --> s1
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_paddr <= 'h0;
    r_s1_tlb_miss <= 'h0;
  end else begin
    r_s1_paddr <= w_s0_tlb_resp.paddr;
    r_s1_tlb_miss <= w_s0_tlb_resp.miss;
  end
end

assign w_s0_ic_req.valid = r_s0_valid & w_s0_ic_ready;
assign w_s0_ic_req.vaddr = r_s0_vaddr;

msrh_icache u_msrh_icache
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

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

   .i_inst_vld (w_s2_ic_resp.valid & !r_ic_resp_would_be_killed),

   .o_inst_rdy     (),
   .i_inst_pc      (w_s2_ic_resp.addr),
   .i_inst_in      (w_s2_ic_resp.data),
   .i_inst_byte_en (w_s2_ic_resp.be),

   .o_inst_buf_valid ( s3_disp.valid   ),
   .o_inst_pc        ( s3_disp.pc_addr ),
   .o_inst_buf       ( s3_disp.inst    ),
   .i_inst_buf_ready ( s3_disp.ready   )
   );

endmodule // msrh_frontend

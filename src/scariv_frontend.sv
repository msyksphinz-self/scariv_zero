// ------------------------------------------------------------------------
// NAME : scariv_frontend
// TYPE : module
// ------------------------------------------------------------------------
// Frontend Instruction Fetcher and Predictor
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_frontend
  import scariv_pkg::*;
  import scariv_ic_pkg::*;
  import scariv_predict_pkg::*;
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
 commit_if.monitor commit_in_if,
 // Branch Tag Update Signal
 br_upd_if.slave              br_upd_if,

 /* CSR information */
 csr_info_if.slave           csr_info,
 /* Interrupt Request information */
 interrupt_if.slave          int_if,

 // Dispatch Info
 scariv_front_if.master    ibuf_front_if,

 // Page Table Walk I/O
 tlb_ptw_if.master ptw_if
);

// ==============
// f0 stage
// ==============

typedef enum logic {
  INIT = 0,
  FETCH_REQ = 1
} if_sm_t;

if_sm_t  w_if_state_next;

logic                     r_f0_valid;
logic                     r_f0_valid_d1;
vaddr_t                   r_f0_vaddr;
vaddr_t                   w_f0_vaddr_next;
vaddr_t                   w_f0_vaddr;
logic                     w_f0_predicted;
scariv_lsu_pkg::tlb_req_t   w_f0_tlb_req;
scariv_lsu_pkg::tlb_resp_t  w_f0_tlb_resp;
ic_req_t                  w_f0_ic_req;
logic                     w_f0_ic_ready;
vaddr_t                   w_f0_vaddr_flush_next;

// ==============
// f1 stage
// ==============

logic    r_f1_valid;
logic    w_f1_inst_valid;
logic    r_f1_clear;
logic    r_f1_predicted;
vaddr_t  r_f1_vaddr;
paddr_t  r_f1_paddr;
logic    r_f1_tlb_miss;
logic    r_f1_tlb_except_valid;
except_t r_f1_tlb_except_cause;

logic    w_f1_predict_valid;
vaddr_t  w_f1_btb_target_vaddr;

logic    w_f1_ubtb_predict_valid;
ubtb_search_if  w_f1_ubtb_predict_if();
logic                           r_f2_ubtb_predict_valid;
scariv_predict_pkg::ubtb_info_t r_f2_ubtb_info;

// ==============
// f2 stage
// ==============

logic             w_f2_inst_valid;
logic             r_f2_valid;
logic             r_f2_clear;
logic             r_f2_predicted;
vaddr_t           r_f2_vaddr;
ic_resp_t         w_f2_ic_resp;
logic             r_f2_tlb_miss;
logic             r_f2_tlb_except_valid;
except_t          r_f2_tlb_except_cause;

logic             w_f2_predict_valid;
vaddr_t           w_f2_predict_target_vaddr;
logic             w_f2_predict_valid_gshare;
vaddr_t           w_f2_predict_target_vaddr_gshare;
logic             w_f2_btb_predict_match;
logic             w_f2_btb_predict_not_match;

logic             w_f2_inst_buffer_load_valid;

// =======================
// Predictors
// =======================

btb_update_if w_btb_update_if ();
btb_search_if w_btb_search_if ();

bim_update_if w_bim_update_if ();
bim_search_if w_bim_search_if ();

ras_search_if w_ras_search_if ();

gshare_search_if w_gshare_search_if ();

decode_flush_t   w_decode_flush;
logic   w_iq_predict_valid;
vaddr_t w_iq_predict_target_vaddr;
logic   r_iq_predict_flush;

`ifdef SIMULATION
paddr_t  sim_r_f2_paddr;
`endif // SIMULATION
logic r_f0_int_flush;
logic w_f0_int_flush_next;
logic w_f0_int_inserted;
logic r_f1_int_inserted;
logic r_f2_int_inserted;

// ==============
// TLB
// ==============
logic    w_tlb_ready;

// ==============
// Commiter PC
// ==============
logic    w_commit_flush;
logic    w_br_flush;
logic    w_br_fe_flush;
logic    w_flush_valid;
logic    w_int_flush_valid;
logic    r_int_flush_valid;

logic    w_flush_valid_next;
cmt_id_t w_flush_cmt_id_next;
grp_id_t w_flush_grp_id_next;

logic    w_inst_buffer_ready;
logic    w_f0_req_ready;
assign w_f0_req_ready = w_f0_ic_ready & w_tlb_ready;

scariv_front_addr_gen
u_addr_gen
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .commit_in_if (commit_in_if),
   .br_upd_if (br_upd_if),

   .csr_info (csr_info),

   .i_f0_req_ready    (w_f0_req_ready       ),
   .i_f0_vaddr        (r_f0_vaddr           ),
   .o_int_flush_valid (w_int_flush_valid    ),
   .o_vaddr           (w_f0_vaddr_flush_next)
   );


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f0_valid    <= 1'b0;
    r_f0_valid_d1 <= 1'b0;
    r_f0_vaddr <= PC_INIT_VAL;
  end else begin
    r_f0_valid     <= 1'b1;
    r_f0_valid_d1  <= r_f0_valid;
    r_f0_vaddr     <= w_f0_vaddr_next;
    r_f0_int_flush <= w_f0_int_flush_next;
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


logic w_f0_update_cond_0, w_f0_update_cond_1;
assign w_f0_update_cond_0 = (w_f0_ic_req.valid & w_f0_ic_ready & w_tlb_ready);
assign w_f0_update_cond_1 = w_if_state_next == FETCH_REQ;

logic w_f2_ic_miss_valid;
assign w_f2_ic_miss_valid = r_f2_valid & w_f2_ic_resp.miss & !r_f2_clear;


assign w_commit_flush  = scariv_pkg::is_flushed_commit(commit_in_if.commit_valid, commit_in_if.payload);

assign w_br_flush      = br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict;
assign w_flush_valid   = w_commit_flush | w_br_flush;

function automatic vaddr_t calc_next_cacheline (vaddr_t in);
  vaddr_t mask;
  mask = scariv_lsu_pkg::ICACHE_DATA_B_W;
  return w_f0_req_ready ? (in & ~(mask-1)) + mask : in;
endfunction // calc_next_cacheline

always_comb begin
  w_f0_int_inserted   = w_int_flush_valid;
  w_f0_int_flush_next = r_f0_int_flush;

  w_f0_predicted  = 1'b0;

  if (w_flush_valid) begin
    // Flush
    w_f0_vaddr      = w_f0_vaddr_flush_next;
    w_f0_vaddr_next = w_f0_vaddr_flush_next;  // In Flush, next cycle Cacheline read start.
  end else if (w_int_flush_valid) begin
    // Interrupt inserted
    w_f0_vaddr      = w_f0_vaddr_flush_next;
    w_f0_vaddr_next = calc_next_cacheline (w_f0_vaddr_flush_next);

  end else if (w_iq_predict_valid) begin
    // From Instruction Queue Stage: Prediction
    w_f0_predicted  = 1'b1;
    w_f0_vaddr      = w_iq_predict_target_vaddr;
    w_f0_vaddr_next = calc_next_cacheline (w_iq_predict_target_vaddr);

  end else if (r_f2_valid & ~r_f2_clear & (w_f2_ic_miss_valid | r_f2_tlb_miss)) begin
    // From Frontend Pipeline f2: hazard happend
    w_f0_vaddr      = r_f2_vaddr;
    w_f0_vaddr_next = calc_next_cacheline(r_f2_vaddr);
  end else if (r_f2_valid & !r_f2_clear & w_f2_ic_resp.valid & ~w_inst_buffer_ready) begin
    // Retry from F2 stage Vaddr
    w_f0_vaddr      = r_f2_vaddr;
    w_f0_vaddr_next = calc_next_cacheline(r_f2_vaddr); // r_f2_vaddr;
  end else if (r_f2_valid & ~r_f2_clear & w_f2_predict_valid) begin
    // F2 stage Prediction
    w_f0_predicted  = 1'b1;
    w_f0_vaddr      = w_f2_predict_target_vaddr;
    w_f0_vaddr_next = calc_next_cacheline(w_f2_predict_target_vaddr);
  end else if (r_f1_valid & ~r_f1_clear & w_f1_predict_valid & w_f1_ubtb_predict_if.ubtb_info.taken) begin
    // F1 stage Prediction
    w_f0_vaddr      = w_f1_ubtb_predict_if.ubtb_info.target_vaddr;
    w_f0_vaddr_next = calc_next_cacheline(w_f1_ubtb_predict_if.ubtb_info.target_vaddr);
  end else if (~w_f0_req_ready) begin
    // Resource Not available
    w_f0_vaddr      = r_f0_vaddr;
    w_f0_vaddr_next = calc_next_cacheline(r_f0_vaddr);
  end else if (r_f0_valid & ~r_f0_valid_d1) begin
    w_f0_vaddr      = PC_INIT_VAL;
    w_f0_vaddr_next = calc_next_cacheline(PC_INIT_VAL);
  end else begin
    // Normal Update
    w_f0_vaddr      = r_f0_vaddr;
    w_f0_vaddr_next = calc_next_cacheline(r_f0_vaddr);
  end
end // always_comb

assign w_f0_tlb_req.valid = w_f0_ic_req.valid;
assign w_f0_tlb_req.vaddr = w_f0_vaddr;
assign w_f0_tlb_req.cmd   = scariv_lsu_pkg::M_XRD;
assign w_f0_tlb_req.size  = 'h0;
assign w_f0_tlb_req.passthrough  = 1'b0;

logic w_f0_tlb_resp_miss;

tlb u_tlb
  (
   .i_clk      (i_clk),
   .i_reset_n  (i_reset_n),

   .i_kill (1'b0),
   .sfence_if(sfence_if),

   .i_csr_update(csr_info.update),
   .i_status_prv(csr_info.priv),
   .i_csr_status(csr_info.mstatus),
   .i_csr_satp(csr_info.satp),
   .ptw_if(ptw_if),

   .i_tlb_req   (w_f0_tlb_req ),
   .o_tlb_ready (w_tlb_ready  ),
   .o_tlb_resp  (w_f0_tlb_resp),

   .o_tlb_update (),
   .o_tlb_resp_miss (w_f0_tlb_resp_miss)
   );

// f0 --> f1
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f1_valid            <= 1'b0;
    r_f1_clear            <= 1'b0;
    r_f1_predicted        <= 1'b0;
    r_f1_vaddr            <= 'h0;
    r_f1_paddr            <= 'h0;
    r_f1_tlb_miss         <= 'h0;
    r_f1_tlb_except_valid <= 1'b0;
  end else begin
    r_f1_valid            <= r_f0_valid & w_f0_ic_req.valid & w_f0_req_ready;
    /* r_f1_clear            <= ~w_flush_valid & w_f2_inst_buffer_load_valid & ~w_inst_buffer_ready &
                             ~w_iq_predict_valid; */
    r_f1_clear            <= 1'b0;
    r_f1_predicted        <= w_f0_predicted;
    r_f1_vaddr            <= w_f0_vaddr;
    r_f1_int_inserted     <= w_f0_int_inserted | r_f0_int_flush;
    r_f1_paddr            <= w_f0_tlb_resp.paddr;
    r_f1_tlb_miss         <= w_f0_tlb_resp_miss & r_f0_valid & w_f0_ic_req.valid;
    r_f1_tlb_except_valid <= w_f0_tlb_resp.pf.inst |
                             w_f0_tlb_resp.ae.inst |
                             w_f0_tlb_resp.ma.inst;
    r_f1_tlb_except_cause <= w_f0_tlb_resp.pf.inst ? INST_PAGE_FAULT :
                             w_f0_tlb_resp.ae.inst ? INST_ACC_FAULT  :
                             INST_ADDR_MISALIGN;  // w_f0_tlb_resp.ma.inst
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


// f1 --> f2
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_f2_valid            <= 1'b0;
    r_f2_clear            <= 1'b0;
    r_f2_vaddr            <= 'h0;
    r_f2_predicted        <= 1'b0;
    r_f2_tlb_miss         <= 1'b0;
    r_f2_tlb_except_valid <= 1'b0;
    r_f2_tlb_except_cause <= except_t'(0);
    r_f2_int_inserted     <= 1'b0;
`ifdef SIMULATION
    sim_r_f2_paddr            <= 'h0;
`endif // SIMULATION
  end else begin // if (!i_reset_n)
    r_f2_valid              <= r_f1_valid & ~w_f2_ic_miss_valid;
    r_f2_clear              <= r_f1_clear | w_int_flush_valid | w_flush_valid | w_iq_predict_valid |
                               w_f2_predict_valid & (~r_f1_predicted | w_f2_btb_predict_not_match) |
                               ~w_flush_valid & w_f2_inst_buffer_load_valid & ~w_inst_buffer_ready;
    r_f2_predicted          <= r_f1_predicted;
    r_f2_vaddr              <= r_f1_vaddr;
    r_f2_tlb_miss           <= r_f1_tlb_miss;
    r_f2_tlb_except_valid   <= w_flush_valid ? 1'b0 : r_f1_tlb_except_valid;
    r_f2_tlb_except_cause   <= r_f1_tlb_except_cause;
    r_f2_int_inserted       <= r_f1_int_inserted;

    r_f2_ubtb_predict_valid <= w_f1_ubtb_predict_if.predict_valid;
    r_f2_ubtb_info          <= w_f1_ubtb_predict_if.ubtb_info;

`ifdef SIMULATION
    sim_r_f2_paddr <= r_f1_paddr;
`endif // SIMULATION
  end
end


// assign w_f0_ic_req.valid = (r_if_state != INIT) & (w_if_state_next == FETCH_REQ);
assign w_f0_ic_req.valid = r_f0_valid & !w_flush_valid & w_tlb_ready;

assign w_f0_ic_req.vaddr = w_f0_vaddr;

assign w_f2_inst_valid = w_f2_ic_resp.valid & r_f2_valid & !r_f2_clear & !r_f2_tlb_miss & ~w_f2_ic_resp.miss;
assign w_f1_inst_valid =                      r_f1_valid & !r_f1_clear & !r_f1_tlb_miss;

scariv_icache u_scariv_icache
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   // flushing is first entry is enough, other killing time, no need to flush
   .i_flush_valid (w_flush_valid),

   .i_fence_i (i_fence_i | sfence_if.valid),

   .i_f0_req (w_f0_ic_req),
   .o_f0_ready(w_f0_ic_ready),


   .i_f1_paddr (r_f1_paddr),
   .i_f1_kill  (r_f1_tlb_miss | r_f2_tlb_miss | r_f1_tlb_except_valid),

   .o_f2_resp (w_f2_ic_resp),

   .ic_l2_req  (ic_l2_req ),
   .ic_l2_resp (ic_l2_resp)
   );

assign w_f2_inst_buffer_load_valid = w_f2_inst_valid  | (r_f2_valid & ~r_f2_clear & ~r_f2_tlb_miss & r_f2_tlb_except_valid);

`ifdef SIMULATION
paddr_t w_f2_ic_resp_debug_addr;
assign w_f2_ic_resp_debug_addr = {w_f2_ic_resp.vaddr, 1'b0};
`endif // SIMULATION
inst_buffer_in_t w_f2_inst_buffer_in;
assign w_f2_inst_buffer_in.valid            = w_f2_inst_buffer_load_valid;
assign w_f2_inst_buffer_in.pc               = w_f2_ic_resp.vaddr;
assign w_f2_inst_buffer_in.inst             = w_f2_ic_resp.data;
`ifdef SIMULATION
assign w_f2_inst_buffer_in.pc_dbg           = {w_f2_ic_resp.vaddr, 1'b0};
`endif // SIMULATION
assign w_f2_inst_buffer_in.int_inserted = r_f2_int_inserted;
assign w_f2_inst_buffer_in.byte_en          = w_f2_ic_resp.be;
assign w_f2_inst_buffer_in.tlb_except_valid = r_f2_tlb_except_valid;
assign w_f2_inst_buffer_in.tlb_except_cause = r_f2_tlb_except_cause;


scariv_inst_buffer
u_scariv_inst_buffer
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),
   // flushing is first entry is enough, other killing time, no need to flush
   .i_flush_valid (w_flush_valid | r_iq_predict_flush),

   .csr_info      (csr_info),

   .bim_search_if    (w_bim_search_if   ),
   .btb_search_if    (w_btb_search_if   ),
   .ras_search_if    (w_ras_search_if   ),
   .gshare_search_if (w_gshare_search_if),

   .i_f2_ubtb_predict_valid (r_f2_ubtb_predict_valid & ~w_f2_btb_predict_not_match),
   .i_f2_ubtb_info          (r_f2_ubtb_info),

   .o_inst_ready (w_inst_buffer_ready),
   .i_f2_inst    (w_f2_inst_buffer_in),

   .o_decode_flush (w_decode_flush),

   .ibuf_front_if(ibuf_front_if),
   .br_upd_if (br_upd_if)
   );


// =======================
// Predictors
// =======================
assign w_btb_search_if.f0_valid       = w_f0_ic_req.valid;
assign w_btb_search_if.f0_pc_vaddr    = w_f0_vaddr;

assign w_btb_update_if.valid          = br_upd_if.update &
                                        ~br_upd_if.dead;
assign w_btb_update_if.taken          = br_upd_if.taken;
assign w_btb_update_if.mispredict     = br_upd_if.mispredict;
assign w_btb_update_if.pc_vaddr       = br_upd_if.pc_vaddr;
assign w_btb_update_if.target_vaddr   = br_upd_if.target_vaddr;
assign w_btb_update_if.is_cond        = br_upd_if.is_cond;
assign w_btb_update_if.is_call        = br_upd_if.is_call;
assign w_btb_update_if.is_ret         = br_upd_if.is_ret;
assign w_btb_update_if.is_rvc         = br_upd_if.is_rvc;

assign w_bim_search_if.f0_valid       = w_f0_ic_req.valid;
assign w_bim_search_if.f0_pc_vaddr    = w_f0_vaddr;

assign w_bim_update_if.valid          = br_upd_if.update & ~br_upd_if.dead;
assign w_bim_update_if.pc_vaddr       = br_upd_if.pc_vaddr;
assign w_bim_update_if.hit            = ~br_upd_if.mispredict;
assign w_bim_update_if.taken          = br_upd_if.taken;
assign w_bim_update_if.bim_value      = br_upd_if.bim_value;
assign w_bim_update_if.is_rvc         = br_upd_if.is_rvc;

assign w_gshare_search_if.f0_valid    = w_f0_ic_req.valid;
assign w_gshare_search_if.f0_pc_vaddr = w_f0_vaddr;

ic_block_t w_f2_btb_gshare_hit_array_tree;
ic_block_t w_f2_call_ret_tree;
assign w_f2_btb_gshare_hit_array_tree = 'h0;
bit_tree_lsb #(.WIDTH(scariv_lsu_pkg::ICACHE_DATA_B_W/2)) s2_call_ret_tree_lsb (.in(w_ras_search_if.f2_is_call | w_ras_search_if.f2_is_ret), .out(w_f2_call_ret_tree));

assign w_f1_predict_valid = r_f1_valid & ~r_f1_clear & w_f1_ubtb_predict_if.predict_valid;

assign w_f2_predict_valid        = r_f2_valid & ~r_f2_clear & w_f2_predict_valid_gshare & ~w_f2_btb_predict_match;
assign w_f2_predict_target_vaddr = w_f2_predict_target_vaddr_gshare;

assign w_f2_btb_predict_match = w_f2_predict_valid_gshare & r_f2_ubtb_predict_valid & r_f2_ubtb_info.taken &
                                (w_f2_predict_target_vaddr_gshare == r_f2_ubtb_info.target_vaddr);
assign w_f2_btb_predict_not_match = w_f2_predict_valid_gshare & r_f2_ubtb_predict_valid &
                                    (w_f2_predict_target_vaddr_gshare != r_f2_ubtb_info.target_vaddr);

// ------------------------------
// Decode Level Prediction Valid
// ------------------------------
assign w_iq_predict_valid        = ibuf_front_if.valid & ibuf_front_if.ready & w_decode_flush.valid;
assign w_iq_predict_target_vaddr = w_decode_flush.pred_vaddr;

// 1-cycle Later, it flushes pipeline
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_iq_predict_flush <= 1'b0;
  end else begin
    r_iq_predict_flush <= w_iq_predict_valid;
  end
end



scariv_predictor_gshare u_predictor
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_f0_valid   (w_f0_ic_req.valid),
   .i_f0_vaddr   (w_f0_ic_req.vaddr),

   .i_f1_valid   (w_f1_inst_valid),
   .i_f2_valid   (w_f2_inst_valid & w_inst_buffer_ready),

   .i_f2_ic_resp (w_f2_ic_resp),

   .update_btb_if     (w_btb_update_if),
   .search_btb_if     (w_btb_search_if),
   .search_btb_mon_if (w_btb_search_if),
   .o_f1_btb_target_vaddr (w_f1_btb_target_vaddr),

   .ras_search_if (w_ras_search_if),

   .gshare_search_if (w_gshare_search_if),

   .f1_ubtb_predict_if (w_f1_ubtb_predict_if),

   .o_f2_predict_valid        (w_f2_predict_valid_gshare       ),
   .o_f2_predict_target_vaddr (w_f2_predict_target_vaddr_gshare),

   .br_upd_if (br_upd_if)
   );

endmodule // scariv_frontend

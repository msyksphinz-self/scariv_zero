// ------------------------------------------------------------------------
// NAME : scariv_vec_lsu
// TYPE : module
// ------------------------------------------------------------------------
// Vector LSU top module
// ------------------------------------------------------------------------
// Scheduler, Vector LSU Pipeline
// Input : Distpached instruction
// Output: Calculation result
// ------------------------------------------------------------------------

module scariv_vec_lsu #(
    parameter PORT_BASE = 0
) (
    input logic i_clk,
    input logic i_reset_n,

   /* CSR information */
   csr_info_if.slave  csr_info,
   /* SFENCE update information */
   sfence_if.slave    sfence_if,
   /* ROB notification interface */
   rob_info_if.slave  rob_info_if,
   /* Page Table Walk I/O */
   tlb_ptw_if.master  ptw_if,

   input scariv_pkg::grp_id_t      disp_valid,
   scariv_front_if.watch           disp,
   vlvtype_info_if.monitor         vlvtype_info_if,
   vlvtype_upd_if.slave            vlvtype_upd_if,

   cre_ret_if.slave             cre_ret_if,

   regread_if.master            ex1_xpr_regread_rs1,

   /* Forwarding path */
   input scariv_pkg::phy_wr_t   i_phy_wr [scariv_pkg::TGT_BUS_SIZE],

   // --------------------
   // To Scalar Interface
   // --------------------
   l1d_rd_if.master             l1d_rd_if,
   l1d_missu_if.master          l1d_missu_if,
   input scariv_lsu_pkg::missu_resolve_t i_missu_resolve,

   /* read output */
   vec_regread_if.master  vec_phy_rd_if[3],
   vec_regread_if.master  vec_phy_old_wr_if,
   /* write output */
   vec_regwrite_if.master vec_phy_wr_if,
   // Vector Forwarding Notification Path
   vec_phy_fwd_if.slave   vec_valu_phy_fwd_if[2],
   vec_phy_fwd_if.master  vec_vlsu_phy_fwd_if[1],

   output scariv_pkg::done_rpt_t o_done_report,
   // Commit notification
   input scariv_pkg::commit_blk_t i_commit,
   br_upd_if.slave                br_upd_if,

   st_buffer_if.master            st_buffer_if
);

localparam VEC_LSU_PORT_SIZE = scariv_conf_pkg::VLSU_DISP_SIZE;

scariv_pkg::disp_t            w_disp_inst[scariv_conf_pkg::DISP_SIZE];
scariv_pkg::disp_t            w_disp_picked_inst[VEC_LSU_PORT_SIZE];
logic [VEC_LSU_PORT_SIZE-1:0] w_disp_picked_inst_valid;
scariv_pkg::grp_id_t          w_disp_picked_grp_id[VEC_LSU_PORT_SIZE];
scariv_vec_pkg::issue_t       w_ex0_issue;
scariv_vec_pkg::issue_t       w_ex0_replay_issue;
scariv_vec_pkg::issue_t       w_issue_from_iss;
vec_phy_fwd_if                w_vec_phy_fwd_if[3]();
lsu_pipe_haz_if #(.T(scariv_vec_pkg::vlsu_replay_queue_t)) w_lsu_pipe_haz_if ();
lsu_pipe_req_if #(.T(scariv_vec_pkg::vlsu_replay_queue_t)) w_lsu_pipe_req_if ();
logic                         w_replay_selected;
logic                         w_replay_queue_full;

done_if                       w_ex3_done_if();

vlsu_lsq_req_if               w_vlsu_ldq_req_if();
vlsu_lsq_req_if               w_vlsu_stq_req_if();


scariv_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(VEC_LSU_PORT_SIZE)
    )
u_scariv_disp_pickup
  (
   .i_disp_valid (disp_valid),
   .i_disp       (disp),

   .o_disp_valid  (w_disp_picked_inst_valid),
   .o_disp        (w_disp_picked_inst),
   .o_disp_grp_id (w_disp_picked_grp_id)
   );

scariv_pkg::early_wr_t w_early_wr_zero[scariv_pkg::REL_BUS_SIZE];
generate for (genvar idx = 0; idx < scariv_pkg::REL_BUS_SIZE; idx++) begin : early_zero_fill
  assign w_early_wr_zero[idx] = 'h0;
end endgenerate

scariv_pkg::mispred_t  w_mispred_lsu[scariv_conf_pkg::LSU_INST_NUM];
generate for (genvar idx = 0; idx < scariv_conf_pkg::LSU_INST_NUM; idx++) begin : mispred_zero_fill
  assign w_mispred_lsu[idx] = 'h0;
end endgenerate

scariv_vlsu_issue_unit
  #(
    .ENTRY_SIZE  (scariv_conf_pkg::RV_VLSU_ENTRY_SIZE),
    .IN_PORT_SIZE(VEC_LSU_PORT_SIZE),
    .NUM_OPERANDS(3)
    )
u_issue_unit
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .rob_info_if (rob_info_if),

   .i_disp_valid(w_disp_picked_inst_valid),
   .i_cmt_id    (disp.payload.cmt_id),
   .i_grp_id    (w_disp_picked_grp_id),
   .i_disp_info (w_disp_picked_inst),
   .vlvtype_info_if (vlvtype_info_if),
   .vlvtype_upd_if  (vlvtype_upd_if),

   .cre_ret_if  (cre_ret_if),

   .i_stall    (w_lsu_pipe_req_if.valid & w_replay_selected),
   .i_replay_queue_full  (w_replay_queue_full ),

   .i_early_wr    (w_early_wr_zero),
   .i_phy_wr      (i_phy_wr),
   .i_mispred_lsu (w_mispred_lsu),
   .vec_phy_fwd_if (w_vec_phy_fwd_if),

   .o_issue(w_issue_from_iss),
   .o_iss_index_oh(),

   .i_commit      (i_commit),
   .br_upd_if     (br_upd_if)
   );


logic w_replay_selected_next;
logic r_replay_selected;
logic r_replay_selected_lock;
assign w_replay_selected_next = w_lsu_pipe_req_if.valid & ~w_issue_from_iss.valid ? 1'b1 :
                                ~w_lsu_pipe_req_if.valid & w_issue_from_iss.valid ? 1'b0 :
                                w_replay_queue_full                               ? 1'b1 :
                                scariv_pkg::id0_is_older_than_id1 (w_lsu_pipe_req_if.cmt_id, w_lsu_pipe_req_if.grp_id,
                                                                   w_issue_from_iss.cmt_id, w_issue_from_iss.grp_id);
assign w_replay_selected = r_replay_selected_lock ? r_replay_selected : w_replay_selected_next;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_replay_selected <= 'h0;
    r_replay_selected_lock <= 1'b0;
  end else begin
    if ((scariv_vec_pkg::VEC_STEP_W > 1) &
        (w_ex0_replay_issue.valid & (w_ex0_replay_issue.vec_step_index == 'h0))) begin
      r_replay_selected <= w_replay_selected_next;
      r_replay_selected_lock <= 1'b1;
    end else if (w_ex0_replay_issue.valid & ((scariv_vec_pkg::VEC_STEP_W == 1) |
                                             (w_ex0_replay_issue.vec_step_index == scariv_vec_pkg::VEC_STEP_W-1))) begin
      r_replay_selected <= w_replay_selected_next;
      r_replay_selected_lock <= 1'b0;
    end else if (!w_ex0_replay_issue.valid) begin
      r_replay_selected_lock <= 1'b0;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


assign w_lsu_pipe_req_if.ready = w_replay_selected;

always_comb begin
  if (w_replay_selected) begin
    w_ex0_replay_issue.valid             = w_lsu_pipe_req_if.valid       ;
    w_ex0_replay_issue.cmt_id            = w_lsu_pipe_req_if.cmt_id      ;
    w_ex0_replay_issue.grp_id            = w_lsu_pipe_req_if.grp_id      ;
    w_ex0_replay_issue.inst              = w_lsu_pipe_req_if.payload.inst        ;
    w_ex0_replay_issue.vlvtype           = w_lsu_pipe_req_if.payload.vlvtype     ;
    w_ex0_replay_issue.rd_regs[0]        = w_lsu_pipe_req_if.payload.rd_reg      ;
    w_ex0_replay_issue.wr_reg            = w_lsu_pipe_req_if.payload.wr_reg      ;
    w_ex0_replay_issue.wr_old_reg        = w_lsu_pipe_req_if.payload.wr_old_reg  ;
    w_ex0_replay_issue.cat               = w_lsu_pipe_req_if.payload.cat         ;
    w_ex0_replay_issue.vec_step_index    = w_lsu_pipe_req_if.payload.vec_step_index;
`ifdef SIMULATION
    w_ex0_replay_issue.kanata_id    = 'h0;  // w_lsu_pipe_req_if.kanata_id   ;
`endif // SIMULATION
  end else begin
    w_ex0_replay_issue = w_issue_from_iss;
  end
end // always_comb

assign w_vec_phy_fwd_if[1].valid   = vec_valu_phy_fwd_if[0].valid;
assign w_vec_phy_fwd_if[1].rd_rnid = vec_valu_phy_fwd_if[0].rd_rnid;
assign w_vec_phy_fwd_if[2].valid   = vec_valu_phy_fwd_if[1].valid;
assign w_vec_phy_fwd_if[2].rd_rnid = vec_valu_phy_fwd_if[1].rd_rnid;

scariv_vec_lsu_pipe
u_lsu_pipe
  (
   .i_clk    (i_clk),
   .i_reset_n(i_reset_n),

   .sfence_if (sfence_if),
   .csr_info  (csr_info),
   .ptw_if    (ptw_if),

   .i_commit  (i_commit),
   .br_upd_if (br_upd_if),

   .i_ex0_issue           (w_ex0_replay_issue             ),
   .i_ex0_replay_selected (w_replay_selected              ),
   .i_ex0_replay_haz_1st_req (w_lsu_pipe_req_if.payload.haz_1st_req),
   .i_ex0_replay_paddr    (w_lsu_pipe_req_if.payload.paddr),

   .ex1_i_phy_wr(i_phy_wr),

   .ex0_xpr_regread_rs1(ex1_xpr_regread_rs1),

   .vec_phy_rd_if (vec_phy_rd_if[0:1]),
   .vec_phy_old_wr_if (vec_phy_old_wr_if),
   .vec_phy_wr_if (vec_phy_wr_if),
   .vec_phy_fwd_if (w_vec_phy_fwd_if[0:0]),

   .o_tlb_resolve (),
   .i_replay_queue_full (w_replay_queue_full),

   .l1d_rd_if    (l1d_rd_if),
   .l1d_missu_if (l1d_missu_if),

   .lsu_pipe_haz_if (w_lsu_pipe_haz_if),

   .vlsu_ldq_req_if (w_vlsu_ldq_req_if),
   .vlsu_stq_req_if (w_vlsu_stq_req_if),

   .o_done_report (o_done_report)
   );


assign vec_vlsu_phy_fwd_if[0].valid   = w_vec_phy_fwd_if[0].valid;
assign vec_vlsu_phy_fwd_if[0].rd_rnid = w_vec_phy_fwd_if[0].rd_rnid;

scariv_lsu_pkg::missu_resolve_t r_missu_resolve_d1;
always_ff @ (posedge i_clk) begin
  r_missu_resolve_d1.valid <= i_missu_resolve.valid;
  r_missu_resolve_d1.resolve_index_oh <= i_missu_resolve.resolve_index_oh;
end
assign r_missu_resolve_d1.missu_entry_valids = i_missu_resolve.missu_entry_valids;

// Replay Queue
scariv_lsu_replay_queue
  #(.queue_base_t(scariv_vec_pkg::vlsu_replay_queue_t))
u_replay_queue
(
 .i_clk     (i_clk    ),
 .i_reset_n (i_reset_n),

 .i_commit  (i_commit),
 .br_upd_if (br_upd_if),

 .rob_info_if (rob_info_if),

 .lsu_pipe_haz_if (w_lsu_pipe_haz_if),

 .i_st_buffer_empty    (1'b0),
 .i_missu_is_empty     (1'b0),

 .i_missu_resolve   (r_missu_resolve_d1),
 .i_missu_is_full   (1'b0 ),
 .i_stq_rs2_resolve (1'b0),

 .o_full (w_replay_queue_full),

 .lsu_pipe_req_if (w_lsu_pipe_req_if)
);


scariv_vlsu_ldq
u_ldq
(
 .i_clk     (i_clk    ),
 .i_reset_n (i_reset_n),

 .vlsu_ldq_req_if (w_vlsu_ldq_req_if),
 .rob_info_if     (rob_info_if      ),
 .i_commit        (i_commit         ),
 .br_upd_if       (br_upd_if        )
);


scariv_vlsu_stq
u_stq
(
 .i_clk     (i_clk    ),
 .i_reset_n (i_reset_n),

 .vlsu_stq_req_if (w_vlsu_stq_req_if),
 .rob_info_if     (rob_info_if      ),
 .i_commit        (i_commit         ),
 .br_upd_if       (br_upd_if        ),
 .vec_vs3_rd_if   (vec_phy_rd_if[2] ),
 .st_buffer_if    (st_buffer_if     )
);




endmodule  // scariv_vec_lsu

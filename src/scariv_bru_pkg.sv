// ------------------------------------------------------------------------
// NAME :
// TYPE : package
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

package scariv_bru_pkg;

typedef struct packed {
  logic                  valid;
  scariv_pkg::vaddr_t    pc_addr;
  logic [riscv_pkg::VADDR_W-1: 1] basicblk_pc_vaddr;
  logic [31:0]           inst;
  decoder_inst_cat_pkg::inst_cat_t    cat;
  decoder_inst_cat_pkg::inst_subcat_t subcat;
  logic                  is_rvc;
  scariv_pkg::brtag_t    brtag;

  scariv_pkg::cmt_id_t   cmt_id;
  scariv_pkg::grp_id_t   grp_id;

  logic                  is_cond;
  logic                  is_call;
  logic                  is_ret;

  logic [scariv_pkg::RAS_W-1: 0] ras_index;
  logic                          pred_taken;
  scariv_pkg::gshare_bht_t       gshare_bhr;
  scariv_pkg::gshare_bht_t       gshare_index;
  logic [ 1: 0]                  bim_value;
  logic                          btb_valid;
  scariv_pkg::vaddr_t            pred_target_vaddr;

  scariv_pkg::reg_wr_issue_t         wr_reg;
  scariv_pkg::reg_rd_issue_t [ 2: 0] rd_regs;

`ifdef SIMULATION
  logic [63: 0]                     kanata_id;
`endif // SIMULATION
} issue_entry_t;


function issue_entry_t assign_issue_common (scariv_pkg::disp_t in,
                                            scariv_pkg::cmt_id_t cmt_id,
                                            scariv_pkg::grp_id_t grp_id,
                                            logic [riscv_pkg::VADDR_W-1:1] basicblk_pc_vaddr);
  issue_entry_t ret;

  ret.valid = in.valid;
  ret.inst = in.inst;
  ret.pc_addr = in.pc_addr;
  ret.basicblk_pc_vaddr = basicblk_pc_vaddr;

  ret.cat    = in.cat;
  ret.subcat = in.subcat;
  ret.is_rvc  = in.rvc_inst_valid;
  ret.brtag   = in.brtag;

  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;

  ret.is_cond          = in.is_cond;
  ret.is_call          = in.is_call;
  ret.is_ret           = in.is_ret;
  ret.gshare_bhr       = in.gshare_bhr;
  ret.gshare_index     = in.gshare_index;
  ret.ras_index        = in.ras_index;
  ret.pred_taken       = in.pred_taken;
  ret.bim_value        = in.bim_value;
  ret.btb_valid        = in.btb_valid;
  ret.pred_target_vaddr = in.pred_target_vaddr;

  ret.wr_reg.valid = in.wr_reg.valid;
  ret.wr_reg.typ = in.wr_reg.typ;
  ret.wr_reg.regidx = in.wr_reg.regidx;
  ret.wr_reg.rnid = in.wr_reg.rnid;

`ifdef SIMULATION
  ret.kanata_id = in.kanata_id;
`endif // SIMULATION
  return ret;

endfunction // assign_issue_common

function issue_entry_t assign_bru_issue (scariv_pkg::disp_t in,
                                         scariv_pkg::cmt_id_t cmt_id,
                                         scariv_pkg::grp_id_t grp_id,
                                         logic [ 1: 0] rs_rel_hit, logic [ 1: 0] rs_phy_hit, logic [ 1: 0] rs_may_mispred, scariv_pkg::rel_bus_idx_t rs_rel_index[2],
                                         logic [riscv_pkg::VADDR_W-1:1]  i_basicblk_pc_vaddr);
  issue_entry_t ret;
  ret = assign_issue_common (in, cmt_id, grp_id, i_basicblk_pc_vaddr);

  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
    ret.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[0] = rs_rel_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[1] = 1'b0;
    if (ret.rd_regs[rs_idx].predict_ready[0]) begin
      ret.rd_regs[rs_idx].early_index = rs_rel_index[rs_idx];
    end
  end

  for (int rs_idx = 2; rs_idx < 3; rs_idx++) begin
    ret.rd_regs[rs_idx].valid = 1'b0;
  end

  return ret;

endfunction  // assign_issue_entry_t


endpackage // scariv_bru_pkg

interface br_upd_if;

  logic                                update;
  logic                                taken;
  logic                                mispredict;
  logic                                is_cond;
  logic                                is_call;
  logic                                is_ret;
  logic                                is_rvc;
  logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] ras_index;
  logic [ 1: 0]                        bim_value;
  scariv_pkg::vaddr_t                    pc_vaddr;
  logic [riscv_pkg::VADDR_W-1:1]         basicblk_pc_vaddr;
  scariv_pkg::vaddr_t                    target_vaddr;
  scariv_pkg::vaddr_t                    ras_prev_vaddr;
`ifdef SIMULATION
  scariv_pkg::vaddr_t                    pred_vaddr;
`endif // SIMULATION
  logic                                  dead;
  scariv_pkg::cmt_id_t                   cmt_id;
  scariv_pkg::grp_id_t                   grp_id;
  (* mark_debug="true" *) (* dont_touch="yes" *) scariv_pkg::brtag_t                    brtag;

  logic [scariv_pkg::GSHARE_BHT_W-1: 0] gshare_index;
  logic [scariv_pkg::GSHARE_BHT_W-1: 0] gshare_bhr;
  logic                                 btb_not_hit;

  modport master (
    output update,
    output taken,
    output mispredict,
    output is_cond,
    output is_call,
    output is_ret,
    output is_rvc,
    output ras_index,
    output bim_value,
    output dead,
    output pc_vaddr,
    output basicblk_pc_vaddr,
    output target_vaddr,
    output ras_prev_vaddr,
`ifdef SIMULATION
    output pred_vaddr,
`endif // SIMULATION
    output cmt_id,
    output grp_id,
    output brtag,
    output gshare_index,
    output gshare_bhr,
    output btb_not_hit
  );

  modport slave (
    input update,
    input taken,
    input mispredict,
    input is_cond,
    input is_call,
    input is_ret,
    input is_rvc,
    input ras_index,
    input bim_value,
    input dead,
    input pc_vaddr,
    input basicblk_pc_vaddr,
    input target_vaddr,
    input ras_prev_vaddr,
`ifdef SIMULATION
    input pred_vaddr,
`endif // SIMULATION
    input cmt_id,
    input grp_id,
    input brtag,
    input gshare_index,
    input gshare_bhr,
    input btb_not_hit
  );

endinterface // br_upd_if


module br_upd_if_buf
  (
   br_upd_if.slave  slave_if,
   br_upd_if.master master_if
   );

assign master_if.update         = slave_if.update         ;
assign master_if.taken          = slave_if.taken          ;
assign master_if.mispredict     = slave_if.mispredict     ;
assign master_if.is_cond        = slave_if.is_cond        ;
assign master_if.is_call        = slave_if.is_call        ;
assign master_if.is_ret         = slave_if.is_ret         ;
assign master_if.is_rvc         = slave_if.is_rvc         ;
assign master_if.ras_index      = slave_if.ras_index      ;
assign master_if.bim_value      = slave_if.bim_value      ;
assign master_if.pc_vaddr       = slave_if.pc_vaddr       ;
assign master_if.basicblk_pc_vaddr = slave_if.basicblk_pc_vaddr;
assign master_if.target_vaddr   = slave_if.target_vaddr   ;
assign master_if.ras_prev_vaddr = slave_if.ras_prev_vaddr ;
`ifdef SIMULATION
assign master_if.pred_vaddr     = slave_if.pred_vaddr     ;
`endif // SIMULATION
assign master_if.dead           = slave_if.dead           ;
assign master_if.cmt_id         = slave_if.cmt_id         ;
assign master_if.grp_id         = slave_if.grp_id         ;
assign master_if.brtag          = slave_if.brtag          ;
assign master_if.gshare_index   = slave_if.gshare_index    ;
assign master_if.gshare_bhr     = slave_if.gshare_bhr      ;

endmodule // br_upd_if_buf


interface cmt_brtag_if;

  logic                    commit;
  scariv_pkg::cmt_id_t     cmt_id;
  scariv_pkg::grp_id_t     grp_id;
  scariv_pkg::vaddr_t      pc_vaddr;
  scariv_pkg::grp_id_t     is_br_inst;
  logic [scariv_conf_pkg::DISP_SIZE-1: 0][$clog2(scariv_conf_pkg::RV_BRU_ENTRY_SIZE)-1: 0] brtag;
  scariv_pkg::gshare_bht_t gshare_bhr;
  scariv_pkg::gshare_bht_t gshare_index;
  logic                    taken;
  logic                    btb_newly_allocated;
  logic                    mispredict;
  logic [ 1: 0]            bim_value;
  logic                    is_rvc;
  logic                    dead;

  modport master (
    output commit,
    output cmt_id,
    output grp_id,
    output pc_vaddr,
    output is_br_inst,
    output brtag,
    output gshare_bhr,
    output gshare_index,
    output taken,
    output btb_newly_allocated,
    output mispredict,
    output bim_value,
    output is_rvc,
    output dead
  );

  modport slave (
    input commit,
    input cmt_id,
    input grp_id,
    input pc_vaddr,
    input is_br_inst,
    input brtag,
    input gshare_bhr,
    input gshare_index,
    input taken,
    input btb_newly_allocated,
    input mispredict,
    input bim_value,
    input is_rvc,
    input dead
  );

endinterface // cmt_brtag_if

interface brtag_if;
  logic valid;
  scariv_pkg::brtag_t brtag;

  modport master (
    output valid,
    output brtag
  );

  modport slave (
    input valid,
    input brtag
  );
endinterface

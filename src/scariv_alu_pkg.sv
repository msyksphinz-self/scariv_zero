package scariv_alu_pkg;

typedef struct packed {
  logic        valid;

  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;

  scariv_pkg::reg_rd_issue_t [ 1: 0] rd_regs;

} iq_entry_t;

typedef struct packed {
  scariv_pkg::vaddr_t pc_addr;
  decoder_inst_cat_pkg::inst_cat_t cat;
  logic [31: 0]  inst;
  scariv_pkg::reg_wr_issue_t wr_reg;
`ifdef SIMULATION
  logic [63: 0]  kanata_id;
`endif // SIMULATION
} iq_payload_t;

typedef struct packed {
  logic    valid;

  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;

  scariv_pkg::reg_wr_issue_t wr_reg;
  scariv_pkg::reg_rd_issue_t [ 1: 0] rd_regs;

  scariv_pkg::vaddr_t        pc_addr;
  decoder_inst_cat_pkg::inst_cat_t cat;
  logic [31: 0]  inst;
`ifdef SIMULATION
  logic [63: 0]  kanata_id;
`endif // SIMULATION
} issue_t;

function automatic iq_entry_t assign_entry (scariv_pkg::cmt_id_t cmt_id, scariv_pkg::grp_id_t grp_id, scariv_pkg::disp_t in,
                                            logic [ 1: 0] rs_rel_hit, logic [ 1: 0] rs_phy_hit, logic [ 1: 0] rs_may_mispred, scariv_pkg::rel_bus_idx_t rs_rel_index[2]);
  iq_entry_t ret;
  ret.valid  = in.valid;

  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;

  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
    ret.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[0] = in.rd_regs[rs_idx].valid & rs_rel_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[1] = 1'b0;
    if (ret.rd_regs[rs_idx].predict_ready[0]) begin
      ret.rd_regs[rs_idx].early_index = rs_rel_index[rs_idx];
    end
  end // for (int rs_idx = 0; rs_idx < 2; rs_idx++)

  return ret;
endfunction // assign_entry


function automatic iq_payload_t assign_payload (scariv_pkg::disp_t in);
  iq_payload_t ret;
  ret.pc_addr   = in.pc_addr;
  ret.cat       = in.cat    ;
  ret.inst      = in.inst   ;
  ret.wr_reg.valid  = in.wr_reg.valid ;
  ret.wr_reg.typ    = in.wr_reg.typ   ;
  ret.wr_reg.regidx = in.wr_reg.regidx;
  ret.wr_reg.rnid   = in.wr_reg.rnid  ;

`ifdef SIMULATION
  ret.kanata_id = in.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_payload

function automatic issue_t assign_issue (iq_entry_t iq, iq_payload_t payload);
  issue_t ret;
  ret.valid   = iq.valid     ;

  ret.cmt_id  = iq.cmt_id    ;
  ret.grp_id  = iq.grp_id    ;

  ret.wr_reg  = payload.wr_reg;
  ret.rd_regs = iq.rd_regs    ;

  ret.pc_addr = payload.pc_addr   ;
  ret.cat     = payload.cat       ;
  ret.inst    = payload.inst      ;
`ifdef SIMULATION
  ret.kanata_id = payload.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_issue

endpackage // scariv_alu_pkg

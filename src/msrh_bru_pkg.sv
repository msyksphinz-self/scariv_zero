interface done_if #(parameter RV_ENTRY_SIZE=32);
logic          done;
logic [RV_ENTRY_SIZE-1: 0] index_oh;
logic                      except_valid;
msrh_pkg::except_t          except_type;
modport master(
  output done,
  output index_oh,
  output except_valid,
  output except_type
);

modport slave(
  input done,
  input index_oh,
  input except_valid,
  input except_type
);

endinterface // done_if


interface br_upd_if;

  logic                                update;
  logic                                mispredict;
  logic [ 1: 0]                        bim_value;
  logic [riscv_pkg::VADDR_W-1: 0]      pc_vaddr;
  logic [riscv_pkg::VADDR_W-1: 0]      target_vaddr;
  logic                                dead;
  logic [msrh_pkg::CMT_ID_W-1:0]       cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
  logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag;
  logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0]         br_mask;

  modport master (
    output update,
    output mispredict,
    output bim_value,
    output dead,
    output pc_vaddr,
    output target_vaddr,
    output cmt_id,
    output grp_id,
    output brtag,
    output br_mask
  );

  modport slave (
    input update,
    input mispredict,
    input bim_value,
    input dead,
    input pc_vaddr,
    input target_vaddr,
    input cmt_id,
    input grp_id,
    input brtag,
    input br_mask
  );

endinterface // br_upd_if


interface cmt_brtag_if;

  logic          commit;
  logic [msrh_conf_pkg::DISP_SIZE-1: 0] is_br_inst;
  logic [msrh_conf_pkg::DISP_SIZE-1: 0][$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1: 0] brtag;

  modport master (
    output commit,
    output is_br_inst,
    output brtag
  );

  modport slave (
    input commit,
    input is_br_inst,
    input brtag
  );

endinterface // cmt_brtag_if

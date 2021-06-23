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
  logic [riscv_pkg::VADDR_W-1: 0]      vaddr;
  logic [msrh_pkg::CMT_ID_W-1:0]       cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
  logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag;

  modport master (
    output update,
    output vaddr,
    output cmt_id,
    output grp_id,
    output brtag
  );

  modport slave (
    input update,
    input vaddr,
    input cmt_id,
    input grp_id,
    input brtag
  );

endinterface // br_upd_if

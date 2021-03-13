interface done_if #(parameter RV_ENTRY_SIZE=32);
logic          done;
logic [RV_ENTRY_SIZE-1: 0] index_oh;

modport master(
  output done,
  output index_oh
);

modport slave(
  input done,
  input index_oh
);

endinterface // done_if


interface br_upd_if;

  logic                                update;
  logic [riscv_pkg::VADDR_W-1: 0]      vaddr;
  logic [msrh_pkg::CMT_BLK_W-1:0]      cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;

  modport master (
    output update,
    output vaddr,
    output cmt_id,
    output grp_id
  );

  modport slave (
    input update,
    input vaddr,
    input cmt_id,
    input grp_id
  );

endinterface // br_upd_if

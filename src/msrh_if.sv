interface done_if #(parameter RV_ENTRY_SIZE=32,
                    parameter FPU_PIPE=1'b0);
logic                                done;
logic [RV_ENTRY_SIZE-1: 0]           index_oh;
msrh_pkg::done_payload_t             payload;

modport master(
  output done,
  output index_oh,
  output payload
);

modport slave(
  input done,
  input index_oh,
  input payload
);

endinterface // done_if



//
// ROB Information Notification IF
//  For oldest uncommitted, notification that is become oldest
//  and older instruction doesn't update PC
//
interface rob_info_if;

  msrh_pkg::cmt_id_t       cmt_id;
  msrh_pkg::grp_id_t grp_id;
  msrh_pkg::grp_id_t done_grp_id;
  msrh_pkg::grp_id_t upd_pc_valid;
  msrh_pkg::grp_id_t except_valid;

  modport master(
    output cmt_id,
    output grp_id,
    output done_grp_id,
    output upd_pc_valid,
    output except_valid
  );

  modport slave(
    input cmt_id,
    input grp_id,
    input done_grp_id,
    input upd_pc_valid,
    input except_valid
  );

endinterface // rob_info_if

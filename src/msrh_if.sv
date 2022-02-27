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

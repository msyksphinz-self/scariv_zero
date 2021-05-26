//
// ROB Information Notification IF
//  For oldest uncommitted, notification that is become oldest
//  and older instruction doesn't update PC
//
interface rob_info_if;

  logic [msrh_pkg::CMT_ID_W-1:0]       cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] done_grp_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] upd_pc_valid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] except_valid;

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

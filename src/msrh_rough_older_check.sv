module msrh_rough_older_check
  import decoder_lsu_ctrl_pkg::*;
  import msrh_lsu_pkg::*;
(
 input logic [msrh_pkg::CMT_BLK_W-1:0]      i_cmt_id0,
 input logic [msrh_conf_pkg::DISP_SIZE-1:0] i_grp_id0,

 input logic [msrh_pkg::CMT_BLK_W-1:0]      i_cmt_id1,
 input logic [msrh_conf_pkg::DISP_SIZE-1:0] i_grp_id1,

 output logic                               o_0_older_than_1
 );

logic                                       w_cmt_is_older;

assign w_cmt_is_older = i_cmt_id0[msrh_pkg::CMT_BLK_W-1] ^ i_cmt_id1[msrh_pkg::CMT_BLK_W-1] ?
                        i_cmt_id0 > i_cmt_id1 :
                        i_cmt_id0 < i_cmt_id1 ;
assign o_0_older_than_1 = w_cmt_is_older ||
                          (i_cmt_id0 == i_cmt_id1 && i_grp_id0 < i_grp_id1);

endmodule // msrh_rough_older_check

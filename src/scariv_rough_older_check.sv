module scariv_rough_older_check
  import decoder_lsu_ctrl_pkg::*;
  import scariv_lsu_pkg::*;
(
 input scariv_pkg::cmt_id_t i_cmt_id0,
 input scariv_pkg::grp_id_t i_grp_id0,

 input scariv_pkg::cmt_id_t i_cmt_id1,
 input scariv_pkg::grp_id_t i_grp_id1,

 output logic                               o_0_older_than_1
 );

logic                                       w_cmt_is_older;

assign w_cmt_is_older = i_cmt_id0[scariv_pkg::CMT_ID_W-1] ^ i_cmt_id1[scariv_pkg::CMT_ID_W-1] ?
                        i_cmt_id0[scariv_pkg::CMT_ID_W-2:0] > i_cmt_id1[scariv_pkg::CMT_ID_W-2:0] :
                        i_cmt_id0[scariv_pkg::CMT_ID_W-2:0] < i_cmt_id1[scariv_pkg::CMT_ID_W-2:0] ;
assign o_0_older_than_1 = w_cmt_is_older ||
                          (i_cmt_id0 == i_cmt_id1 && i_grp_id0 < i_grp_id1);

endmodule // scariv_rough_older_check

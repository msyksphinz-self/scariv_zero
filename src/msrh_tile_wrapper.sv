module msrh_tile_wrapper
(
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    output logic                                     o_ic_req_valid,
    output msrh_lsu_pkg::mem_cmd_t                   o_ic_req_cmd,
    output logic [riscv_pkg::PADDR_W-1:0]            o_ic_req_addr,
    output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    o_ic_req_tag,
    output logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   o_ic_req_data,
    output logic [msrh_lsu_pkg::ICACHE_DATA_W/8-1:0] o_ic_req_byte_en,
    input logic                                      i_ic_req_ready,

    input logic                                   i_ic_resp_valid,
    input logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]  i_ic_resp_tag,
    input logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0] i_ic_resp_data,
    output logic                                  o_ic_resp_ready,

    // L2 request from L1D
    output logic                                     o_l1d_req_valid,
    output msrh_lsu_pkg::mem_cmd_t                   o_l1d_req_cmd,
    output logic [riscv_pkg::PADDR_W-1:0]            o_l1d_req_addr,
    output logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]    o_l1d_req_tag,
    output logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0]   o_l1d_req_data,
    output logic [msrh_lsu_pkg::ICACHE_DATA_W/8-1:0] o_l1d_req_byte_en,
    input logic                                      i_l1d_req_ready,

    input logic                                   i_l1d_resp_valid,
    input logic [msrh_lsu_pkg::L2_CMD_TAG_W-1:0]  i_l1d_resp_tag,
    input logic [msrh_lsu_pkg::ICACHE_DATA_W-1:0] i_l1d_resp_data,
    output logic                                  o_l1d_resp_ready
);

    l2_req_if  ic_l2_req  ();
    l2_resp_if ic_l2_resp ();

    l2_req_if  l1d_l2_req  ();
    l2_resp_if l1d_l2_resp ();

    assign o_ic_req_valid   = ic_l2_req.valid          ;
    assign o_ic_req_cmd     = ic_l2_req.payload.cmd    ;
    assign o_ic_req_addr    = ic_l2_req.payload.addr   ;
    assign o_ic_req_tag     = ic_l2_req.payload.tag    ;
    assign o_ic_req_data    = ic_l2_req.payload.data   ;
    assign o_ic_req_byte_en = ic_l2_req.payload.byte_en;
    assign ic_l2_req.ready  = i_ic_req_ready        ;

    assign ic_l2_resp.valid        = i_ic_resp_valid ;
    assign ic_l2_resp.payload.tag  = i_ic_resp_tag      ;
    assign ic_l2_resp.payload.data = i_ic_resp_data     ;
    assign o_ic_resp_ready         = ic_l2_resp.ready   ;

    assign o_l1d_req_valid   = l1d_l2_req.valid          ;
    assign o_l1d_req_cmd     = l1d_l2_req.payload.cmd    ;
    assign o_l1d_req_addr    = l1d_l2_req.payload.addr   ;
    assign o_l1d_req_tag     = l1d_l2_req.payload.tag    ;
    assign o_l1d_req_data    = l1d_l2_req.payload.data   ;
    assign o_l1d_req_byte_en = l1d_l2_req.payload.byte_en;
    assign l1d_l2_req.ready  = i_l1d_req_ready        ;

    assign l1d_l2_resp.valid        = i_l1d_resp_valid ;
    assign l1d_l2_resp.payload.tag  = i_l1d_resp_tag   ;
    assign l1d_l2_resp.payload.data = i_l1d_resp_data  ;
    assign o_l1d_resp_ready         = ic_l2_resp.ready ;

    msrh_tile u_msrh_tile (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),

        .ic_l2_req  (ic_l2_req ),
        .ic_l2_resp (ic_l2_resp),

        .l1d_ext_req  (l1d_l2_req ),
        .l1d_ext_resp (l1d_l2_resp)
    );




endmodule

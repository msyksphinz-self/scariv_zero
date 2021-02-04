module mrh_tile_wrapper
(
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    output logic                                o_ic_req_valid,
    output mrh_pkg::mem_cmd_t                   o_ic_req_cmd,
    output logic [riscv_pkg::PADDR_W-1:0]       o_ic_req_addr,
    output logic [mrh_pkg::L2_CMD_TAG_W-1:0]    o_ic_req_tag,
    output logic [mrh_pkg::ICACHE_DATA_W-1:0]   o_ic_req_data,
    output logic [mrh_pkg::ICACHE_DATA_W/8-1:0] o_ic_req_byte_en,
    input logic                                 i_ic_req_ready,

    input logic                              i_ic_resp_valid,
    input logic [mrh_pkg::L2_CMD_TAG_W-1:0]  i_ic_resp_tag,
    input logic [mrh_pkg::ICACHE_DATA_W-1:0] i_ic_resp_data,
    output logic                             o_ic_resp_ready
);

    l2_req_if  ic_l2_req  ();
    l2_resp_if ic_l2_resp ();

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

    mrh_tile u_mrh_tile (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),

        .ic_l2_req  (ic_l2_req ),
        .ic_l2_resp (ic_l2_resp)
    );




endmodule

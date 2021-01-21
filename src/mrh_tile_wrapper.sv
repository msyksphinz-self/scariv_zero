module mrh_tile_wrapper
(
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    output logic                                o_ic_req_vaild,
    output mrh_pkg::mem_cmd_t                   o_ic_req_cmd,
    output logic [riscv_pkg::PADDR_W-1:0]       o_ic_req_addr,
    output logic [mrh_pkg::L2_CMD_TAG_W-1:0]    o_ic_req_tag,
    output logic [mrh_pkg::ICACHE_DATA_W-1:0]   o_ic_req_data,
    output logic [mrh_pkg::ICACHE_DATA_W/8-1:0] o_ic_req_byte_en,
    input logic                                 i_ic_req_ready,

    input logic                              i_ic_resp_valid,
    input logic [mrh_pkg::L2_CMD_TAG_W-1:0]  i_ic_resp_tag,
    input logic [mrh_pkg::ICACHE_DATA_W-1:0] i_ic_resp_data,
    output logic                             o_ic_resq_ready
);

    mrh_pkg::l2_req_t  w_req_payload;
    mrh_pkg::l2_resp_t w_resp_payload;

    assign o_ic_req_cmd     = w_req_payload.cmd    ;
    assign o_ic_req_addr    = w_req_payload.addr   ;
    assign o_ic_req_tag     = w_req_payload.tag    ;
    assign o_ic_req_data    = w_req_payload.data   ;
    assign o_ic_req_byte_en = w_req_payload.byte_en;

    assign w_ic_resp_payload.tag  = i_ic_resp_tag;
    assign w_ic_resp_payload.data = i_ic_resp_data;

    mrh_tile u_mrh_tile (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),

        .ic_req_vaild   (o_ic_req_valid),
        .ic_req_payload (w_ic_req_payload),
        .ic_req_ready   (i_ic_req_ready),

        .ic_resp_valid   (i_ic_resp_valid),
        .ic_resp_payload (w_ic_resp_payload),
        .ic_resq_ready   (o_ic_resp_valid)
    );


endmodule

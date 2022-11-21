module page_table_walker
(
    input logic clk,
    input logic reset_n,

    input  scariv_pkg::ptw_req_t  i_ptw_req,
    output scariv_pkg::ptw_resp_t o_ptw_resp,

    output scariv_lsu_pkg::mem_req_t  o_mem_req,
    input  scariv_lsu_pkg::mem_resp_t i_mem_resp,
);

typedef enum {
    INIT = 0,
    PTW_ACC_REQ = 1,
    PTW_ACC_WAIT = 2,
} ptw_state_t;

ptw_state_t ptw_state_q;

always_ff @ (posedge clk, negedge reset_n) begin
    if (!reset_n) begin
        ptw_state_q <= INIT;
    end else begin
        case (ptw_state_q) 
        INIT : begin
            if (i_ptw_req.valid) begin
                ptw_state_q <= PTW_ACC_REQ;
                o_mem_req.valid <= 1'b1;
            end
        end
        PTW_ACC_REQ : begin
            if (o_mem_req.ready) begin
                ptw_state_q <= PTW_ACC_WAIT;
            if (o_mem_resp.valid) begin
                ptw_state_q <= PTW_ACC_WAIT
            end
        end
        endcase
    end
end


endmodule
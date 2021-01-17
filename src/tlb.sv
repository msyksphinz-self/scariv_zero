module tlb
(
    input  mrh_pkg::tlb_req_t  tlb_req,
    output mrh_pkg::tlb_resp_t tlb_resp
);

assign tlb_resp.miss = 1'b0;
assign tlb_resp.paddr = tlb_req.vaddr[riscv_pkg::PADDR_W-1:0];

endmodule

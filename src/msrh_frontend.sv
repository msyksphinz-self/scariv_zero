module msrh_frontend
(
 input logic i_clk,
 input logic i_reset_n,

 l2_req_if.master ic_l2_req,
 l2_resp_if.slave ic_l2_resp,

 disp_if.master disp
);



    // ==============
    // s0 stage
    // ==============

    logic       s0_vaddr_valid;
    logic [riscv_pkg::VADDR_W-1:0] r_s0_vaddr;
    msrh_pkg::tlb_req_t           w_s0_tlb_req;
    msrh_pkg::tlb_resp_t          w_s0_tlb_resp;
    msrh_pkg::ic_req_t            w_s0_ic_req;
    logic                        w_s0_ic_ready;


    // ==============
    // s1 stage
    // ==============

    logic [riscv_pkg::PADDR_W-1:0] r_s1_paddr;
    logic                        r_s1_tlb_miss;

    // ==============
    // s2 stage
    // ==============

    msrh_pkg::ic_resp_t w_s2_ic_resp;

    always_ff @ (posedge i_clk, negedge i_reset_n) begin
        if (!i_reset_n) begin
            /* verilator lint_off WIDTH */
            r_s0_vaddr <= msrh_pkg::PC_INIT_VAL;
        end else begin
            if (w_s0_ic_ready) begin
                r_s0_vaddr <= r_s0_vaddr + (1 << $clog2(msrh_pkg::ICACHE_DATA_B_W));
            end
        end
    end

    assign s0_vaddr_valid     = i_reset_n;
    assign w_s0_tlb_req.vaddr = r_s0_vaddr;
    assign w_s0_tlb_req.cmd   = msrh_pkg::M_XRD;

    tlb u_tlb
        (
         .i_clk      (i_clk),
         .i_reset_n  (i_reset_n),

         .i_tlb_req  (w_s0_tlb_req ),
         .o_tlb_resp (w_s0_tlb_resp)
         );

    // s0 --> s1
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
        if (!i_reset_n) begin
            r_s1_paddr <= 'h0;
            r_s1_tlb_miss <= 'h0;
        end else begin
            r_s1_paddr <= w_s0_tlb_resp.paddr;
            r_s1_tlb_miss <= w_s0_tlb_resp.miss;
        end
    end

    assign w_s0_ic_req.valid = s0_vaddr_valid;
    assign w_s0_ic_req.vaddr = r_s0_vaddr;

    icache u_icache
        (
         .i_clk     (i_clk),
         .i_reset_n (i_reset_n),

         .i_s0_req (w_s0_ic_req),
         .o_s0_ready(w_s0_ic_ready),


         .i_s1_paddr (r_s1_paddr),
         .i_s1_tlb_miss (r_s1_tlb_miss),

         .o_s2_resp (w_s2_ic_resp),

         .ic_l2_req  (ic_l2_req ),
         .ic_l2_resp (ic_l2_resp)
         );

inst_buffer
u_inst_buffer
  (
   .i_clk     (i_clk    ),
   .i_reset_n (i_reset_n),

   .i_inst_vld (w_s2_ic_resp.valid),

   .o_inst_rdy(),
   .i_inst_in (w_s2_ic_resp.data),
   .i_inst_byte_en(w_s2_ic_resp.be),

   .o_inst_buf_valid ( disp.valid ),
   .o_inst_buf       ( disp.inst  ),
   .i_inst_buf_ready ( disp.ready )
   );

endmodule // msrh_frontend

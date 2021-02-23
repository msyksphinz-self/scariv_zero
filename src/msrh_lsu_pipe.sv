module msrh_lsu_pipe
  #(
    parameter RV_ENTRY_SIZE = 32
    )
(
 input logic                       i_clk,
 input logic                       i_reset_n,

 input logic                       rv0_is_store,
 input                             msrh_pkg::issue_t rv0_issue,
 input logic [RV_ENTRY_SIZE-1:0]   rv0_index,
 input                             msrh_pkg::phy_wr_t ex1_i_phy_wr[msrh_pkg::TGT_BUS_SIZE],

                                   regread_if.master ex1_regread_rs1,
                                   regread_if.master ex1_regread_rs2,

 output                            msrh_pkg::early_wr_t o_ex1_early_wr,
 output                            msrh_pkg::phy_wr_t o_ex3_phy_wr,

 output logic                      o_ex3_done,
 output logic [RV_ENTRY_SIZE-1: 0] o_ex3_index

);

//
// EX0 stage
//
msrh_pkg::issue_t                  w_ex0_issue;
logic [RV_ENTRY_SIZE-1: 0]         w_ex0_index;

//
// EX1 stage
//
msrh_pkg::issue_t                  r_ex1_issue;
logic [RV_ENTRY_SIZE-1: 0]         r_ex1_index;
logic [riscv_pkg::VADDR_W-1: 0]    w_ex1_vaddr;
msrh_pkg::tlb_req_t                w_ex1_tlb_req;
msrh_pkg::tlb_resp_t               w_ex1_tlb_resp;

//
// EX2 stage
//
msrh_pkg::issue_t                  r_ex2_issue;
logic [RV_ENTRY_SIZE-1: 0]         r_ex2_index;


//
// Pipeline Logic
//
always_ff @(posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_issue     <= 'h0;
    r_ex1_index     <= 'h0;
    r_ex1_pipe_ctrl <= 'h0;

    r_ex2_issue     <= 'h0;
    r_ex2_index     <= 'h0;
    r_ex2_pipe_ctrl <= 'h0;
  end else begin
    r_ex1_issue     <= w_ex0_issue;
    r_ex1_index     <= w_ex0_index;
    r_ex1_pipe_ctrl <= w_ex0_pipe_ctrl;

    r_ex2_issue     <= w_ex2_issue;
    r_ex2_index     <= w_ex2_index;
    r_ex2_pipe_ctrl <= w_ex2_pipe_ctrl;
  end
end


// TLB
tlb
  #(
    .USING_VM(1'b1)
    )
u_tlb
(
 .i_clk    (i_clk),
 .i_reset_n(i_reset_n),

 .i_tlb_req (w_ex1_tlb_req ),
 .o_tlb_resp(w_ex1_tlb_resp)
 );


//
// EX0 stage pipeline
//

//
// EX1 stage pipeline
//
assign ex1_regread_rs1.valid = r_ex1_issue.valid & r_ex1_issue.rs1_valid;
assign ex1_regread_rs1.rnid  = r_ex1_issue.rs1_rnid;

assign ex1_regread_rs2.valid = rv0_is_store ? r_ex1_issue.valid & r_ex1_issue.rs2_valid : 0;
assign ex1_regread_rs2.rnid  = r_ex1_issue.rs2_rnid;

assign w_ex1_vaddr = ex1_regread_rs1.data + r_ex1_issue.inst[31:20];
assign w_ex1_tlb_req.vld   = r_ex1_issue.valid;
assign w_ex1_tlb_req.vaddr = w_ex1_vaddr;


endmodule // msrh_lsu_pipe

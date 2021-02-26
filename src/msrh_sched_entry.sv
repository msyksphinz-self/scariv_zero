module msrh_sched_entry
(
   input logic  i_clk,
   input logic  i_reset_n,

   input logic  i_put,
   input logic [msrh_pkg::CMT_BLK_W-1:0] i_cmt_id,
   input logic [msrh_pkg::DISP_SIZE-1:0] i_grp_id,
   input        msrh_pkg::disp_t i_put_data,

   output logic o_entry_valid,
   output logic o_entry_ready,
   output msrh_pkg::issue_t o_entry,

   /* Forwarding path */
   input        msrh_pkg::early_wr_t i_early_wr[msrh_pkg::REL_BUS_SIZE],

   input logic  i_entry_picked,
   input logic  i_pipe_done,
   output logic o_entry_done,
   output logic [msrh_pkg::CMT_BLK_W-1:0] o_cmt_id,
   output logic [msrh_pkg::DISP_SIZE-1:0] o_grp_id
   );

typedef enum { INIT, WAIT, ISSUED, DONE } state_t;

logic    r_entry_valid;
logic    w_entry_valid;
logic    r_issued;
msrh_pkg::issue_t r_entry;
msrh_pkg::issue_t w_entry;
msrh_pkg::issue_t w_init_entry;

logic [msrh_pkg::RNID_W-1:0] w_rs1_rnid;
logic [msrh_pkg::RNID_W-1:0] w_rs2_rnid;
msrh_pkg::reg_t w_rs1_type;
msrh_pkg::reg_t w_rs2_type;

logic     w_rs1_entry_hit;
logic     w_rs2_entry_hit;

state_t r_state;


function logic all_operand_ready(msrh_pkg::issue_t entry);
  return (!entry.rs1_valid | entry.rs1_valid  & entry.rs1_ready) &
    (!entry.rs2_valid | entry.rs2_valid  & entry.rs2_ready);
endfunction // all_operand_ready


assign w_rs1_rnid = i_put ? i_put_data.rs1_rnid : r_entry.rs1_rnid;
assign w_rs2_rnid = i_put ? i_put_data.rs2_rnid : r_entry.rs2_rnid;

assign w_rs1_type = i_put ? i_put_data.rs1_type : r_entry.rs1_type;
assign w_rs2_type = i_put ? i_put_data.rs2_type : r_entry.rs2_type;

select_early_wr_bus rs1_rel_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .i_early_wr   (i_early_wr),

 .o_valid      (w_rs1_entry_hit)
 );


select_early_wr_bus rs2_rel_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .i_early_wr   (i_early_wr),

 .o_valid      (w_rs2_entry_hit)
 );


always_comb begin
  w_entry_valid = r_entry_valid;
  w_entry = r_entry;
  w_entry.rs1_ready = r_entry.rs1_ready | w_rs1_entry_hit;
  w_entry.rs2_ready = r_entry.rs2_ready | w_rs2_entry_hit;
end


assign w_init_entry = msrh_pkg::assign_issue_t(i_put_data, i_cmt_id, i_grp_id,
                                               w_rs1_entry_hit, w_rs2_entry_hit);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry_valid <= 1'b0;
    r_entry <= 'h0;

    r_state <= INIT;
    r_issued <= 1'b0;
  end else begin
    case (r_state)
      INIT : begin
        if (i_put) begin
          r_entry_valid <= 1'b1;
          r_entry <= w_init_entry;
          r_state <= WAIT;
        end
      end
      WAIT : begin
        r_entry <= w_entry;
        if (o_entry_valid & o_entry_ready & i_entry_picked) begin
          r_issued <= 1'b1;
          r_state <= ISSUED;
        end
      end
      ISSUED : begin
        if (i_pipe_done) begin
          r_state <= DONE;
        end
      end
      DONE : begin
        r_entry_valid <= 1'b0;
        r_issued <= 1'b0;
        r_state <= INIT;
      end
    endcase // case (r_state)
  end // else: !if(!i_reset_n)
end

assign o_entry_valid = r_entry_valid;
assign o_entry_ready = r_entry_valid & !r_issued & all_operand_ready(w_entry);
assign o_entry       = w_entry;

assign o_entry_done = r_state == DONE;
assign o_cmt_id = r_entry.cmt_id;
assign o_grp_id = r_entry.grp_id;

endmodule // msrh_sched_entry

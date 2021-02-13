module msrh_sched_entry
(
   input logic i_clk,
   input logic i_reset_n,

   input logic            i_put,
   input msrh_pkg::disp_t  i_put_data,

   output logic            o_entry_valid,
   output logic            o_entry_ready,
   output msrh_pkg::issue_t o_entry,

   /* Forwarding path */
   input msrh_pkg::release_t release_in[msrh_pkg::REL_BUS_SIZE]
   );


logic    r_entry_valid;
logic    w_entry_valid;
msrh_pkg::issue_t r_entry;
msrh_pkg::issue_t w_entry;

logic [msrh_pkg::RNID_W-1:0] w_rs1_rnid;
logic [msrh_pkg::RNID_W-1:0] w_rs2_rnid;
msrh_pkg::reg_t w_rs1_type;
msrh_pkg::reg_t w_rs2_type;

logic     w_rs1_entry_hit;
logic     w_rs2_entry_hit;

function logic all_operand_ready(msrh_pkg::issue_t entry);
  return (!entry.rs1_valid | entry.rs1_valid  & entry.rs1_ready) &
    (!entry.rs2_valid | entry.rs2_valid  & entry.rs2_ready);
endfunction // all_operand_ready


assign w_rs1_rnid = i_put ? i_put_data.rs1_rnid : r_entry.rs1_rnid;
assign w_rs2_rnid = i_put ? i_put_data.rs2_rnid : r_entry.rs2_rnid;

assign w_rs1_type = i_put ? i_put_data.rs1_type : r_entry.rs1_type;
assign w_rs2_type = i_put ? i_put_data.rs2_type : r_entry.rs2_type;

select_release_bus rs1_rel_select
(
 .i_entry_rnid (w_rs1_rnid),
 .i_entry_type (w_rs1_type),
 .release_in   (release_in),

 .o_valid      (w_rs1_entry_hit)
 );


select_release_bus rs2_rel_select
(
 .i_entry_rnid (w_rs2_rnid),
 .i_entry_type (w_rs2_type),
 .release_in   (release_in),

 .o_valid      (w_rs2_entry_hit)
 );


always_comb begin
  w_entry_valid = r_entry_valid;
  w_entry = r_entry;
  w_entry.rs1_ready = r_entry.rs1_ready | w_rs1_entry_hit;
  w_entry.rs2_ready = r_entry.rs2_ready | w_rs2_entry_hit;
end


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry_valid <= 1'b0;
    r_entry <= 'h0;
  end else begin
    if (i_put) begin
      r_entry_valid <= 1'b1;
      r_entry <= msrh_pkg::assign_issue_t(i_put_data, w_rs1_entry_hit, w_rs2_entry_hit);
    end else if (o_entry_valid & o_entry_ready) begin
      r_entry_valid <= 1'b0;
      r_entry <= 'h0;
    end else begin
      r_entry_valid <= w_entry_valid;
      r_entry <= w_entry;
    end
  end // else: !if(!i_reset_n)
end

assign o_entry_valid = r_entry_valid;
assign o_entry_ready = r_entry_valid & all_operand_ready(w_entry);
assign o_entry       = w_entry;

endmodule // msrh_sched_entry

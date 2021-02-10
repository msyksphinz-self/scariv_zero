module mrh_sched_entry
(
   input logic i_clk,
   input logic i_reset_n,

   input logic            i_put,
   input mrh_pkg::disp_t  i_put_data,

   output logic            o_entry_valid,
   output logic            o_entry_ready,
   output mrh_pkg::issue_t o_entry,

   /* Forwarding path */
   input mrh_pkg::release_t release_in[mrh_pkg::REL_BUS_SIZE]
   );


logic     r_entry_valid;
mrh_pkg::issue_t r_entry;

function logic all_operand_ready(mrh_pkg::issue_t entry);
  return (!entry.rs1_valid | entry.rs1_valid  & entry.rs1_ready) &
    (!entry.rs2_valid | entry.rs2_valid  & entry.rs2_ready);
endfunction // all_operand_ready


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry_valid <= 1'b0;
    r_entry <= 'h0;
  end else begin
    if (i_put) begin
      r_entry_valid <= 1'b1;
      r_entry <= mrh_pkg::assign_issue_t(i_put_data);
    end
  end
end

assign o_entry_valid = r_entry_valid;
assign o_entry_ready = r_entry_valid & all_operand_ready(r_entry);
assign o_entry       = r_entry;

endmodule // mrh_sched_entry

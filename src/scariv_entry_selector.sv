// ------------------------------------------------------------------------
// NAME : scariv_entry_selector
// TYPE : module
// ------------------------------------------------------------------------
// Valid bits are selected based on i_oh_ptr
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_entry_selector
  #(
    parameter ENTRY_SIZE = 8
    )
(
 input logic [ENTRY_SIZE-1: 0]  i_oh_ptr,
 input logic [ENTRY_SIZE-1: 0]  i_entry_valids,

 output logic [ENTRY_SIZE-1: 0] o_entry_valid
 );


logic [ENTRY_SIZE-1: 0]         w_picked_valids;
logic [ENTRY_SIZE-1: 0]         w_picked_valids_pri;

bit_brshift
  #(.WIDTH(ENTRY_SIZE))
u_age_selector
  (
   .in   (i_entry_valids),
   .i_sel(i_oh_ptr),
   .out  (w_picked_valids)
   );

bit_extract_lsb #(.WIDTH(ENTRY_SIZE)) u_pick_ready_inst (.in(w_picked_valids), .out(w_picked_valids_pri));

bit_blshift
  #(.WIDTH(ENTRY_SIZE))
u_inst_selector
  (
   .in   (w_picked_valids_pri),
   .i_sel(i_oh_ptr),
   .out  (o_entry_valid)
   );

endmodule // scariv_entry_selector

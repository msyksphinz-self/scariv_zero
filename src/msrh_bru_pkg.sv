interface done_if #(parameter RV_ENTRY_SIZE=32);
logic          done;
logic [RV_ENTRY_SIZE-1: 0] index_oh;

modport master(
  output done,
  output index_oh
);

modport slave(
  input done,
  input index_oh
);

endinterface // done_if

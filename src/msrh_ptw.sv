module msrh_ptw
  (
   // Page Table Walk I/O
   tlb_ptw_if.slave ptw_if[1 + msrh_conf_pkg::LSU_INST_NUM]
   );

endmodule // msrh_ptw

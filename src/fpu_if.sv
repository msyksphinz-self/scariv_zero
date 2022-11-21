interface fflags_update_if;
  logic               valid;
  scariv_pkg::fflags_t  fflags;

modport master
  (
   output valid,
   output fflags
   );
modport slave
  (
   input valid,
   input fflags
   );

endinterface // fflags_update_if

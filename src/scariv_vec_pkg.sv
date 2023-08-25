package scariv_vec_pkg;

parameter VLEN = 128;
parameter VLENB = VLEN / 8;
parameter VLENBMAX = VLENB * 8;

typedef struct packed {
  logic          valid;
  logic [ 7: 0]  vtype;
  logic          vill;
  logic [$clog2(VLENBMAX)-1: 0] vl;
} csr_write_t;
typedef struct packed {
  logic [$clog2(VLENBMAX)-1: 0] vl;
  logic [$clog2(VLENBMAX)-1: 0] vlmax;
} csr_info_t;

function automatic logic [$clog2(VLENBMAX)-1: 0] calc_vlmax(logic [ 2: 0] vlmul,
                                                            logic [ 2: 0] vsew);
  return (VLENB << vlmul) >> vsew;

endfunction

endpackage // scariv_vec_pkg


interface vec_csr_if;

  scariv_vec_pkg::csr_write_t write;
  scariv_vec_pkg::csr_info_t  info;

  modport master (
    input  write,
    output info
  );

  modport slave (
    output write,
    input  info
  );

endinterface // vec_csr_if

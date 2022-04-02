interface csr_rd_if;

  logic valid;
  logic [11: 0] addr;
  riscv_pkg::xlen_t data;
  logic                          resp_error;

  modport master (
    output valid,
    output addr,
    input  data,
    input  resp_error
  );

  modport slave (
    input  valid,
    input  addr,
    output data,
    output resp_error
  );

endinterface // csr_rd_if


interface csr_wr_if;

  logic                          valid;
  logic [11: 0]                  addr;
  riscv_pkg::xlen_t data;
  logic                          resp_error;

  modport master (
    output valid,
    output addr,
    output data,
    input  resp_error
  );

  modport slave (
    input  valid,
    input  addr,
    input  data,
    output resp_error
  );

endinterface // csr_wr_if


interface csr_info_if;

riscv_common_pkg::priv_t       priv;
riscv_pkg::xlen_t mstatus;
riscv_pkg::xlen_t mepc;
riscv_pkg::xlen_t mtvec;
riscv_pkg::xlen_t stvec;
riscv_pkg::xlen_t utvec;
riscv_pkg::xlen_t sepc;
riscv_pkg::xlen_t uepc;
riscv_pkg::xlen_t satp;
riscv_pkg::xlen_t medeleg;
riscv_pkg::xlen_t sedeleg;
logic [31: 0] fcsr;


modport master (
  output priv,
  output mstatus,
  output mepc,
  output mtvec,
  output stvec,
  output utvec,
  output sepc,
  output uepc,
  output satp,
  output medeleg,
  output sedeleg,
  output fcsr
);

modport slave (
  input priv,
  input mstatus,
  input mepc,
  input mtvec,
  input stvec,
  input utvec,
  input sepc,
  input uepc,
  input satp,
  input medeleg,
  input sedeleg,
  input fcsr
);

endinterface // csr_info_if

interface interrupt_if;

logic   s_software_int_valid;
logic   s_timer_int_valid;
logic   s_external_int_valid;

logic   m_software_int_valid;
logic   m_timer_int_valid;
logic   m_external_int_valid;

modport master (
   output s_software_int_valid,
   output s_timer_int_valid,
   output s_external_int_valid,
   output m_software_int_valid,
   output m_timer_int_valid,
   output m_external_int_valid
);

modport slave (
   input s_software_int_valid,
   input s_timer_int_valid,
   input s_external_int_valid,
   input m_software_int_valid,
   input m_timer_int_valid,
   input m_external_int_valid
);

endinterface // interrupt_if

package msrh_csu_pkg;

typedef enum logic [ 1: 0] {
  TVEC_MODE_DIRECT = 2'b00,
  TVEC_MODE_VECTOR = 2'b01
} tvec_mode_t;

typedef struct packed {
  logic [riscv_pkg::XLEN_W-1: 2] base;
  tvec_mode_t                    mode;
} tvec_field_t;

typedef union packed {
  tvec_field_t                   field;
  riscv_pkg::xlen_t raw_bit;
} tvec_t;


typedef struct packed {
logic [31: 3]  hpm;
logic          ir;
logic          tm;
logic          cy;
} counteren_field_t;

typedef union packed {
  counteren_field_t field;
  logic [31: 0] raw_bit;
} counteren_t;

endpackage // msrh_csu_pkg

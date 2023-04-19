// ------------------------------------------------------------------------
// NAME : scariv_csr
// TYPE : module
// ------------------------------------------------------------------------
// Actual Control & System Register File
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_csr
  import riscv_pkg::*;
  import scariv_csu_pkg::*;
  (
   input logic                i_clk,
   input logic                i_reset_n,

   csr_rd_if.slave            read_if,
   csr_wr_if.slave            write_if,

   /* CSR information */
   csr_info_if.master         csr_info,
   /* Interrupt Request information */
   interrupt_if.master        int_if,
   /* FFlags update for FPU */
   fflags_update_if.slave     fflags_update_if,

   // CLINT connection
   clint_if.slave clint_if,
   // PLIC connection
   plic_if.slave  plic_if,

   // Commit notification
   input scariv_pkg::commit_blk_t i_commit
   );

`include "scariv_csr_def.svh"

riscv_common_pkg::priv_t    r_priv, w_priv_next;

logic w_wr_mcsr_ill_access;
logic w_wr_scsr_ill_access;
logic w_wr_mcsr_ill_write ;

logic w_rd_satp_tvm_1;
logic w_rd_counter;
logic w_rd_mcsr_ill_access;
logic w_rd_scsr_ill_access;
logic w_rd_fpu_ill_access;
logic w_rd_ill_address;

logic [63: 0]                 r_cycle;    // These registers are always 64-bit
logic [63: 0]                 r_instret;  // These registers are always 64-bit
logic [63: 0]                 r_time;     // These registers are always 64-bit

logic [63: 0]                 r_hpmcounter [31: 3];

xlen_t r_ustatus;
xlen_t r_uie;
tvec_t              r_utvec;
xlen_t r_vstart;
xlen_t r_vxsat;
xlen_t r_vxrm;
xlen_t r_uscratch;
xlen_t r_uepc;
xlen_t r_ucause;
xlen_t r_ubadaddr;
xlen_t r_uip;
logic [ 4: 0]                 r_fflags;
logic [ 2: 0]                 r_frm;
xlen_t r_sedeleg;
xlen_t r_sideleg;
xlen_t r_sie;
tvec_t              r_stvec;
counteren_t         r_scounteren;
xlen_t r_sscratch;
xlen_t r_sepc, w_sepc_next;
xlen_t r_scause, w_scause_next;
xlen_t r_stval, w_stval_next;
xlen_t r_sip;
xlen_t r_satp;
xlen_t r_hstatus;
xlen_t r_hedeleg;
xlen_t r_hideleg;
xlen_t r_hie;
tvec_t              r_htvec;
xlen_t r_hscratch;
xlen_t r_hepc;
xlen_t r_hcause;
xlen_t r_hbadaddr;
xlen_t r_hip;
xlen_t r_hptbr;
xlen_t r_mvendorid;
xlen_t r_marchid;
xlen_t r_mimpid;
xlen_t r_mhartid;
riscv_pkg::xlen_t w_mstatus, w_mstatus_next;
xlen_t r_mstatus;
xlen_t r_misa;
xlen_t r_medeleg;
xlen_t r_mideleg;
xlen_t r_mie;
tvec_t              r_mtvec;
counteren_t         r_mcounteren;
xlen_t r_mscratch;
xlen_t r_mepc,   w_mepc_next;
xlen_t r_mcause, w_mcause_next;
xlen_t r_mtval,  w_mtval_next;
xlen_t r_mip;
xlen_t r_mbase;
xlen_t r_mbound;
xlen_t r_mibase;
xlen_t r_mibound;
xlen_t r_mdbase;
xlen_t r_mdbound;
xlen_t r_mhpevent3;
xlen_t r_mhpevent4;
xlen_t r_mhpevent5;
xlen_t r_mhpevent6;
xlen_t r_mhpevent7;
xlen_t r_mhpevent8;
xlen_t r_mhpevent9;
xlen_t r_mhpevent10;
xlen_t r_mhpevent11;
xlen_t r_mhpevent12;
xlen_t r_mhpevent13;
xlen_t r_mhpevent14;
xlen_t r_mhpevent15;
xlen_t r_mhpevent16;
xlen_t r_mhpevent17;
xlen_t r_mhpevent18;
xlen_t r_mhpevent19;
xlen_t r_mhpevent20;
xlen_t r_mhpevent21;
xlen_t r_mhpevent22;
xlen_t r_mhpevent23;
xlen_t r_mhpevent24;
xlen_t r_mhpevent25;
xlen_t r_mhpevent26;
xlen_t r_mhpevent27;
xlen_t r_mhpevent28;
xlen_t r_mhpevent29;
xlen_t r_mhpevent30;
xlen_t r_mhpevent31;
xlen_t r_pmpcfg0;
xlen_t r_pmpcfg1;
xlen_t r_pmpcfg2;
xlen_t r_pmpcfg3;
xlen_t r_pmpaddr0;
xlen_t r_pmpaddr1;
xlen_t r_pmpaddr2;
xlen_t r_pmpaddr3;
xlen_t r_pmpaddr4;
xlen_t r_pmpaddr5;
xlen_t r_pmpaddr6;
xlen_t r_pmpaddr7;
xlen_t r_pmpaddr8;
xlen_t r_pmpaddr9;
xlen_t r_pmpaddr10;
xlen_t r_pmpaddr11;
xlen_t r_pmpaddr12;
xlen_t r_pmpaddr13;
xlen_t r_pmpaddr14;
xlen_t r_pmpaddr15;
xlen_t r_stats;

always_comb begin
  w_rd_ill_address = 1'b0;
  case (read_if.addr)
    `SYSREG_ADDR_USTATUS        : read_if.data = r_ustatus;
    `SYSREG_ADDR_UIE            : read_if.data = r_uie;
    `SYSREG_ADDR_UTVEC          : read_if.data = r_utvec.raw_bit;
    `SYSREG_ADDR_VSTART         : read_if.data = r_vstart;
    `SYSREG_ADDR_VXSAT          : read_if.data = r_vxsat;
    `SYSREG_ADDR_VXRM           : read_if.data = r_vxrm;
    `SYSREG_ADDR_USCRATCH       : read_if.data = r_uscratch;
    `SYSREG_ADDR_UEPC           : read_if.data = r_uepc;
    `SYSREG_ADDR_UCAUSE         : read_if.data = r_ucause;
    `SYSREG_ADDR_UBADADDR       : read_if.data = r_ubadaddr;
    `SYSREG_ADDR_UIP            : read_if.data = r_uip;
    `SYSREG_ADDR_FFLAGS         : read_if.data = {27'h0, r_fflags};
    `SYSREG_ADDR_FRM            : read_if.data = {29'h0, r_frm};
    `SYSREG_ADDR_FCSR           : read_if.data = {24'h0, r_frm, r_fflags};
    `SYSREG_ADDR_CYCLE          : read_if.data = r_cycle  [riscv_pkg::XLEN_W-1: 0];
    // `SYSREG_ADDR_TIME           : read_if.data = r_time   [riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_INSTRET        : read_if.data = r_instret[riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER3    : read_if.data = r_hpmcounter[ 3][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER4    : read_if.data = r_hpmcounter[ 4][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER5    : read_if.data = r_hpmcounter[ 5][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER6    : read_if.data = r_hpmcounter[ 6][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER7    : read_if.data = r_hpmcounter[ 7][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER8    : read_if.data = r_hpmcounter[ 8][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER9    : read_if.data = r_hpmcounter[ 9][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER10   : read_if.data = r_hpmcounter[10][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER11   : read_if.data = r_hpmcounter[11][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER12   : read_if.data = r_hpmcounter[12][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER13   : read_if.data = r_hpmcounter[13][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER14   : read_if.data = r_hpmcounter[14][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER15   : read_if.data = r_hpmcounter[15][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER16   : read_if.data = r_hpmcounter[16][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER17   : read_if.data = r_hpmcounter[17][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER18   : read_if.data = r_hpmcounter[18][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER19   : read_if.data = r_hpmcounter[19][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER20   : read_if.data = r_hpmcounter[20][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER21   : read_if.data = r_hpmcounter[21][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER22   : read_if.data = r_hpmcounter[22][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER23   : read_if.data = r_hpmcounter[23][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER24   : read_if.data = r_hpmcounter[24][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER25   : read_if.data = r_hpmcounter[25][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER26   : read_if.data = r_hpmcounter[26][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER27   : read_if.data = r_hpmcounter[27][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER28   : read_if.data = r_hpmcounter[28][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER29   : read_if.data = r_hpmcounter[29][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER30   : read_if.data = r_hpmcounter[30][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_HPMCOUNTER31   : read_if.data = r_hpmcounter[31][riscv_pkg::XLEN_W-1: 0];
`ifdef RV32
    `SYSREG_ADDR_CYCLEH         : read_if.data = r_cycle          [63:32];
    // `SYSREG_ADDR_TIMEH          : read_if.data = r_time           [63:32];
    `SYSREG_ADDR_INSTRETH       : read_if.data = r_instret        [63:32];
    `SYSREG_ADDR_HPMCOUNTERH3   : read_if.data = r_hpmcounter[ 3][63:32];
    `SYSREG_ADDR_HPMCOUNTERH4   : read_if.data = r_hpmcounter[ 4][63:32];
    `SYSREG_ADDR_HPMCOUNTERH5   : read_if.data = r_hpmcounter[ 5][63:32];
    `SYSREG_ADDR_HPMCOUNTERH6   : read_if.data = r_hpmcounter[ 6][63:32];
    `SYSREG_ADDR_HPMCOUNTERH7   : read_if.data = r_hpmcounter[ 7][63:32];
    `SYSREG_ADDR_HPMCOUNTERH8   : read_if.data = r_hpmcounter[ 8][63:32];
    `SYSREG_ADDR_HPMCOUNTERH9   : read_if.data = r_hpmcounter[ 9][63:32];
    `SYSREG_ADDR_HPMCOUNTERH10  : read_if.data = r_hpmcounter[10][63:32];
    `SYSREG_ADDR_HPMCOUNTERH11  : read_if.data = r_hpmcounter[11][63:32];
    `SYSREG_ADDR_HPMCOUNTERH12  : read_if.data = r_hpmcounter[12][63:32];
    `SYSREG_ADDR_HPMCOUNTERH13  : read_if.data = r_hpmcounter[13][63:32];
    `SYSREG_ADDR_HPMCOUNTERH14  : read_if.data = r_hpmcounter[14][63:32];
    `SYSREG_ADDR_HPMCOUNTERH15  : read_if.data = r_hpmcounter[15][63:32];
    `SYSREG_ADDR_HPMCOUNTERH16  : read_if.data = r_hpmcounter[16][63:32];
    `SYSREG_ADDR_HPMCOUNTERH17  : read_if.data = r_hpmcounter[17][63:32];
    `SYSREG_ADDR_HPMCOUNTERH18  : read_if.data = r_hpmcounter[18][63:32];
    `SYSREG_ADDR_HPMCOUNTERH19  : read_if.data = r_hpmcounter[19][63:32];
    `SYSREG_ADDR_HPMCOUNTERH20  : read_if.data = r_hpmcounter[20][63:32];
    `SYSREG_ADDR_HPMCOUNTERH21  : read_if.data = r_hpmcounter[21][63:32];
    `SYSREG_ADDR_HPMCOUNTERH22  : read_if.data = r_hpmcounter[22][63:32];
    `SYSREG_ADDR_HPMCOUNTERH23  : read_if.data = r_hpmcounter[23][63:32];
    `SYSREG_ADDR_HPMCOUNTERH24  : read_if.data = r_hpmcounter[24][63:32];
    `SYSREG_ADDR_HPMCOUNTERH25  : read_if.data = r_hpmcounter[25][63:32];
    `SYSREG_ADDR_HPMCOUNTERH26  : read_if.data = r_hpmcounter[26][63:32];
    `SYSREG_ADDR_HPMCOUNTERH27  : read_if.data = r_hpmcounter[27][63:32];
    `SYSREG_ADDR_HPMCOUNTERH28  : read_if.data = r_hpmcounter[28][63:32];
    `SYSREG_ADDR_HPMCOUNTERH29  : read_if.data = r_hpmcounter[29][63:32];
    `SYSREG_ADDR_HPMCOUNTERH30  : read_if.data = r_hpmcounter[30][63:32];
    `SYSREG_ADDR_HPMCOUNTERH31  : read_if.data = r_hpmcounter[31][63:32];
`endif // RV32
    `SYSREG_ADDR_SSTATUS        : read_if.data = riscv_pkg::map_sstatus(r_mstatus);
    `SYSREG_ADDR_SEDELEG        : read_if.data = r_sedeleg;
    `SYSREG_ADDR_SIDELEG        : read_if.data = r_sideleg;
    `SYSREG_ADDR_SIE            : read_if.data = r_sie;
    `SYSREG_ADDR_STVEC          : read_if.data = r_stvec.raw_bit;
    /* verilator lint_off WIDTH */
    `SYSREG_ADDR_SCOUNTEREN     : read_if.data = r_scounteren.raw_bit;
    `SYSREG_ADDR_SSCRATCH       : read_if.data = r_sscratch;
    `SYSREG_ADDR_SEPC           : read_if.data = r_sepc;
    `SYSREG_ADDR_SCAUSE         : read_if.data = r_scause;
    `SYSREG_ADDR_STVAL          : read_if.data = r_stval;
    `SYSREG_ADDR_SIP            : read_if.data = r_sip;
    `SYSREG_ADDR_SATP           : read_if.data = r_satp;
    `SYSREG_ADDR_HSTATUS        : read_if.data = r_hstatus;
    `SYSREG_ADDR_HEDELEG        : read_if.data = r_hedeleg;
    `SYSREG_ADDR_HIDELEG        : read_if.data = r_hideleg;
    `SYSREG_ADDR_HIE            : read_if.data = r_hie;
    `SYSREG_ADDR_HTVEC          : read_if.data = r_htvec.raw_bit;
    `SYSREG_ADDR_HSCRATCH       : read_if.data = r_hscratch;
    `SYSREG_ADDR_HEPC           : read_if.data = r_hepc;
    `SYSREG_ADDR_HCAUSE         : read_if.data = r_hcause;
    `SYSREG_ADDR_HBADADDR       : read_if.data = r_hbadaddr;
    `SYSREG_ADDR_HIP            : read_if.data = r_hip;
    `SYSREG_ADDR_HPTBR          : read_if.data = r_hptbr;
    `SYSREG_ADDR_MVENDORID      : read_if.data = r_mvendorid;
    `SYSREG_ADDR_MARCHID        : read_if.data = r_marchid;
    `SYSREG_ADDR_MIMPID         : read_if.data = r_mimpid;
    `SYSREG_ADDR_MHARTID        : read_if.data = r_mhartid;
    `SYSREG_ADDR_MSTATUS        : read_if.data = w_mstatus;
    `SYSREG_ADDR_MISA           : read_if.data = r_misa;
    `SYSREG_ADDR_MEDELEG        : read_if.data = r_medeleg;
    `SYSREG_ADDR_MIDELEG        : read_if.data = r_mideleg;
    `SYSREG_ADDR_MIE            : read_if.data = r_mie;
    `SYSREG_ADDR_MTVEC          : read_if.data = r_mtvec.raw_bit;
    /* verilator lint_off WIDTH */
    `SYSREG_ADDR_MCOUNTEREN     : read_if.data = r_mcounteren.raw_bit;
    `SYSREG_ADDR_MSCRATCH       : read_if.data = r_mscratch;
    `SYSREG_ADDR_MEPC           : read_if.data = r_mepc;
    `SYSREG_ADDR_MCAUSE         : read_if.data = r_mcause;
    `SYSREG_ADDR_MTVAL          : read_if.data = r_mtval;
    `SYSREG_ADDR_MIP            : read_if.data = r_mip;
    `SYSREG_ADDR_MBASE          : read_if.data = r_mbase;
    `SYSREG_ADDR_MBOUND         : read_if.data = r_mbound;
    `SYSREG_ADDR_MIBASE         : read_if.data = r_mibase;
    `SYSREG_ADDR_MIBOUND        : read_if.data = r_mibound;
    `SYSREG_ADDR_MDBASE         : read_if.data = r_mdbase;
    `SYSREG_ADDR_MDBOUND        : read_if.data = r_mdbound;
    `SYSREG_ADDR_MCYCLE         : read_if.data = r_cycle   [riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MINSTRET       : read_if.data = r_instret [riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER3   : read_if.data = r_hpmcounter[ 3][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER4   : read_if.data = r_hpmcounter[ 4][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER5   : read_if.data = r_hpmcounter[ 5][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER6   : read_if.data = r_hpmcounter[ 6][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER7   : read_if.data = r_hpmcounter[ 7][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER8   : read_if.data = r_hpmcounter[ 8][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER9   : read_if.data = r_hpmcounter[ 9][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER10  : read_if.data = r_hpmcounter[10][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER11  : read_if.data = r_hpmcounter[11][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER12  : read_if.data = r_hpmcounter[12][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER13  : read_if.data = r_hpmcounter[13][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER14  : read_if.data = r_hpmcounter[14][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER15  : read_if.data = r_hpmcounter[15][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER16  : read_if.data = r_hpmcounter[16][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER17  : read_if.data = r_hpmcounter[17][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER18  : read_if.data = r_hpmcounter[18][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER19  : read_if.data = r_hpmcounter[19][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER20  : read_if.data = r_hpmcounter[20][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER21  : read_if.data = r_hpmcounter[21][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER22  : read_if.data = r_hpmcounter[22][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER23  : read_if.data = r_hpmcounter[23][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER24  : read_if.data = r_hpmcounter[24][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER25  : read_if.data = r_hpmcounter[25][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER26  : read_if.data = r_hpmcounter[26][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER27  : read_if.data = r_hpmcounter[27][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER28  : read_if.data = r_hpmcounter[28][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER29  : read_if.data = r_hpmcounter[29][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER30  : read_if.data = r_hpmcounter[30][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPMCOUNTER31  : read_if.data = r_hpmcounter[31][riscv_pkg::XLEN_W-1: 0];
    `SYSREG_ADDR_MHPEVENT3      : read_if.data = r_mhpevent3;
    `SYSREG_ADDR_MHPEVENT4      : read_if.data = r_mhpevent4;
    `SYSREG_ADDR_MHPEVENT5      : read_if.data = r_mhpevent5;
    `SYSREG_ADDR_MHPEVENT6      : read_if.data = r_mhpevent6;
    `SYSREG_ADDR_MHPEVENT7      : read_if.data = r_mhpevent7;
    `SYSREG_ADDR_MHPEVENT8      : read_if.data = r_mhpevent8;
    `SYSREG_ADDR_MHPEVENT9      : read_if.data = r_mhpevent9;
    `SYSREG_ADDR_MHPEVENT10     : read_if.data = r_mhpevent10;
    `SYSREG_ADDR_MHPEVENT11     : read_if.data = r_mhpevent11;
    `SYSREG_ADDR_MHPEVENT12     : read_if.data = r_mhpevent12;
    `SYSREG_ADDR_MHPEVENT13     : read_if.data = r_mhpevent13;
    `SYSREG_ADDR_MHPEVENT14     : read_if.data = r_mhpevent14;
    `SYSREG_ADDR_MHPEVENT15     : read_if.data = r_mhpevent15;
    `SYSREG_ADDR_MHPEVENT16     : read_if.data = r_mhpevent16;
    `SYSREG_ADDR_MHPEVENT17     : read_if.data = r_mhpevent17;
    `SYSREG_ADDR_MHPEVENT18     : read_if.data = r_mhpevent18;
    `SYSREG_ADDR_MHPEVENT19     : read_if.data = r_mhpevent19;
    `SYSREG_ADDR_MHPEVENT20     : read_if.data = r_mhpevent20;
    `SYSREG_ADDR_MHPEVENT21     : read_if.data = r_mhpevent21;
    `SYSREG_ADDR_MHPEVENT22     : read_if.data = r_mhpevent22;
    `SYSREG_ADDR_MHPEVENT23     : read_if.data = r_mhpevent23;
    `SYSREG_ADDR_MHPEVENT24     : read_if.data = r_mhpevent24;
    `SYSREG_ADDR_MHPEVENT25     : read_if.data = r_mhpevent25;
    `SYSREG_ADDR_MHPEVENT26     : read_if.data = r_mhpevent26;
    `SYSREG_ADDR_MHPEVENT27     : read_if.data = r_mhpevent27;
    `SYSREG_ADDR_MHPEVENT28     : read_if.data = r_mhpevent28;
    `SYSREG_ADDR_MHPEVENT29     : read_if.data = r_mhpevent29;
    `SYSREG_ADDR_MHPEVENT30     : read_if.data = r_mhpevent30;
    `SYSREG_ADDR_MHPEVENT31     : read_if.data = r_mhpevent31;
    `SYSREG_ADDR_PMPCFG0        : read_if.data = r_pmpcfg0;
    `SYSREG_ADDR_PMPCFG1        : read_if.data = r_pmpcfg1;
    `SYSREG_ADDR_PMPCFG2        : read_if.data = r_pmpcfg2;
    `SYSREG_ADDR_PMPCFG3        : read_if.data = r_pmpcfg3;
    `SYSREG_ADDR_PMPADDR0       : read_if.data = r_pmpaddr0;
    `SYSREG_ADDR_PMPADDR1       : read_if.data = r_pmpaddr1;
    `SYSREG_ADDR_PMPADDR2       : read_if.data = r_pmpaddr2;
    `SYSREG_ADDR_PMPADDR3       : read_if.data = r_pmpaddr3;
    `SYSREG_ADDR_PMPADDR4       : read_if.data = r_pmpaddr4;
    `SYSREG_ADDR_PMPADDR5       : read_if.data = r_pmpaddr5;
    `SYSREG_ADDR_PMPADDR6       : read_if.data = r_pmpaddr6;
    `SYSREG_ADDR_PMPADDR7       : read_if.data = r_pmpaddr7;
    `SYSREG_ADDR_PMPADDR8       : read_if.data = r_pmpaddr8;
    `SYSREG_ADDR_PMPADDR9       : read_if.data = r_pmpaddr9;
    `SYSREG_ADDR_PMPADDR10      : read_if.data = r_pmpaddr10;
    `SYSREG_ADDR_PMPADDR11      : read_if.data = r_pmpaddr11;
    `SYSREG_ADDR_PMPADDR12      : read_if.data = r_pmpaddr12;
    `SYSREG_ADDR_PMPADDR13      : read_if.data = r_pmpaddr13;
    `SYSREG_ADDR_PMPADDR14      : read_if.data = r_pmpaddr14;
    `SYSREG_ADDR_PMPADDR15      : read_if.data = r_pmpaddr15;
    `SYSREG_ADDR_STATS          : read_if.data = r_stats;
    default : begin
      read_if.data = {riscv_pkg::XLEN_W{1'bx}};
      w_rd_ill_address = 1'b1;
    end
  endcase // case (read_if.addr)
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ustatus       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_USTATUS       ) begin r_ustatus       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uie           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UIE           ) begin r_uie           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_utvec.raw_bit <= 'h0;
  end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UTVEC) begin
    r_utvec.raw_bit <= write_if.data;
  end
end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vstart        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_VSTART        ) begin r_vstart        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vxsat         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_VXSAT         ) begin r_vxsat         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vxrm          <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_VXRM          ) begin r_vxrm          <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uscratch      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_USCRATCH      ) begin r_uscratch      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uepc          <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UEPC          ) begin r_uepc          <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ucause        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UCAUSE        ) begin r_ucause        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ubadaddr      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UBADADDR      ) begin r_ubadaddr      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uip           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UIP           ) begin r_uip           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_fflags  <= 'h0;
  end else begin
    if (fflags_update_if.valid) begin
      r_fflags <= fflags_update_if.fflags;
    end else if (write_if.valid & (write_if.addr ==  `SYSREG_ADDR_FFLAGS)) begin
      r_fflags <= write_if.data[ 4: 0];
    end else if (write_if.valid & (write_if.addr ==  `SYSREG_ADDR_FRM)) begin
      r_frm    <= write_if.data[ 2: 0];
    end else if (write_if.valid & (write_if.addr ==  `SYSREG_ADDR_FCSR)) begin
      r_fflags <= write_if.data[ 4: 0];
      r_frm    <= write_if.data[ 7: 5];
    end
  end
end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter3   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER3   ) begin r_hpmcounter3   <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter4   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER4   ) begin r_hpmcounter4   <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter5   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER5   ) begin r_hpmcounter5   <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter6   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER6   ) begin r_hpmcounter6   <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter7   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER7   ) begin r_hpmcounter7   <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter8   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER8   ) begin r_hpmcounter8   <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter9   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER9   ) begin r_hpmcounter9   <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter10  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER10  ) begin r_hpmcounter10  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter11  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER11  ) begin r_hpmcounter11  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter12  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER12  ) begin r_hpmcounter12  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter13  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER13  ) begin r_hpmcounter13  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter14  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER14  ) begin r_hpmcounter14  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter15  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER15  ) begin r_hpmcounter15  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter16  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER16  ) begin r_hpmcounter16  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter17  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER17  ) begin r_hpmcounter17  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter18  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER18  ) begin r_hpmcounter18  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter19  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER19  ) begin r_hpmcounter19  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter20  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER20  ) begin r_hpmcounter20  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter21  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER21  ) begin r_hpmcounter21  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter22  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER22  ) begin r_hpmcounter22  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter23  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER23  ) begin r_hpmcounter23  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter24  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER24  ) begin r_hpmcounter24  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter25  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER25  ) begin r_hpmcounter25  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter26  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER26  ) begin r_hpmcounter26  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter27  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER27  ) begin r_hpmcounter27  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter28  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER28  ) begin r_hpmcounter28  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter29  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER29  ) begin r_hpmcounter29  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter30  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER30  ) begin r_hpmcounter30  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter31  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER31  ) begin r_hpmcounter31  <= write_if.data; end end

// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh3  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH3  ) begin r_hpmcounterh3  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh4  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH4  ) begin r_hpmcounterh4  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh5  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH5  ) begin r_hpmcounterh5  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh6  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH6  ) begin r_hpmcounterh6  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh7  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH7  ) begin r_hpmcounterh7  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh8  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH8  ) begin r_hpmcounterh8  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh9  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH9  ) begin r_hpmcounterh9  <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh10 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH10 ) begin r_hpmcounterh10 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh11 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH11 ) begin r_hpmcounterh11 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh12 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH12 ) begin r_hpmcounterh12 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh13 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH13 ) begin r_hpmcounterh13 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh14 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH14 ) begin r_hpmcounterh14 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh15 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH15 ) begin r_hpmcounterh15 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh16 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH16 ) begin r_hpmcounterh16 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh17 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH17 ) begin r_hpmcounterh17 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh18 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH18 ) begin r_hpmcounterh18 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh19 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH19 ) begin r_hpmcounterh19 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh20 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH20 ) begin r_hpmcounterh20 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh21 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH21 ) begin r_hpmcounterh21 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh22 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH22 ) begin r_hpmcounterh22 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh23 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH23 ) begin r_hpmcounterh23 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh24 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH24 ) begin r_hpmcounterh24 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh25 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH25 ) begin r_hpmcounterh25 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh26 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH26 ) begin r_hpmcounterh26 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh27 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH27 ) begin r_hpmcounterh27 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh28 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH28 ) begin r_hpmcounterh28 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh29 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH29 ) begin r_hpmcounterh29 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh30 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH30 ) begin r_hpmcounterh30 <= write_if.data; end end
// always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh31 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH31 ) begin r_hpmcounterh31 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sedeleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SEDELEG       ) begin r_sedeleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sideleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SIDELEG       ) begin r_sideleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sie           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SIE           ) begin r_sie           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_stvec.raw_bit <= 'h0;
  end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_STVEC) begin
    r_stvec.raw_bit <= write_if.data;
  end
end
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_scounteren.raw_bit <= 'h0;
  end else if (write_if.valid & write_if.addr == `SYSREG_ADDR_SCOUNTEREN) begin
    r_scounteren.raw_bit <= write_if.data[31: 0];
  end
end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sscratch      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SSCRATCH      ) begin r_sscratch      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sip           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SIP           ) begin r_sip           <= write_if.data; end end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_satp <= 'h0;
  end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SATP) begin
    r_satp <= write_if.data;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hstatus       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HSTATUS       ) begin r_hstatus       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hedeleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HEDELEG       ) begin r_hedeleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hideleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HIDELEG       ) begin r_hideleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hie           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HIE           ) begin r_hie           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_htvec.raw_bit <= 'h0;
  end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HTVEC) begin
    r_htvec.raw_bit <= write_if.data;
  end
end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hscratch      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HSCRATCH      ) begin r_hscratch      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hepc          <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HEPC          ) begin r_hepc          <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hcause        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HCAUSE        ) begin r_hcause        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hbadaddr      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HBADADDR      ) begin r_hbadaddr      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hip           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HIP           ) begin r_hip           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hptbr         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPTBR         ) begin r_hptbr         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mvendorid     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MVENDORID     ) begin r_mvendorid     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_marchid <= 'h5;
  end else if (write_if.valid & (write_if.addr == `SYSREG_ADDR_MARCHID)) begin
    r_marchid <= write_if.data;
  end
end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mimpid        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIMPID        ) begin r_mimpid        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhartid       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHARTID       ) begin r_mhartid       <= write_if.data; end end

xlen_t w_misa_reset;
generate if (riscv_fpu_pkg::FLEN_W == 0) begin
  assign w_misa_reset = (`RV_AMO << ("A" - "A")) |
              ('h1 << ("C" - "A")) |
              ('h1 << ("I" - "A")) |
              ('h1 << ("M" - "A")) |
              ('h1 << ("S" - "A")) |
              ('h1 << ("U" - "A")) |
              ((XLEN_W / 32) << (XLEN_W-2));
end else if (riscv_fpu_pkg::FLEN_W == 32) begin
  assign w_misa_reset = (`RV_AMO << ("A" - "A")) |
              ('h1 << ("C" - "A")) |
              ('h1 << ("F" - "A")) |
              ('h1 << ("I" - "A")) |
              ('h1 << ("M" - "A")) |
              ('h1 << ("S" - "A")) |
              ('h1 << ("U" - "A")) |
              ((XLEN_W / 32) << (XLEN_W-2));
end else if (riscv_fpu_pkg::FLEN_W ==64) begin
  assign w_misa_reset = (`RV_AMO << ("A" - "A")) |
              ('h1 << ("C" - "A")) |
              ('h1 << ("D" - "A")) |
              ('h1 << ("F" - "A")) |
              ('h1 << ("I" - "A")) |
              ('h1 << ("M" - "A")) |
              ('h1 << ("S" - "A")) |
              ('h1 << ("U" - "A")) |
              ((XLEN_W / 32) << (XLEN_W-2));
end
endgenerate

xlen_t w_misa_next;
always_comb begin
  w_misa_next = write_if.data;
  if (riscv_fpu_pkg::FLEN_W == 0) begin
    w_misa_next[("F" - "A")] = 1'b0;
    w_misa_next[("D" - "A")] = 1'b0;
  end else if (riscv_fpu_pkg::FLEN_W == 32) begin
    w_misa_next[("D" - "A")] = 1'b0;
  end
  w_misa_next[("A" - "A")] = `RV_AMO;
  w_misa_next[("B" - "A")] = 1'b0;
  w_misa_next[("V" - "A")] = 1'b0;
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_misa <= w_misa_reset;
  end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MISA) begin
    r_misa <= w_misa_next;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_medeleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MEDELEG       ) begin r_medeleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mideleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIDELEG       ) begin r_mideleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mie           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIE           ) begin r_mie           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_mtvec.raw_bit <= 'h0;
  end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MTVEC) begin
    r_mtvec.raw_bit <= write_if.data;
  end
end
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_mcounteren.raw_bit <= 'h0;
  end else if (write_if.valid & write_if.addr == `SYSREG_ADDR_MCOUNTEREN) begin
    r_mcounteren.raw_bit <= write_if.data[31: 0];
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mscratch      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MSCRATCH      ) begin r_mscratch      <= write_if.data; end end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_mip <= 'h0;

  end else if (write_if.valid & (write_if.addr == `SYSREG_ADDR_MIP)) begin
    r_mip <= write_if.data;
  end else if (clint_if.time_irq_clear) begin
    r_mip[ 7] <= 1'b0;
  end else if (clint_if.time_irq_valid) begin
    r_mip[ 7] <= 1'b1;
  end else if (plic_if.int_valid) begin
    r_mip[11] <= 1'b1;
  end

  end else begin
    if (write_if.valid & (write_if.addr == `SYSREG_ADDR_MIP)) begin
      r_mip <= write_if.data;
    end else if (clint_if.time_irq_clear) begin
      r_mip[ 7] <= 1'b0;
    end else if (clint_if.time_irq_valid) begin
      r_mip[ 7] <= 1'b1;
    end
    if (plic_if.int_valid) begin
      r_mip[11] <= 1'b1;
    end else if (plic_if.int_complete) begin
      r_mip[11] <= 1'b0;
    end
  end // else: !if(!i_reset_n)

end

assign plic_if.ie = r_mie[11];


always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mbase         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MBASE         ) begin r_mbase         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mbound        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MBOUND        ) begin r_mbound        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mibase        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIBASE        ) begin r_mibase        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mibound       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIBOUND       ) begin r_mibound       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mdbase        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MDBASE        ) begin r_mdbase        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mdbound       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MDBOUND       ) begin r_mdbound       <= write_if.data; end end

logic [$clog2(scariv_conf_pkg::DISP_SIZE): 0] w_inst_bit_cnt;
bit_cnt #(.WIDTH(scariv_conf_pkg::DISP_SIZE)) u_minstret_bit_cnt(.in(i_commit.grp_id & ~i_commit.dead_id), .out(w_inst_bit_cnt));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_instret <= 'h0;
  end else if (write_if.valid & (write_if.addr == `SYSREG_ADDR_MINSTRET)) begin
    /* verilator lint_off WIDTH */
    r_instret <= write_if.data;
  end else if (write_if.valid & (write_if.addr == `SYSREG_ADDR_INSTRET)) begin

  end else if (i_commit.commit) begin
    /* verilator lint_off WIDTH */
    r_instret <= r_instret + w_inst_bit_cnt;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_cycle <= 'h0;
  end else if (write_if.valid & (write_if.addr == `SYSREG_ADDR_MCYCLE)) begin
    /* verilator lint_off WIDTH */
    r_cycle <= write_if.data;
  end else begin
    r_cycle <= r_cycle + 'h1;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_time <= 'h0;
  // end else if (write_if.valid & (write_if.addr == `SYSREG_ADDR_MTIME)) begin
  //   r_time <= write_if.data;
  end else begin
    r_time <= r_time + 'h1;
  end
end

// Access Priviledges check
assign w_wr_mcsr_ill_access = (write_if.addr[9:8] == 2'b11) & ((r_priv == riscv_common_pkg::PRIV_U) | (r_priv == riscv_common_pkg::PRIV_S));
assign w_wr_scsr_ill_access = (write_if.addr[9:8] == 2'b01) & ((r_priv == riscv_common_pkg::PRIV_U));
assign w_wr_mcsr_ill_write  = (write_if.addr[11:10] == 2'b11);

assign write_if.resp_error = write_if.valid & ((write_if.addr == `SYSREG_ADDR_CYCLE   ) |
                                               (write_if.addr == `SYSREG_ADDR_TIME    ) |
                                               (write_if.addr == `SYSREG_ADDR_INSTRET ) |
                                               (write_if.addr == `SYSREG_ADDR_CYCLEH  ) |
                                               (write_if.addr == `SYSREG_ADDR_INSTRETH) |
                                               w_wr_mcsr_ill_access | w_wr_scsr_ill_access | w_wr_mcsr_ill_write
                                               );

assign w_rd_satp_tvm_1      = (read_if.addr == `SYSREG_ADDR_SATP) & r_mstatus[`MSTATUS_TVM] & (r_priv == riscv_common_pkg::PRIV_S);
assign w_rd_counter = ((r_priv == riscv_common_pkg::PRIV_U) | (r_priv == riscv_common_pkg::PRIV_S)) &
                      ((read_if.addr == `SYSREG_ADDR_CYCLE)   & r_mcounteren.field.cy |
                       (read_if.addr == `SYSREG_ADDR_TIME)    & r_mcounteren.field.tm |
                       (read_if.addr == `SYSREG_ADDR_INSTRET) & r_mcounteren.field.ir);
assign w_rd_mcsr_ill_access = (read_if.addr[9:8] == 2'b11) & ((r_priv == riscv_common_pkg::PRIV_U) | (r_priv == riscv_common_pkg::PRIV_S));
assign w_rd_scsr_ill_access = (read_if.addr[9:8] == 2'b01) & ((r_priv == riscv_common_pkg::PRIV_U));
assign w_rd_fpu_ill_access  = ((read_if.addr == `SYSREG_ADDR_FFLAGS) |
                               (read_if.addr == `SYSREG_ADDR_FRM) |
                               (read_if.addr == `SYSREG_ADDR_FCSR)) & !(r_misa["F" - "A"] | r_misa["D" - "A"]);

assign read_if.resp_error = read_if.valid & (w_rd_mcsr_ill_access | w_rd_scsr_ill_access |
                                             w_rd_counter | w_rd_satp_tvm_1 |
                                             w_rd_fpu_ill_access |
                                             w_rd_ill_address);

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[ 3] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER3  ) begin r_hpmcounter[ 3] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[ 4] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER4  ) begin r_hpmcounter[ 4] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[ 5] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER5  ) begin r_hpmcounter[ 5] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[ 6] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER6  ) begin r_hpmcounter[ 6] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[ 7] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER7  ) begin r_hpmcounter[ 7] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[ 8] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER8  ) begin r_hpmcounter[ 8] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[ 9] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER9  ) begin r_hpmcounter[ 9] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[10] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER10 ) begin r_hpmcounter[10] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[11] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER11 ) begin r_hpmcounter[11] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[12] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER12 ) begin r_hpmcounter[12] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[13] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER13 ) begin r_hpmcounter[13] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[14] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER14 ) begin r_hpmcounter[14] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[15] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER15 ) begin r_hpmcounter[15] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[16] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER16 ) begin r_hpmcounter[16] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[17] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER17 ) begin r_hpmcounter[17] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[18] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER18 ) begin r_hpmcounter[18] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[19] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER19 ) begin r_hpmcounter[19] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[20] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER20 ) begin r_hpmcounter[20] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[21] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER21 ) begin r_hpmcounter[21] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[22] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER22 ) begin r_hpmcounter[22] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[23] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER23 ) begin r_hpmcounter[23] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[24] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER24 ) begin r_hpmcounter[24] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[25] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER25 ) begin r_hpmcounter[25] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[26] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER26 ) begin r_hpmcounter[26] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[27] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER27 ) begin r_hpmcounter[27] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[28] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER28 ) begin r_hpmcounter[28] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[29] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER29 ) begin r_hpmcounter[29] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[30] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER30 ) begin r_hpmcounter[30] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter[31] <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER31 ) begin r_hpmcounter[31] <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent3     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT3     ) begin r_mhpevent3     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent4     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT4     ) begin r_mhpevent4     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent5     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT5     ) begin r_mhpevent5     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent6     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT6     ) begin r_mhpevent6     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent7     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT7     ) begin r_mhpevent7     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent8     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT8     ) begin r_mhpevent8     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent9     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT9     ) begin r_mhpevent9     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent10    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT10    ) begin r_mhpevent10    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent11    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT11    ) begin r_mhpevent11    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent12    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT12    ) begin r_mhpevent12    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent13    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT13    ) begin r_mhpevent13    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent14    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT14    ) begin r_mhpevent14    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent15    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT15    ) begin r_mhpevent15    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent16    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT16    ) begin r_mhpevent16    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent17    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT17    ) begin r_mhpevent17    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent18    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT18    ) begin r_mhpevent18    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent19    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT19    ) begin r_mhpevent19    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent20    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT20    ) begin r_mhpevent20    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent21    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT21    ) begin r_mhpevent21    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent22    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT22    ) begin r_mhpevent22    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent23    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT23    ) begin r_mhpevent23    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent24    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT24    ) begin r_mhpevent24    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent25    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT25    ) begin r_mhpevent25    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent26    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT26    ) begin r_mhpevent26    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent27    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT27    ) begin r_mhpevent27    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent28    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT28    ) begin r_mhpevent28    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent29    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT29    ) begin r_mhpevent29    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent30    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT30    ) begin r_mhpevent30    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent31    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT31    ) begin r_mhpevent31    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg0       <= 'h1f; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPCFG0       ) begin r_pmpcfg0       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg1       <= 'h1f; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPCFG1       ) begin r_pmpcfg1       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg2       <= 'h1f; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPCFG2       ) begin r_pmpcfg2       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg3       <= 'h1f; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPCFG3       ) begin r_pmpcfg3       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr0      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR0      ) begin r_pmpaddr0      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr1      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR1      ) begin r_pmpaddr1      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr2      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR2      ) begin r_pmpaddr2      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr3      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR3      ) begin r_pmpaddr3      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr4      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR4      ) begin r_pmpaddr4      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr5      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR5      ) begin r_pmpaddr5      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr6      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR6      ) begin r_pmpaddr6      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr7      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR7      ) begin r_pmpaddr7      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr8      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR8      ) begin r_pmpaddr8      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr9      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR9      ) begin r_pmpaddr9      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr10     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR10     ) begin r_pmpaddr10     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr11     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR11     ) begin r_pmpaddr11     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr12     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR12     ) begin r_pmpaddr12     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr13     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR13     ) begin r_pmpaddr13     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr14     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR14     ) begin r_pmpaddr14     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr15     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR15     ) begin r_pmpaddr15     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_stats         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_STATS         ) begin r_stats         <= write_if.data; end end

assign csr_info.update  = i_commit.commit & |(i_commit.except_valid & i_commit.flush_valid);
assign csr_info.mstatus = w_mstatus;
assign csr_info.mepc    = r_mepc  & ~(r_misa[2] ? 1 : 3); // MISA.C is off, only accepted 4-byte align
assign csr_info.mtvec   = r_mtvec & ~(r_misa[2] ? 1 : 3); // MISA.C is off, only accepted 4-byte align
assign csr_info.stvec   = r_stvec & ~(r_misa[2] ? 1 : 3); // MISA.C is off, only accepted 4-byte align
assign csr_info.utvec   = r_utvec & ~(r_misa[2] ? 1 : 3); // MISA.C is off, only accepted 4-byte align
assign csr_info.sepc    = r_sepc  & ~(r_misa[2] ? 1 : 3); // MISA.C is off, only accepted 4-byte align
assign csr_info.uepc    = r_uepc  & ~(r_misa[2] ? 1 : 3); // MISA.C is off, only accepted 4-byte align
assign csr_info.satp    = r_satp;
// assign csr_info.priv    = r_priv;
// Priviledge should be pass immediately when exception is valid
assign csr_info.priv    = w_priv_next;
assign csr_info.medeleg = r_medeleg;
assign csr_info.sedeleg = r_sedeleg;
assign csr_info.fcsr    = {24'h0, r_frm, r_fflags};

// assign csr_info.int_request = |(r_mip & r_mie) & (r_priv == riscv_common_pkg::PRIV_M) |
//                               |(r_sip & r_sie) & (r_priv == riscv_common_pkg::PRIV_S) |
//                               |(r_uip & r_uie) & (r_priv == riscv_common_pkg::PRIV_U);

riscv_pkg::xlen_t w_m_int_en;
riscv_pkg::xlen_t w_s_int_en;
riscv_pkg::xlen_t w_m_pend_ints;
logic                          w_m_csr_int_en;
logic                          w_s_csr_int_en;
riscv_pkg::xlen_t w_s_pend_ints;

assign w_m_csr_int_en = (r_priv < riscv_common_pkg::PRIV_M) |
                        ((r_priv == riscv_common_pkg::PRIV_M) & r_mstatus[`MSTATUS_MIE]);
assign w_m_pend_ints = r_mip & r_mie;
assign w_m_int_en  = w_m_pend_ints & ~r_mideleg & {riscv_pkg::XLEN_W{w_m_csr_int_en}};

assign w_s_csr_int_en = (r_priv < riscv_common_pkg::PRIV_S) |
                        ((r_priv == riscv_common_pkg::PRIV_S) & r_mstatus[`MSTATUS_SIE]);
assign w_s_int_en = w_m_int_en == 'h0 ? w_m_pend_ints & r_mideleg & {riscv_pkg::XLEN_W{w_s_csr_int_en}} :
                    'h0;

assign int_if.s_software_int_valid = w_m_int_en[ 1] | w_s_int_en[ 1];
assign int_if.m_software_int_valid = w_m_int_en[ 3] | w_s_int_en[ 3];
assign int_if.s_timer_int_valid    = w_m_int_en[ 5] | w_s_int_en[ 5];
assign int_if.m_timer_int_valid    = w_m_int_en[ 7] | w_s_int_en[ 7];
assign int_if.s_external_int_valid = w_m_int_en[ 9] | w_s_int_en[ 9];
assign int_if.m_external_int_valid = w_m_int_en[11] | w_s_int_en[11];

logic w_delegate;
assign w_delegate = scariv_conf_pkg::USING_VM & (r_priv <= riscv_common_pkg::PRIV_S) &
                    r_medeleg[int'(i_commit.except_type)];

always_comb begin
  w_mstatus = r_mstatus;
  w_mstatus[riscv_pkg::MSTATUS_SD] = (&w_mstatus[`MSTATUS_FS]) | (&w_mstatus[`MSTATUS_XS]);
end


xlen_t deleg_int_encoded;
xlen_t int_encoded;

assign deleg_int_encoded = (r_mideleg & w_m_int_en) == (1 << riscv_common_pkg::MACHINE_SOFT_INT    ) ? riscv_common_pkg::MACHINE_SOFT_INT     :
                           (r_mideleg & w_m_int_en) == (1 << riscv_common_pkg::MACHINE_TIMER_INT   ) ? riscv_common_pkg::MACHINE_TIMER_INT    :
                           (r_mideleg & w_m_int_en) == (1 << riscv_common_pkg::MACHINE_EXTERNAL_INT) ? riscv_common_pkg::MACHINE_EXTERNAL_INT :
                           'h0;

assign int_encoded = w_m_int_en == (1 << riscv_common_pkg::MACHINE_SOFT_INT    ) ? riscv_common_pkg::MACHINE_SOFT_INT     :
                     w_m_int_en == (1 << riscv_common_pkg::MACHINE_TIMER_INT   ) ? riscv_common_pkg::MACHINE_TIMER_INT    :
                     w_m_int_en == (1 << riscv_common_pkg::MACHINE_EXTERNAL_INT) ? riscv_common_pkg::MACHINE_EXTERNAL_INT :
                     'h0;


always_comb begin
  w_mstatus_next = w_mstatus;
  w_priv_next    = r_priv  ;
  w_sepc_next    = r_sepc  ;
  w_scause_next  = r_scause;
  w_stval_next   = r_stval ;
  w_mepc_next    = r_mepc  ;
  w_mcause_next  = r_mcause;
  w_mtval_next   = r_mtval ;


  if (i_commit.commit & i_commit.int_valid & |(i_commit.grp_id & ~i_commit.dead_id)) begin

    if (r_priv <= riscv_common_pkg::PRIV_S & ((r_mideleg & w_m_int_en) != 'h0)) begin
      // Delegation

      w_sepc_next = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){i_commit.epc[riscv_pkg::VADDR_W-1]}},
                     i_commit.epc[riscv_pkg::VADDR_W-1: 0]};

      // CSRWrite (SYSREG_ADDR_SEPC,  epc);
      w_scause_next = 1 << (riscv_pkg::XLEN_W - 1) | deleg_int_encoded;
      w_stval_next = 'h0;
      // CSRRead  (SYSREG_ADDR_STVEC,to &tvec);
      w_priv_next = riscv_common_pkg::PRIV_S;

      w_mstatus_next[`SSTATUS_SPIE] = r_mstatus[`SSTATUS_SIE];
      w_mstatus_next[`SSTATUS_SPP]  = r_priv;
      w_mstatus_next[`SSTATUS_SIE]  = 'h0;
    end else begin // if (r_priv <= riscv_common_pkg::PRIV_S & ((r_mideleg & w_m_int_en) != 'h0))

      w_mepc_next = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){i_commit.epc[riscv_pkg::VADDR_W-1]}},
                     i_commit.epc[riscv_pkg::VADDR_W-1: 0]};

      // CSRWrite (SYSREG_ADDR_MEPC,   epc);
      w_mcause_next = 1 << (riscv_pkg::XLEN_W - 1) | int_encoded;
      w_mtval_next = 'h0;

      // CSRRead  (SYSREG_ADDR_MTVEC, &tvec);
      w_mstatus_next[`MSTATUS_MPIE] = r_mstatus[`MSTATUS_MIE];
      w_mstatus_next[`MSTATUS_MPP]  = r_priv;
      w_mstatus_next[`MSTATUS_MIE]  = 'h0;

    end // else: !if(r_priv <= riscv_common_pkg::PRIV_S & ((r_mideleg & w_m_int_en) 1= 'h0))

  end else if (i_commit.commit & |(i_commit.except_valid & i_commit.flush_valid)) begin
    if (~|(i_commit.except_valid & i_commit.dead_id) & (i_commit.except_type == scariv_pkg::MRET)) begin
      // r_mepc <= epc;
      /* verilator lint_off WIDTH */
      // r_mcause <= i_commit.except_type;
      // r_mtval <= io.tval;
      w_mstatus_next[`MSTATUS_MPIE] = 1'b1;
      w_mstatus_next[`MSTATUS_MPP ] = riscv_common_pkg::PRIV_U;
      w_mstatus_next[`MSTATUS_MIE ] = w_mstatus[`MSTATUS_MPIE];
      w_priv_next = riscv_common_pkg::priv_t'(w_mstatus[`MSTATUS_MPP]);
      // w_mtval_next = 'h0;
    end else if (~|(i_commit.except_valid & i_commit.dead_id) & (i_commit.except_type == scariv_pkg::SRET)) begin
      // r_mepc <= epc;
      /* verilator lint_off WIDTH */
      // r_mcause <= i_commit.except_type;
      // r_mtval <= io.tval;
      w_mstatus_next[`MSTATUS_SPIE] = 1'b1;
      w_mstatus_next[`MSTATUS_SPP ] = riscv_common_pkg::PRIV_U;
      w_mstatus_next[`MSTATUS_SIE ] = w_mstatus[`MSTATUS_SPIE];
      w_priv_next = riscv_common_pkg::priv_t'(w_mstatus[`MSTATUS_SPP]);
      w_stval_next = i_commit.tval;
    end else if (~|(i_commit.except_valid & i_commit.dead_id) & (i_commit.except_type == scariv_pkg::URET)) begin // if (i_commit.except_type == scariv_pkg::SRET)
      w_mtval_next = 'h0;
    end else if (w_delegate) begin
      w_sepc_next = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){i_commit.epc[riscv_pkg::VADDR_W-1]}},
                     i_commit.epc[riscv_pkg::VADDR_W-1: 0]};
      /* verilator lint_off WIDTH */
      w_scause_next = i_commit.except_type;
      if (i_commit.except_type == scariv_pkg::ILLEGAL_INST        ||
          i_commit.except_type == scariv_pkg::INST_ADDR_MISALIGN  ||
          i_commit.except_type == scariv_pkg::INST_ACC_FAULT      ||
          i_commit.except_type == scariv_pkg::INST_PAGE_FAULT     ||
          i_commit.except_type == scariv_pkg::LOAD_ADDR_MISALIGN  ||
          i_commit.except_type == scariv_pkg::LOAD_ACC_FAULT      ||
          i_commit.except_type == scariv_pkg::LOAD_PAGE_FAULT     ||
          i_commit.except_type == scariv_pkg::STAMO_ADDR_MISALIGN ||
          i_commit.except_type == scariv_pkg::STAMO_ACC_FAULT     ||
          i_commit.except_type == scariv_pkg::STAMO_PAGE_FAULT) begin
        w_stval_next = i_commit.tval;
      end else begin // if (i_commit.except_type == scariv_pkg::INST_ADDR_MISALIGN  ||...
        w_stval_next = 'h0;
      end // if (i_commit.except_type == INST_ADDR_MISALIGN  ||...
      w_mstatus_next[`MSTATUS_SPIE] = w_mstatus[`MSTATUS_SIE];
      w_mstatus_next[`MSTATUS_SPP ] = r_priv[0];
      w_mstatus_next[`MSTATUS_SIE ] = 1'b0;

      w_priv_next = riscv_common_pkg::PRIV_S;
    end else if (i_commit.except_type != scariv_pkg::SILENT_FLUSH &&
                 i_commit.except_type != scariv_pkg::ANOTHER_FLUSH) begin
      w_mepc_next = {{(riscv_pkg::XLEN_W-riscv_pkg::VADDR_W){i_commit.epc[riscv_pkg::VADDR_W-1]}},
                     i_commit.epc[riscv_pkg::VADDR_W-1: 0]};
      /* verilator lint_off WIDTH */
      w_mcause_next = i_commit.except_type;
      if (i_commit.except_type == scariv_pkg::ILLEGAL_INST        ||
          i_commit.except_type == scariv_pkg::INST_ADDR_MISALIGN  ||
          i_commit.except_type == scariv_pkg::INST_ACC_FAULT      ||
          i_commit.except_type == scariv_pkg::INST_PAGE_FAULT     ||
          i_commit.except_type == scariv_pkg::LOAD_ADDR_MISALIGN  ||
          i_commit.except_type == scariv_pkg::LOAD_ACC_FAULT      ||
          i_commit.except_type == scariv_pkg::LOAD_PAGE_FAULT     ||
          i_commit.except_type == scariv_pkg::STAMO_ADDR_MISALIGN ||
          i_commit.except_type == scariv_pkg::STAMO_ACC_FAULT     ||
          i_commit.except_type == scariv_pkg::STAMO_PAGE_FAULT) begin
        w_mtval_next = i_commit.tval;
      end else begin // if (i_commit.except_type == scariv_pkg::INST_ADDR_MISALIGN  ||...
        w_mtval_next = 'h0;
      end // if (i_commit.except_type == INST_ADDR_MISALIGN  ||...
      w_mstatus_next[`MSTATUS_MPIE] = w_mstatus[`MSTATUS_MIE];
      w_mstatus_next[`MSTATUS_MPP ] = r_priv;
      w_mstatus_next[`MSTATUS_MIE ] = 1'b0;
      w_priv_next = riscv_common_pkg::PRIV_M;
    end // else: !if(w_delegate)

  end else if (write_if.valid) begin
    case(write_if.addr)
      `SYSREG_ADDR_FFLAGS: begin
        w_mstatus_next[`MSTATUS_FS] = 2'b11;
      end
      `SYSREG_ADDR_FRM: begin
        w_mstatus_next[`MSTATUS_FS] = 2'b11;
      end
      `SYSREG_ADDR_FCSR: begin
        w_mstatus_next[`MSTATUS_FS] = 2'b11;
      end
      `SYSREG_ADDR_SEPC : begin
        w_sepc_next = write_if.data;
      end
      `SYSREG_ADDR_SCAUSE : begin
        w_scause_next = write_if.data;
      end
      `SYSREG_ADDR_STVAL : begin
        w_stval_next      = write_if.data;
      end
      `SYSREG_ADDR_MEPC : begin
        w_mepc_next       = write_if.data;
      end
      `SYSREG_ADDR_MCAUSE : begin
        w_mcause_next     = write_if.data;
      end
      `SYSREG_ADDR_MTVAL : begin
        w_mtval_next      = write_if.data;
      end
      `SYSREG_ADDR_MSTATUS : begin
        // r_mstatus <= write_if.data;
        w_mstatus_next[`MSTATUS_MIE ] = write_if.data[`MSTATUS_MIE ];
        w_mstatus_next[`MSTATUS_MPIE] = write_if.data[`MSTATUS_MPIE];

        w_mstatus_next[`MSTATUS_MPRV] = write_if.data[`MSTATUS_MPRV];
        w_mstatus_next[`MSTATUS_MPP ] = write_if.data[`MSTATUS_MPP];

        w_mstatus_next[`MSTATUS_SPP ] = write_if.data[`MSTATUS_SPP ];
        w_mstatus_next[`MSTATUS_SPIE] = write_if.data[`MSTATUS_SPIE];
        w_mstatus_next[`MSTATUS_SIE ] = write_if.data[`MSTATUS_SIE ];
        w_mstatus_next[`MSTATUS_TW  ] = write_if.data[`MSTATUS_TW  ];
        w_mstatus_next[`MSTATUS_TSR ] = write_if.data[`MSTATUS_TSR ];

        if (scariv_conf_pkg::USING_VM) begin
          w_mstatus_next[`MSTATUS_MXR] = write_if.data[`MSTATUS_MXR];
          w_mstatus_next[`MSTATUS_SUM] = write_if.data[`MSTATUS_SUM];
          w_mstatus_next[`MSTATUS_TVM] = write_if.data[`MSTATUS_TVM];
        end

        w_mstatus_next[`MSTATUS_FS] = write_if.data[`MSTATUS_FS];
      end // case: `SYSREG_ADDR_MSTATUS

      `SYSREG_ADDR_SSTATUS : begin
        w_mstatus_next[`MSTATUS_SIE ] = write_if.data[`MSTATUS_SIE ];
        w_mstatus_next[`MSTATUS_SPIE] = write_if.data[`MSTATUS_SPIE];
        w_mstatus_next[`MSTATUS_SPP ] = write_if.data[`MSTATUS_SPP ];
        w_mstatus_next[`MSTATUS_XS  ] = write_if.data[`MSTATUS_XS  ];
        w_mstatus_next[`MSTATUS_FS  ] = write_if.data[`MSTATUS_FS  ];
        w_mstatus_next[`MSTATUS_MPP ] = write_if.data[`MSTATUS_MPP ];
        w_mstatus_next[`MSTATUS_MXR ] = write_if.data[`MSTATUS_MXR ];
        w_mstatus_next[`MSTATUS_SUM ] = write_if.data[`MSTATUS_SUM ];
      end
      default : begin end
    endcase // case (write_if.addr)
  end // if (write_if.valid)
end // always_comb


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_priv <= riscv_common_pkg::PRIV_M;
    r_mstatus <= riscv_pkg::init_mstatus;

    r_sepc <= 'h0;
    r_scause <= 'h0;
    r_stval <= 'h0;

    r_mepc <= 'h0;
    r_mcause <= 'h0;
    r_mtval <= 'h0;
  end else begin
    r_priv <= w_priv_next;
    r_mstatus <= w_mstatus_next;

    r_sepc   <= w_sepc_next  ;
    r_scause <= w_scause_next;
    r_stval  <= w_stval_next ;

    r_mepc   <= w_mepc_next  ;
    r_mcause <= w_mcause_next;
    r_mtval  <= w_mtval_next ;
  end // else: !if(!i_reset_n)

end // always_ff @ (posedge i_clk, negedge i_reset_n)


endmodule // scariv_csr

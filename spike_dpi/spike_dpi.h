#pragma once
#include <svdpi.h>

extern "C" {
  void initial_spike (const char *filename, int rv_xlen);
  void step_spike(long long time, long long rtl_pc,
                  int rtl_priv, long long rtl_mstatus,
                  int rtl_exception, int rtl_exception_cause,
                  int rtl_cmt_id, int rtl_grp_id,
                  int rtl_insn,
                  int rtl_wr_valid, int rtl_wr_gpr_addr,
                  int rtl_wr_gpr_rnid, long long rtl_wr_val);
  void stop_sim(int code);

#ifndef VERILATOR
  void open_log_fp(const char *filename);
#endif // VERILATOR
  void record_stq_store(long long rtl_time,
                        long long paddr,
                        int ram_addr,
                        const char* l1d_data,
                        long long be,
                        int size);

  void record_l1d_load(long long rtl_time,
                       long long paddr,
                       int ram_addr,
                       const unsigned int* l1d_data,
                       int size);

  void record_l1d_evict(long long rtl_time,
                        long long paddr,
                        int ram_addr,
                        const unsigned int* l1d_data,
                        int size);
}

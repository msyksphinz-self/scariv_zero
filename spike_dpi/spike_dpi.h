#pragma once
#include <svdpi.h>

extern "C" {
  void initial_spike (const char *filename, int rv_xlen, int rv_flen, const char* ext_isa, int rv_vlen);
  void step_spike(long long time, long long rtl_pc,
                  int rtl_priv, long long rtl_mstatus,
                  int rtl_exception, int rtl_exception_cause,
                  int rtl_cmt_id, int rtl_grp_id,
                  int rtl_insn,
                  int rtl_wr_valid, int rtl_wr_type, int rtl_wr_gpr_addr,
                  int rtl_wr_gpr_rnid, long long rtl_wr_val,
                  const uint8_t* rtl_wr_vec_val_0,
                  const uint8_t* rtl_wr_vec_val_1,
                  const uint8_t* rtl_wr_vec_val_2,
                  const uint8_t* rtl_wr_vec_val_3,
                  const uint8_t* rtl_wr_vec_val_4,
                  const uint8_t* rtl_wr_vec_val_5,
                  const uint8_t* rtl_wr_vec_val_6,
                  const uint8_t* rtl_wr_vec_val_7);
  void stop_sim(int code, long long rtl_time);

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
                       const uint8_t* l1d_data,
                       long long l1d_be,
                       int merge_valid,
                       const uint8_t* merged_l1d_data,
                       long long merge_be,
                       int size);

  void record_l1d_evict(long long rtl_time,
                        long long paddr,
                        int ram_addr,
                        const unsigned int* l1d_data,
                        int size);

  void step_spike_wo_cmp(int steps);

  void check_mmu_trans (long long time, long long rtl_va,
                        int rtl_len, int rtl_acc_type,
                        long long rtl_pa);

  void spike_update_timer(long long value);
}

#pragma once
#include <svdpi.h>

extern "C" {
  void initial_ras(long long ras_length);
  void step_ras (long long rtl_time,
                 int rtl_cmt_id, int rtl_grp_id,
                 long long rtl_ras_index,
                 long long rtl_ras_addr
                 );
  void rtl_push_ras (long long rtl_time,
                     long long rtl_pc_vaddr,
                     long long rtl_ras_index,
                     long long rtl_ras_value);
  void rtl_pop_ras (long long rtl_time,
                    long long rtl_pc_vaddr,
                    long long rtl_ras_index,
                    long long rtl_ras_value);
  void rtl_flush_ras (long long rtl_time,
                      int rtl_cmt_id, int rtl_grp_id,
                      long long rtl_pc_vaddr,
                      long long rtl_ras_index);
}

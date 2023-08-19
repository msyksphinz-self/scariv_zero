#include <vector>
#include <cmath>
#include "sim.h"

#include "gshare_model.h"

FILE *gshare_log_fp;

// declared in spike_dpi.cpp
extern sim_t *spike_core;

size_t iss_bhr_length;
size_t iss_cache_block_byte_size;
long long iss_bhr;

typedef struct {
  uint8_t *bim;
} bim_block_t;

std::vector<bim_block_t *> bim_array; // uint8_t used but actually 2-bit is only used.

bool is_cond_branch_inst(uint64_t insn)
{
  if ((insn & MASK_BEQ   ) == MATCH_BEQ    ||
      (insn & MASK_BNE   ) == MATCH_BNE    ||
      (insn & MASK_BLT   ) == MATCH_BLT    ||
      (insn & MASK_BGE   ) == MATCH_BGE    ||
      (insn & MASK_BLTU  ) == MATCH_BLTU   ||
      (insn & MASK_BGEU  ) == MATCH_BGEU   ||
      (insn & MASK_C_BEQZ) == MATCH_C_BEQZ ||
      (insn & MASK_C_BNEZ) == MATCH_C_BNEZ) {
    return true;
  } else {
    return false;
  }
}

size_t cond_inst_size(uint64_t insn)
{
  if ((insn & MASK_BEQ   ) == MATCH_BEQ    ||
      (insn & MASK_BNE   ) == MATCH_BNE    ||
      (insn & MASK_BLT   ) == MATCH_BLT    ||
      (insn & MASK_BGE   ) == MATCH_BGE    ||
      (insn & MASK_BLTU  ) == MATCH_BLTU   ||
      (insn & MASK_BGEU  ) == MATCH_BGEU) {
    return 4;
  }
  if ((insn & MASK_C_BEQZ) == MATCH_C_BEQZ ||
      (insn & MASK_C_BNEZ) == MATCH_C_BNEZ) {
    return 2;
  }

  return 0;
}


void initial_gshare(long long bhr_length,
                    long long cache_block_byte_size)
{
  gshare_log_fp = fopen("gshare_check.log", "w");

  iss_bhr_length = static_cast<size_t>(bhr_length);
  iss_cache_block_byte_size = static_cast<size_t>(cache_block_byte_size);

  fprintf (gshare_log_fp, "Info : GSHARE length is set %ld\n", iss_bhr_length);
  fprintf (gshare_log_fp, "Info : Cache Block Size is set %ld\n", iss_cache_block_byte_size);

  for(int i = 0; i < bhr_length; i++) {
    bim_block_t *bim_block = new bim_block_t();
    bim_block->bim = new uint8_t [iss_cache_block_byte_size / 2];
    for (int j = 0; j < iss_cache_block_byte_size / 2; j++) {
      bim_block->bim[j] = 0x2;  // default: weakly taken
    }
    bim_array.push_back(bim_block);
  }
}

// 数値を２進数文字列に変換
std::string to_binString(unsigned int val, const int length)
{
    if( !val )
        return std::string("0");
    std::string str;
    int l = 0;
    while( val != 0 ) {
      if( (val & 1) == 0 )  // val は偶数か？
        str.insert(str.begin(), '0');  //  偶数の場合
      else
        str.insert(str.begin(), '1');  //  奇数の場合
      val >>= 1;
      l++;
    }
    while (l < length) {
      str.insert(str.begin(), '0');
      l++;
    }
    return str;
}


void step_gshare (long long rtl_time,
                  int rtl_cmt_id, int rtl_grp_id,
                  long long rtl_gshare_bhr)
{
  processor_t *p = spike_core->get_core(0);
  auto iss_next_pc = p->get_state()->pc;
  auto iss_pc      = p->get_state()->prev_pc;
  auto iss_insn    = p->get_state()->insn;

  if (is_cond_branch_inst(iss_insn.bits())) {
    const size_t iss_cache_block_byte_length = log2(iss_cache_block_byte_size);
    const size_t iss_bhr_mask = (1 << iss_bhr_length) - 1;

    size_t bim_array_index = ((iss_pc >> iss_cache_block_byte_length) >> 1) & iss_bhr_mask;
    size_t bim_block_internal_index = (iss_pc >> 1) & iss_bhr_mask;

    uint8_t bim_counter = bim_array.at(bim_array_index)->bim[bim_block_internal_index];
    bool iss_predict_taken = (bim_counter >> 1) & 1;

    bool is_branch_taken = iss_next_pc != iss_pc + cond_inst_size(iss_insn.bits());
    iss_bhr = (iss_bhr << 1) | is_branch_taken;

    fprintf(gshare_log_fp, "%lld : PC=%08lx (%02d,%02d) : ", rtl_time, iss_pc, rtl_cmt_id, rtl_grp_id);
    if ((iss_bhr & (1 << iss_bhr_length) - 1) != rtl_gshare_bhr) {
      fprintf(gshare_log_fp, "Warning : BHR different: RTL = %s, ISS = %s\n",
              to_binString(rtl_gshare_bhr, iss_bhr_length).c_str(),
              to_binString(iss_bhr & ((1 << iss_bhr_length)-1), iss_bhr_length).c_str());
    } else {
      fprintf(gshare_log_fp, "BHR RTL = %s\n", to_binString(rtl_gshare_bhr, iss_bhr_length).c_str());
    }

    fprintf (gshare_log_fp, "GSHARE MODEL : index = (%x, %x), predict = %s, result = %s, %s\n",
             static_cast<unsigned int>(bim_array_index), static_cast<unsigned int>(bim_block_internal_index),
             iss_predict_taken ? "TAKEN" : "NOT TAKEN",
             is_branch_taken   ? "TAKEN" : "NOT TAKEN",
             iss_predict_taken == is_branch_taken ? "MATCH" : "FAIL");

  }
}

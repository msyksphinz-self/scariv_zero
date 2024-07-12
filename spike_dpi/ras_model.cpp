#include "sim.h"

#include "ras_model.h"

uint64_t *iss_ras_stack;
size_t    iss_ras_length;
size_t    iss_ras_head;

extern int g_rv_xlen; // defined in spike_dpi.c

FILE *ras_log_fp;

// declared in spike_dpi.cpp
extern sim_t *spike_core;

bool is_call (uint64_t insn)
{
  if ((((insn & MASK_JAL   ) == MATCH_JAL )  ||  // JAL  x1, imm
       ((insn & MASK_JALR  ) == MATCH_JALR)) &&  // JALR x1, rs1
      (((insn >> 7) & 0x1f) == 0x1)) {
    return true;
  }
  if ((insn & MASK_C_JAL) == MATCH_C_JAL) {  // C.JAL x1, imm
    return g_rv_xlen == 32;
  }
  if ((insn & MASK_C_JALR) == MATCH_C_JALR) {  // C.JALR rs1
    return true;
  }
  return false;
}


bool is_ret (uint64_t insn)
{
  if (((insn & MASK_JALR  ) == MATCH_JALR) &&
      (((insn >>  7) & 0x1f) == 0x0) &&
      (((insn >> 15) & 0x1f) == 0x1)) {   // JALR x0, x1
    return true;
  }
  if (((insn & MASK_C_JR) == MATCH_C_JR) &&
      (((insn >>  7) & 0x1f) == 0x1)) {   // C.JR x1
    return true;
  }
  return false;
}


uint64_t inst_size (uint64_t insn)
{
  if ((insn & MASK_JAL ) == MATCH_JAL  ||
      (insn & MASK_JALR) == MATCH_JALR) {
    return 4;
  }
  if ((insn & MASK_C_JAL)  == MATCH_C_JAL  ||
      (insn & MASK_C_JALR) == MATCH_C_JALR ||
      (insn & MASK_C_JR)   == MATCH_C_JR) {
    return 2;
  }

  return 0;
}


void initial_ras(long long ras_length)
{
  ras_log_fp = fopen("ras_check.log", "w");

  iss_ras_length = ras_length;
  iss_ras_stack = new uint64_t[ras_length];
  iss_ras_head = 0;
  fprintf (ras_log_fp, "Info : RAS size is set %ld\n", iss_ras_length);
}

void step_ras (long long rtl_commit_time,
               int rtl_commit_cmt_id, int rtl_commit_grp_id,
               long long rtl_commit_ras_index, long long rtl_commit_ras_addr)
{
  processor_t *p = spike_core->get_core(0);
  auto iss_next_pc = p->get_state()->pc;
  auto iss_pc      = p->get_state()->prev_pc;
  auto iss_insn    = p->get_state()->insn;

  if (is_call(iss_insn.bits())) {
    uint64_t stack_val = iss_pc + inst_size(iss_insn.bits());
    fprintf (ras_log_fp, "%lld : CMT RAS PUSH : PC = %08lx (%02d,%02d), RAS[%zu]<=%08lx\n",
             rtl_commit_time,
             iss_pc,
             rtl_commit_cmt_id, rtl_commit_grp_id,
             iss_ras_head, stack_val);

    iss_ras_stack[iss_ras_head] = stack_val;
    iss_ras_head = (iss_ras_head + 1) % iss_ras_length;
  }
  if (is_ret(iss_insn.bits())) {
    fprintf (ras_log_fp, "%lld : CMT RAS POP  : PC = %08lx (%02d,%02d), RAS[%zu]=>%08lx, TARGET=%08lx : %s, RTL RAS[%lld]=>%08llx : %s\n",
             rtl_commit_time,
             iss_pc,
             rtl_commit_cmt_id, rtl_commit_grp_id,
             iss_ras_head-1, iss_ras_stack[iss_ras_head-1], iss_next_pc,
             iss_ras_stack[iss_ras_head-1] != iss_next_pc ? "MODEL_DIFF " : "MODEL_MATCH",
             rtl_commit_ras_index, rtl_commit_ras_addr,
             iss_ras_stack[iss_ras_head-1] != rtl_commit_ras_addr ? "RTL_MODEL_DIFF " : "RTL_MODEL_MATCH"
             );
    iss_ras_head = iss_ras_head >= 1 ? iss_ras_head - 1 : iss_ras_length - 1;
  }

  return;
}


void rtl_push_ras (long long rtl_time,
                   long long rtl_pc_vaddr,
                   long long rtl_ras_index,
                   long long rtl_ras_value)
{
  fprintf (ras_log_fp, "%lld : RTL RAS PUSH : PC = %08llx RAS[%lld]<=%08llx\n",
           rtl_time, rtl_pc_vaddr, rtl_ras_index, rtl_ras_value);
}

void rtl_pop_ras (long long rtl_time,
                  long long rtl_pc_vaddr,
                  long long rtl_ras_index,
                  long long rtl_ras_value)
{
  fprintf (ras_log_fp, "%lld : RTL RAS POP  : PC = %08llx RAS[%lld]=>%08llx\n",
           rtl_time, rtl_pc_vaddr, rtl_ras_index, rtl_ras_value);
}

void rtl_flush_ras (long long rtl_time,
                    int rtl_cmt_id, int rtl_grp_id,
                    long long rtl_pc_vaddr,
                    long long rtl_ras_index)
{
  fprintf (ras_log_fp, "%lld : RTL RAS FLUSH: PC = %08llx (%02d,%02d), RAS_INDEX<=%lld\n",
           rtl_time, rtl_pc_vaddr, rtl_cmt_id, rtl_grp_id, rtl_ras_index);
}

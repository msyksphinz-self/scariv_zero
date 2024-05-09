#include <map>
#include "config.h"
#include "cfg.h"
#include "disasm.h"
#include "kanata.h"

FILE *kanata_fp = NULL;
extern disassembler_t *disasm;
bool log_started = false;

bool kanata_enable = false;

void init_kanata ()
{
  if ((kanata_fp = fopen("kanata.log", "w")) == NULL) {
    perror("failed to open log file");
    exit(EXIT_FAILURE);
  }
  fprintf(kanata_fp, "Kanata 0004\n");

  cfg_t cfg;
  cfg.isa = DEFAULT_ISA;
  cfg.priv = DEFAULT_PRIV;
  isa_parser_t isa_parser(cfg.isa, cfg.priv);
  disasm = new disassembler_t (&isa_parser);
}

void start_kanata (long long cycle)
{
  if (!kanata_enable) return;

  fprintf (kanata_fp, "C=\t%lld\n", cycle);
}

void proceed_kanata_cycle(int cycle)
{
  if (!kanata_enable) return;

  if (log_started) {
    fprintf (kanata_fp, "C\t%d\n", cycle);
  }
}


std::map<long long, char *> stage_map;

void log_dispatch(long long time, long long id, long long pc, int inst)
{
  if (!kanata_enable) return;

  if (!log_started) {
    start_kanata (time);
    log_started = true;
  }
  fprintf (kanata_fp, "I\t%lld\t%lld\t0\n",
           id, id);
  fprintf (kanata_fp, "L\t%lld\t0\t%08llx:%s\n",
           id, pc, disasm->disassemble(inst).c_str());
}


void log_stage (long long id, const char *stage)
{
  if (!kanata_enable) return;

  decltype(stage_map)::iterator it = stage_map.find(id);
  if (it != stage_map.end()) {
    fprintf (kanata_fp, "E\t%lld\t0\t%s\n", id, it->second);
    stage_map.erase (id);
  }
  fprintf (kanata_fp, "S\t%lld\t0\t%s\n", id, stage);
  char *stage_str = (char *)malloc(sizeof(strlen(stage))+1);
  strcpy(stage_str, stage);
  stage_map.insert (std::make_pair(id, stage_str));
}


void retire_inst (long long id, long long retire_id, bool dead)
{
  if (!kanata_enable) return;
  decltype(stage_map)::iterator it = stage_map.find(id);
  if (it != stage_map.end()) {
    stage_map.erase (id);
    fprintf (kanata_fp, "E\t%lld\t0\t%s\n", id, it->second);
    free (it->second);
  }
  fprintf (kanata_fp, "R\t%lld\t%lld\t%d\n", id, retire_id, dead);
}

import os
import sys
import getopt
import functools
import time
import subprocess

def print_config (d_config):
  # necessary options to run (solver, formula, timeout)
  config_line = "-s {} ".format(d_config['solver'])
  config_line += "-i {} ".format(d_config['formula'])
  config_line += "-t {} ".format(d_config['timeout'])

  # additional solver options
  if 'restarts' in d_config:
    config_line += "-m {} ".format(d_config['restarts'])
  
  if 'flips' in d_config:
    config_line += "-c {} ".format(d_config['flips'])

  if 'card_compute' in d_config:
    config_line += "-o {} ".format(d_config['card_compute'])

  if 'seed' in d_config:
    config_line += "-r {} ".format(d_config['seed'])

  if 'stochastic_selection' in d_config and d_config['stochastic_selection'] > 1:
    config_line += "-S {} ".format(d_config['stochastic_selection'])

  if 'hard_eps' in d_config and d_config['hard_eps'] > 0:
    config_line += "-H {} ".format(d_config['hard_eps'])

  if 'soft_eps' in d_config and d_config['soft_eps'] > 0:
    config_line += "-E {} ".format(d_config['soft_eps'])

  if 'neighbors_plus' in d_config and d_config['neighbors_plus']:
    config_line += "-n "

  if 'ignore_weight' in d_config and d_config['ignore_weight']:
    config_line += "-I "
  
  if 'soft_transfer' in d_config and d_config['soft_transfer']:
    config_line += "-T "

  if 'soft_takes_hard' in d_config and d_config['soft_takes_hard']:
    config_line += "-P "

  if 'exp_wt' in d_config and d_config['exp_wt'] is not None:
    config_line += "-e {} ".format(d_config['exp_wt'])

  if 'all_transfer' in d_config and d_config['all_transfer'] is not None:
    config_line += "-a {} ".format(d_config['all_transfer'])

  if 'init_card_wt' in d_config and d_config['init_card_wt'] is not None:
    config_line += "-C {} ".format(d_config['init_card_wt'])

  if 'transfer_slow' in d_config and d_config['transfer_slow']:
    config_line += "-F "

  if 'hard_takes_soft' in d_config and d_config['hard_takes_soft']:
    config_line += "-p "

  if 'rand_uvar' in d_config and d_config['rand_uvar'] is not None:
    config_line += "-R {} ".format (d_config['rand_uvar'])

  if 'sel_exp' in d_config and d_config['sel_exp'] is not None:
    config_line += "-l {} ".format (d_config['sel_exp'])

  if 'card_wt_rule' in d_config and d_config['card_wt_rule'] is not None:
    config_line += "-q {} ".format (d_config['card_wt_rule'])

  if 'inner_bound' in d_config and d_config['inner_bound'] is not None:
    config_line += "-b {} ".format (d_config['inner_bound'])

  if 'hit_bound' in d_config and d_config['hit_bound'] is not None:
    config_line += "-z {} ".format (d_config['hit_bound'])

  if 'inner_mult' in d_config and d_config['inner_mult'] is not None:
    config_line += "-h {} ".format (d_config['inner_mult'])

  if 'flip_step' in d_config and d_config['flip_step'] is not None:
    config_line += "-Q {} ".format (d_config['flip_step'])

  if 'outer_bound' in d_config and d_config['outer_bound'] is not None:
    config_line += "-B {} ".format (d_config['outer_bound'])

  if 'hard_stochastic_selection' in d_config and d_config['hard_stochastic_selection'] > 1:
    config_line += "-Z {} ".format(d_config['hard_stochastic_selection'])

  if 'init_cls_wt' in d_config and d_config['init_cls_wt'] is not None:
    config_line += "-g {} ".format(d_config['init_cls_wt'])

  if 'init_cls_relative' in d_config and d_config['init_cls_relative'] is not None:
    config_line += "-Y "

  if 'cls_no_maxs_multiply' in d_config and d_config['cls_no_maxs_multiply'] is not None:
    config_line += "-y "

  if 'select_random_sat' in d_config and d_config['select_random_sat'] is not None:
    config_line += "-U {} ".format(d_config['select_random_sat'])
  

  print(config_line)


def get_card_ddfw_config (seed,formula,timeout,flips,restarts,card_compute, stochastic_selection, hard_eps, soft_eps, neighbors_plus, ignore_weight, soft_transfer, soft_takes_hard, exp_wt, all_transfer, init_card_wt, transfer_slow, hard_takes_soft, rand_uvar, sel_exp, card_wt_rule, inner_bound, hit_bound, inner_mult, flip_step, hard_stochastic_selection, outer_bound,init_cls_wt,init_cls_relative,cls_no_maxs_multiply, select_random_sat):
  d = {'solver':'card_ddfw', 'seed':seed, 'formula':formula, 'timeout':timeout, 'flips':flips, 'restarts':restarts, 'card_compute':card_compute, 'stochastic_selection':stochastic_selection, 'hard_eps':hard_eps, 'soft_eps':soft_eps, 'neighbors_plus':neighbors_plus, 'ignore_weight':ignore_weight, 'soft_transfer':soft_transfer,'soft_takes_hard':soft_takes_hard,'exp_wt':exp_wt, 'all_transfer':all_transfer, 'init_card_wt':init_card_wt, 'transfer_slow':transfer_slow,'hard_takes_soft':hard_takes_soft,'rand_uvar':rand_uvar, 'sel_exp':sel_exp, 'card_wt_rule':card_wt_rule, 'inner_bound':inner_bound, 'hit_bound':hit_bound, 'inner_mult':inner_mult, 'flip_step':flip_step, 'hard_stochastic_selection':hard_stochastic_selection, 'outer_bound':outer_bound, 'init_cls_wt':init_cls_wt, 'init_cls_relative':init_cls_relative, 'cls_no_maxs_multiply':cls_no_maxs_multiply,'select_random_sat':select_random_sat}
  return d

def get_card_cadical_config (formula, timeout):
  d = {'solver':'card_cadical', 'formula':formula, 'timeout':timeout}
  return d

def get_cadical_config (formula, timeout):
  d = {'solver':'cadical', 'formula':formula, 'timeout':timeout}
  return d

def get_ddfw_config (seed,formula,timeout,flips,restarts):
  d = {'solver':'ddfw', 'seed':seed, 'formula':formula, 'timeout':timeout, 'flips':flips, 'restarts':restarts}
  return d

def get_yal_config (seed,formula,timeout,flips,restarts):
  d = {'solver':'yalsat', 'seed':seed, 'formula':formula, 'timeout':timeout, 'flips':flips, 'restarts':restarts}
  return d

def get_carl_config (seed,formula,timeout,flips,restarts):
  d = {'solver':'carlsat', 'seed':seed, 'formula':formula, 'timeout':timeout}
  return d

def get_puremse_config (seed,formula,timeout,flips,restarts):
  d = {'solver':'purems_mse', 'seed':seed, 'formula':formula, 'timeout':timeout}
  return d

def get_lsecnf_config (seed,formula,timeout,flips,restarts):
  d = {'solver':'ls-ecnf', 'seed':seed, 'formula':formula, 'timeout':timeout}
  return d


def run(name, args):

  input_file = None
  seed_cnt = 200
  timeout = 2700
  flips = 1000000000
  restarts = 1000

  opts, args = getopt.getopt(args, "i:")

  for (opt,value) in opts:
    if (opt == '-i'):
      input_file = value

  wknf_forms = ["../../benchmarks/wknf/mm-SR03.wknf","../../benchmarks/wknf/mm-SR05.wknf","../../benchmarks/wknf/mm-SW02.wknf","../../benchmarks/wknf/mm-SW05.wknf"]
  # # card_ddfw
  for formula in wknf_forms:
    for seed in range(seed_cnt):
      d = get_card_ddfw_config(seed,formula,timeout,flips,1,1,1,0,0,1,0,0,0,None,None,35,None,1,None,None, None, 1000, 1, 25, None, 7, None, None,1,1,12)
      print_config (d)


  # # card_cadical
  # for formula in knf_forms:
  #   d = get_card_cadical_config (formula, timeout)
  #   print_config (d)

  # cnf_forms = ["../benchmarks/cnf/maxsquare-9-51-SAT.cnf"]
  # # cadical
  # for formula in cnf_forms:
  #   d = get_cadical_config (formula, timeout)
  #   print_config (d)
  
  # # ddfw
  # for formula in cnf_forms:
  #   for seed in range(seed_cnt):
  #     d = get_ddfw_config(seed,formula,timeout,flips,1)
  #     print_config (d)

  # # yalsat
  # for formula in cnf_forms:
  #   for seed in range(seed_cnt):
  #     d = get_yal_config(seed,formula,timeout,flips,1)
  #     print_config (d)

  # wcard_forms = ["../../benchmarks/wcard/mm-SR03.wcard","../../benchmarks/wcard/mm-SR05.wcard","../../benchmarks/wcard/mm-SW02.wcard","../../benchmarks/wcard/mm-SW05.wcard"]
  # # carlsat
  # for formula in wcard_forms:
  #   for seed in range(seed_cnt):
  #     d = get_carl_config(seed,formula,timeout,flips,1)
  #     print_config (d)

  # wcnf_forms = ["../../benchmarks/wcnf/mm-SR03.wcnf","../../benchmarks/wcnf/mm-SR05.wcnf","../../benchmarks/wcnf/mm-SW02.wcnf","../../benchmarks/wcnf/mm-SW05.wcnf"]
  # # pure_mse
  # for formula in wcnf_forms:
  #   for seed in range(seed_cnt):
  #     d = get_puremse_config(seed,formula,timeout,flips,1)
  #     print_config (d)

  # wcai_forms = ["../../benchmarks/wcai/mm-SR03.ecnf","../../benchmarks/wcai/mm-SR05.ecnf","../../benchmarks/wcai/mm-SW02.ecnf","../../benchmarks/wcai/mm-SW05.ecnf"]
  # # pure_mse
  # for formula in wcai_forms:
  #   for seed in range(3):
  #     d = get_lsecnf_config(seed,formula,timeout,flips,1)
  #     print_config (d)

  

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
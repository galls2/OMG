import itertools
import os
import re

from z3 import Bool, Not, And, simplify, Or, Exists, substitute, BoolVal

from cnf_parser import CnfParser
from formula_wrapper import FormulaWrapper
from state import State
from z3_utils import Z3Utils

OMG_EXE_PATH = '~/Desktop/extavy/cmake-build-debug/avy/src/omg'
AIG_SPLIT_EXE_PATH = '/home/galls2/Downloads/aiger-1.9.9/aigsplit'
AIG_TO_AAG_EXE_PATH = '/home/galls2/Downloads/aiger-1.9.9/aigtoaig'

AIG_EXAMPLE_PATH = 'AigFiles/'
IIMC_EXAMPLE_PATH = 'iimc_aigs/'
AIG_EXAMPLE_NAME = 'yakir4n.aig'
OUTPUT_PATH = 'iimc_dimacs/'

DIMACS_PREFIX = 'p'
HEADER_PREFIX = 'MAXVAR'


def parse_aig_latch_line(latch_line):
    parts = latch_line.split()
    return [0] if len(parts) == 1 else ([int(parts[-1])] if parts[-1] in ['0', '1'] else [0, 1])


def _parse_aag_latch_line(latch_line):
    parts = latch_line.split()
    return [0] if len(parts) == 2 else ([int(parts[-1])] if parts[-1] in ['0', '1'] else [0, 1])


def _latch_lines_to_init_values(latch_lines, line_value_extractor):
    latch_options = [line_value_extractor(l_line) for l_line in latch_lines]
    return itertools.product(*latch_options)


class AigParser(object):
    def get_tr_and_initial(self, qe_policy, kripke):
        raise NotImplementedError()

    def get_ap_mapping(self):
        raise NotImplementedError()

    def get_num_latches(self):
        raise NotImplementedError()


def main_connective(f, txt):
    return f.decl().name() == txt


def get_initial_states(i_latches, output_formulas, kripke, tr):
    def get_outputs_for_latch_values(l_vals):
        return itertools.product(*[out_val_list \
                                   for out_formula in output_formulas
                                   for out_val_list in Z3Utils.all_sat(out_formula.assign_int_vec(l_vals))])

    initial_states = (State.from_int_list(list(i_latch) + list(comb), tr.get_var_vectors()[0], kripke)
                      for i_latch in i_latches
                      for comb in get_outputs_for_latch_values(i_latch))
    return initial_states


class PythonAigParser(AigParser):
    def __init__(self, aig_path):
        super(PythonAigParser, self).__init__()

        self._aig_path = aig_path

        self._get_MILOA()
        self._init_latch_values = None

    def _get_MILOA(self):
        f = open(self._aig_path, 'r')
        self._M, self._I, self._L, self._O, self._A = [int(val) for val in f.readline().split()[1:6]]
        f.close()

    def _to_aag(self):
        out_path = self._aig_path.split('.')[0] + '.aag'
        cmd = '{aigtoaig} -a {inpath} > {outpath}'.format(aigtoaig=AIG_TO_AAG_EXE_PATH, inpath=self._aig_path,
                                                          outpath=out_path)
        #   print cmd
        os.system(cmd)
        return out_path

    def _dfs(self, lit_hash, to_calc, lines, first_and_lit):
        if to_calc in lit_hash.keys():
            return lit_hash[to_calc]

        if to_calc % 2 == 1:
            self._dfs(lit_hash, to_calc - 1, lines, first_and_lit)
            if main_connective(lit_hash[to_calc - 1], 'and'):
                and_line = lines[(to_calc - first_and_lit)/2].split()
                l, r = int(and_line[1]), int(and_line[2])
                if main_connective(lit_hash[l], 'not') and main_connective(lit_hash[r], 'not'):
                    lit_hash[to_calc] = Or(lit_hash[l - 1], lit_hash[r - 1])
                    return
            lit_hash[to_calc] = Not(lit_hash[to_calc - 1])
            return

        and_line = lines[(to_calc - first_and_lit)/2].split()
        l, r = int(and_line[1]), int(and_line[2])
        self._dfs(lit_hash, l, lines, first_and_lit)
        self._dfs(lit_hash, r, lines, first_and_lit)
        lit_hash[to_calc] = And(lit_hash[l], lit_hash[r])
        return

    def _get_initial_latch_values(self, aag_lines):
        return _latch_lines_to_init_values(aag_lines[1 + self._I: 1 + self._I + self._L], _parse_aag_latch_line)

    def get_num_latches(self):
        return self._L

    def get_tr_and_initial(self, qe_policy, kripke):
        aag_path = self._to_aag()

        f = open(aag_path, 'r')
        aag_lines = f.readlines()
        self._M, self._I, self._L, self._O, self._A = [int(val) for val in aag_lines[0].split()[1:6]]
        f.close()

        self._prefetch_ap_mapping(aag_lines)
        self._init_latch_values = _latch_lines_to_init_values(aag_lines[1 + self._I: 1 + self._I + self._L],
                                                              _parse_aag_latch_line)

        in_lits = [int(l.split()[0]) for l in aag_lines[1: self._I + 1]]
        next_state_lits = [int(l.split()[1]) for l in aag_lines[self._I + 1: self._I + self._L + 1]]
        prev_state_lits = [int(l.split()[0]) for l in aag_lines[self._I + 1: self._I + self._L + 1]]
        out_lits = [int(l.split()[0]) for l in aag_lines[self._I + self._L + 1: self._I + self._L + self._O + 1]]

        formulas = {lit: Bool(str(lit)) for lit in in_lits + prev_state_lits}
        formulas[0] = BoolVal(False)
        formulas[1] = BoolVal(True)
        first_and_line_idx = next(i for i in range(len(aag_lines)) if len(aag_lines[i].split()) == 3)
        aag_from_and = aag_lines[first_and_line_idx:]
        first_and_lit = int(aag_lines[first_and_line_idx].split()[0])
        for lit_to_calc in next_state_lits + out_lits:
            self._dfs(formulas, lit_to_calc, aag_from_and, first_and_lit)

        max_var = 2*self._M + 3
        in_vars = [Bool(str(max_var + _i)) for _i in range(self._I)]
        max_var += self._I
        prev_state_vars = [Bool(str(max_var + _pl)) for _pl in range(self._L)]
        max_var += self._L
        next_state_vars = [Bool(str(max_var + _nl)) for _nl in range(self._L)]
        max_var += self._L
        prev_output_vars = [Bool(str(max_var + i)) for i in range(self._O)]
        max_var += self._O
        next_output_vars = [Bool(str(max_var + i)) for i in range(self._O)]
        max_var += self._O

        ltr_z3_no_sub = simplify(And(*[next_state_vars[_l] == formulas[next_state_lits[_l]] for _l in range(self._L)])) #in_lits,prev_state_lits->nextstate_vars
        outputs_z3_no_sub = [simplify(next_output_vars[_o] == formulas[out_lits[_o]]) for _o in range(self._O)]  #in_lits,prev_state_lits->nextoutput_vars

        in_p_vars = [Bool(str(_i)) for _i in in_lits]
        state_p_vars = [Bool(str(_l)) for _l in prev_state_lits]
        ltr_z3 = substitute(ltr_z3_no_sub, zip(in_p_vars + state_p_vars, in_vars + prev_state_vars))
        outputs_z3 = [substitute(outputs_z3_no_sub[_o], zip(in_p_vars + state_p_vars, in_vars + next_state_vars)) for _o in range(self._O)]

        output_formulas = [FormulaWrapper(outputs_z3[_o], [next_state_vars, [next_output_vars[_o]]]) for _o in range(self._O)]

        prev_var_vector = prev_state_vars + prev_output_vars
        next_var_vector = next_state_vars + next_output_vars
        var_vectors = [prev_var_vector, next_var_vector]

        if in_vars:
            quantified_input = Z3Utils.apply_qe(And(*[Exists(in_vars, f) for f in [ltr_z3] + outputs_z3]), qe_policy)
        else:
            quantified_input = And(*[f for f in [ltr_z3] + outputs_z3])

        tr = FormulaWrapper(quantified_input, var_vectors)

        initial_states = get_initial_states(self._init_latch_values, output_formulas, kripke, tr)

        return tr, initial_states

    def get_ap_mapping(self):
        return self._ap_mapping

    def _prefetch_ap_mapping(self, aag_lines):
        ap_line_regex = re.compile(".*[ilo][0-9]* .*")
        aps_lines = [line for line in aag_lines if re.match(ap_line_regex, line.replace('\n', ''))]

        ap_part_regex = re.compile("[ilo][0-9]* .*")
        aps = [re.findall(ap_part_regex, ap_line)[0] for ap_line in aps_lines]
        self._ap_mapping = {' '.join(line.split(' ')[1:]): line.split()[0] for line in aps}


def split_aig(aig_path):
    if not os.path.isfile(AIG_SPLIT_EXE_PATH):
        raise IOError('No aigsplit file where you promised! Do you try to mess me up??')

    cmd = AIG_SPLIT_EXE_PATH + ' ' + aig_path
    os.system(cmd)


def delete_aux_files(aig_path):
    pattern_to_remove = '.'.join(aig_path.split('.')[:-1]) + 'o*'
    os.system('rm ' + pattern_to_remove)


def _get_cnf(aig_path, cmd_arg):
    output_file_name = aig_path.split('/')[-1][:-4]
    out_path = "{}{}_{}.dimacs".format(OUTPUT_PATH, output_file_name, cmd_arg)
    cmd = "{} {} {} > {}".format(OMG_EXE_PATH, aig_path, cmd_arg, out_path)
    #    print cmd
    os.system(cmd)
    with open(out_path, 'r') as input_dimacs:
        txt = [line.replace('\n', '') for line in input_dimacs.readlines()]
    first_dimacs_line = next(line for line in txt if line.startswith(DIMACS_PREFIX))
    first_header_line = next(line for line in txt if line.startswith(HEADER_PREFIX))
    dimacs_content = txt[txt.index(first_dimacs_line):]
    metadata = txt[txt.index(first_header_line):txt.index(first_dimacs_line)]
    return metadata, dimacs_content


class AvyAigParser(AigParser):
    def __init__(self, aig_path):
        super(AvyAigParser, self).__init__()
        self._aig_path = aig_path
        self._init_from_path()

    def _init_from_path(self):
        self._aig_lines = []
        with open(self._aig_path, 'r') as aig_file:
            self._aig_lines = aig_file.readlines()
            self._M, self._I, self._L, self._O, self._A = [int(val) for val in self._aig_lines[0].split()[1:6]]

    def _parse(self):
        split_aig(self._aig_path)

        def get_file_num_name(idx, O):
            return str(idx).zfill(len(str(O)))

        bad_file_names = ['.'.join(self._aig_path.split('.')[:-1]) + 'o' + get_file_num_name(i, self._O) + '.aig'
                          for i in range(self._O)]
        ltr_aig_path = bad_file_names[0]

        ltr_metadata, ltr_dimacs = _get_cnf(ltr_aig_path, 'Tr')
        bads = [_get_cnf(aig, 'Bad') for aig in bad_file_names]
        delete_aux_files(self._aig_path)
        return [(ltr_metadata, ltr_dimacs)] + bads

    def _get_initial_latch_values(self):
        return _latch_lines_to_init_values(self._aig_lines[1: 1 + self._L], parse_aig_latch_line)

    def _get_aig_after_reset(self):
        return self._aig_lines[0:1] + \
               [line.split()[0] + '\n' for line in self._aig_lines[1:self._L + 1]] + \
               self._aig_lines[self._L + 1:]

    def _reset_logic(self):
        new_aig_lines = self._get_aig_after_reset()
        old_path_parts = self._aig_path.split('.')
        new_aig_path = '.'.join(old_path_parts[:-1]) + '_reset.' + old_path_parts[-1]
        with open(new_aig_path, 'w') as new_aig:
            new_aig.write(''.join(new_aig_lines))

        self._aig_path = new_aig_path
        self._init_from_path()

    def get_tr_and_initial(self, qe_policy, kripke):
        self._reset_logic()
        parse_results = self._parse()

        cnf_parser = CnfParser(self._L, qe_policy)
        ltr_metadata, ltr_dimacs = parse_results[0]

        ltr_formula = cnf_parser.dimacs_to_z3(ltr_metadata, ltr_dimacs, cnf_parser.parse_metadata_tr)
        output_formulas = \
            [cnf_parser.dimacs_to_z3(output_metadata, output_dimacs, cnf_parser.parse_metadata_bad)
             for (output_metadata, output_dimacs) in parse_results[1:]]

        max_var_ltr = int(ltr_dimacs[0].split()[-1])
        tr = Z3Utils.combine_ltr_with_bad_formulas(ltr_formula, output_formulas, max_var_ltr + 1)

        initial_states = get_initial_states(self._get_initial_latch_values(), output_formulas, kripke, tr)

        return tr, initial_states

    def get_ap_mapping(self):
        ap_line_regex = re.compile(".*[ilo][0-9]* .*")
        aps_lines = [line for line in self._aig_lines if re.match(ap_line_regex, line.replace('\n', ''))]

        ap_part_regex = re.compile("[ilo][0-9]* .*")
        aps = [re.findall(ap_part_regex, ap_line)[0] for ap_line in aps_lines]
        return {' '.join(line.split(' ')[1:]): line.split()[0] for line in aps}

    def get_num_latches(self):
        return self._L

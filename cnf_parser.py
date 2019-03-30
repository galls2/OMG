from z3 import *

from formula_wrapper import FormulaWrapper
from omg import _big_cup
from z3_utils import get_vars, Z3Utils

DEBUG = True


def _raw_lit_to_lit(raw_lit):
    atom = Bool(raw_lit.replace('-', ''))
    return atom if not raw_lit.startswith('-') else Not(atom)


def _line_to_clause(line):
    parts = [raw_lit for raw_lit in line.split() if raw_lit not in ['', '\n', '\t']]
    if parts[-1] == '0':
        parts = parts[:-1]
    clause_parts = [_raw_lit_to_lit(raw_lit) for raw_lit in parts]
    clause = Or(*clause_parts)
    return clause


class CnfParser( object):
    def __init__(self, num_regs, qe_policy):
        super(CnfParser, self).__init__()
        self._num_regs = num_regs
        self._qe_policy = qe_policy
    '''
      dimacs is a list of lines, each line is a clause
    '''

    def parse_metadata_tr(self, tr_metadata):
        PREFIXES = ['CURRENT', 'NEXT']
        parsed_parts = [[p for p in meta_line.split() if p != ''] for meta_line in tr_metadata]
        parsed_with_vectors = [line for line in parsed_parts if
                               any([line[0].startswith(prefix) for prefix in PREFIXES])]
        var_vectors = [[z3.Bool(raw_var) for raw_var in parsed_part[1:]] for parsed_part in parsed_with_vectors]
        if DEBUG:
            assert len(var_vectors) and all([len(vec) == self._num_regs for vec in var_vectors])
        return var_vectors

    def parse_metadata_bad(self, bad_metadata):
        PREFIXES = ['IN', 'OUT']
        parsed_parts = [[p for p in meta_line.split(' ') if p != ''] for meta_line in bad_metadata]
        parsed_with_vectors = [line for line in parsed_parts if
                               any([line[0].startswith(prefix) for prefix in PREFIXES])]

        var_vectors = [[Bool(raw_var) for raw_var in parsed_part[max(1, len(parsed_part) - self._num_regs):]]
                       for parsed_part in parsed_with_vectors]
        return var_vectors

    def dimacs_to_z3(self, metadata, extended_dimacs, metadata_parser):
        dimacs_lines = filter(lambda raw_line: len(raw_line) > 0 and raw_line[0] not in [' ', 'p', '\t'],
                              extended_dimacs)
        clauses = [_line_to_clause(line) for line in dimacs_lines]
        all_vars_list = [set(get_vars(clause)) for clause in clauses]
        all_vars = _big_cup(all_vars_list)
        final_z3_formula = And(*clauses)
        var_vectors = metadata_parser(metadata)
        aux = set(all_vars).difference(set([var for vec in var_vectors for var in vec]))

        quantifier_over_aux = Exists(list(aux), final_z3_formula)
    #    print 'beforelalalaa'
    #    s = simplify(quantifier_over_aux)
    #    print s
    #    print quantifier_over_aux
    #    after_qe = Z3Utils.apply_qe(quantifier_over_aux)  ## try for
        after_qe = Z3Utils.apply_qe(quantifier_over_aux, self._qe_policy)
    #    print 'lalalala'
        return FormulaWrapper(after_qe, var_vectors)

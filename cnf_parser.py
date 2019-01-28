from z3 import *

from formula_wrapper import FormulaWrapper
from z3_utils import get_vars, Z3Utils

DEBUG = True


class CnfParser(object):
    def __init__(self):
        super(CnfParser, self).__init__()

    @classmethod
    def raw_lit_to_lit(cls, raw_lit):
        atom = Bool(raw_lit.replace('-', ''))
        return atom if not raw_lit.startswith('-') else Not(atom)

    @classmethod
    def line_to_clause(cls, line):
        parts = filter(lambda raw_lit: raw_lit not in ['', '\n', '\t'], line.split(' '))
        if parts[-1] == '0':
            parts = parts[:-1]
        clause_parts = map(lambda raw_lit: CnfParser.raw_lit_to_lit(raw_lit), parts)
        clause = Or(*clause_parts)
        return clause

    '''
      dimacs is a list of lines, each line is a clause
    '''

    @classmethod
    def parse_metadata_tr(cls, tr_metadata, num_regs):
        parsed_parts = map(lambda meta_line: filter(lambda p: p != '', meta_line.split(' ')), tr_metadata)
        parsed_with_vectors = filter(
            lambda meta_line: (meta_line[0].startswith('CURRENT') or meta_line[0].startswith('NEXT')),
            parsed_parts)
        var_vectors = [[Bool(raw_var) for raw_var in parsed_part[1:]] for parsed_part in parsed_with_vectors]
        if DEBUG:
            assert len(var_vectors) and all([len(vec) == num_regs for vec in var_vectors])
        return var_vectors

    @classmethod
    def parse_metadata_bad(cls, bad_metadata, num_regs):
        parsed_parts = map(lambda meta_line: filter(lambda p: p != '', meta_line.split(' ')), bad_metadata)
        parsed_with_vectors = filter(
            lambda meta_line: (meta_line[0].startswith('IN') or meta_line[0].startswith('OUT')),
            parsed_parts)
        var_vectors = [[Bool(raw_var) for raw_var in parsed_part[max(1, len(parsed_part) - num_regs):]]
                       for parsed_part in parsed_with_vectors]
        return var_vectors

    @classmethod
    def z3_formula_from_dimacs(cls, metadata, extended_dimacs, metadata_parser, num_regs):
        dimacs_lines = filter(lambda raw_line: len(raw_line) > 0 and raw_line[0] not in [' ', 'p', '\t'],
                              extended_dimacs)
        clauses = [CnfParser.line_to_clause(line) for line in dimacs_lines]
        final_z3_formula = And(*clauses)
        var_vectors = metadata_parser(metadata, num_regs)
        aux = set(get_vars(final_z3_formula)).difference(set([var for vec in var_vectors for var in vec]))

        quantifier_over_aux = Exists(list(aux), final_z3_formula)
        after_qe = Z3Utils.apply_qe(quantifier_over_aux)
        return FormulaWrapper(after_qe, var_vectors)

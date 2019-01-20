def clean_raw_line(txt):
    return txt[:-2]


class CnfParser(object):
    def __init__(self):
        super(CnfParser, self).__init__()

    @classmethod
    def raw_lit_to_lit(cls, raw_lit):
        atom = Bool(raw_lit)
        return atom if not raw_lit.startswith('-') else Not(atom)

    @classmethod
    def line_to_clause(cls, line):
        parts = line.split(' ')
        if parts[-1] == '0':
            parts = parts[:-1]
        clause_parts = map(lambda raw_lit: CnfParser.raw_lit_to_lit(raw_lit), parts)
        clause = Or(*clause_parts)
        return clause

    '''
      dimacs is a list of lines, each line is a clause
    '''
    @classmethod
    def parse_metadata(cls, metadata):
        parts = metadata.split('\n')
        parsed_parts = map(lambda part: part.split(' '), parts)
        var_vectors = [Bool(raw_var) for parsed_part in parsed_parts for raw_var in parsed_part[1:]]
        return var_vectors

    @classmethod
    def z3_formula_from_dimacs(cls, metadata, extended_dimacs):
        raw_lines = map(lambda raw_line: clean_raw_line(raw_line), extended_dimacs)
        dimacs_lines = filter(lambda raw_line: len(raw_line) > 0 and raw_line[0] not in [' ', 'p', '\t'], raw_lines)
        clauses = [CnfParser.line_to_clause(line) for line in dimacs_lines]
        final_z3_formula = And(*clauses)
        var_vectors = CnfParser.parse_metadata(metadata)
        return FormulaWrapper(final_z3_formula, var_vectors)

def get_cnfs():
    formula_types = ['Tr']
    file_names = ['DimacsFiles/yakir4n_' + f_type + '.dimacs' for f_type in formula_types]

    cnfs = []
    for file_name in file_names:
        f = open(file_name, 'r')
        cnf = CnfParser.z3_formula_from_dimacs(f.readlines())
        cnfs.append(cnf)
    return cnfs


def test_print_and_swap():
    for cnf in get_cnfs():
        t = Then('simplify', 'propagate-values', 'ctx-simplify')
        print t(cnf)


if __name__ == '__main__':
    test_print_and_swap()

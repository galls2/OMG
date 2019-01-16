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
    def from_dimacs(cls, dimacs):
        raw_lines = map(lambda raw_line: clean_raw_line(raw_line), dimacs)
        dimacs_lines = filter(lambda raw_line: len(raw_line) > 0 and raw_line[0] not in [' ', 'p', '\t'], raw_lines)
        clauses = [CnfParser.line_to_clause(line) for line in dimacs_lines]
        return And(*clauses)


def get_cnfs():
    formula_types = ['Tr']
    file_names = ['DimacsFiles/yakir4n_' + f_type + '.dimacs' for f_type in formula_types]

    cnfs = []
    for file_name in file_names:
        f = open(file_name, 'r')
        cnf = CnfParser.from_dimacs(f.readlines())
        cnfs.append(cnf)
    return cnfs


def test_print_and_swap():
    for cnf in get_cnfs():
        print cnf


if __name__ == '__main__':
    test_print_and_swap()

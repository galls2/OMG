def par(txt):
    return '(' + txt + ')'


class PropFormula(object):
    def __init__(self, main_connective, operands, atom):
        super(PropFormula, self).__init__()
        self._main_connective = main_connective
        self._operands = operands
        self._atom = atom

    @classmethod
    def from_dimacs(cls, file_path):
        with open(file_path, 'r') as f:
            dimacs_lines = filter(lambda line: len(line) > 0 and line[0] not in [' ', 'p', '\t'], f.readlines())

    def to_smtlib(self):
        if self._atom is not None:
            return par(self._atom)
        return par(self._main_connective + ' ' + ' '.join([op.to_smtlib() for op in self._operands]))

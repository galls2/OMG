import sys

from ctl import CtlParser
from kripke_structure import AigKripkeStructure
from omg import OmgModelChecker


def parse_input():
    aig_file_path = sys.argv[1]
    ctl_formula_path = sys.argv[2]
    return aig_file_path, ctl_formula_path

def parse_ctl_formula(ctl_formula_path):
    ctl_parser = CtlParser()   ##FIXME
    with open(ctl_formula_path, 'r') as ctl_file:
        lines = ctl_formula_path.readlines()
        specification_lines = filter(lambda line: line != '' and not line.startswith('#'), lines)
        return [ctl_parser.parse_omg(specification_line) for specification_line in specification_lines]

if __name__ == '__main__':
    aig_path, ctl_path = parse_input()
    ctl_formulas = parse_ctl_formula(ctl_path)
    aps = list([functools.reduce(lambda x, y: x | y, set(ctl_formula.get_atomic_propositions())  for ctl_formula in ctl_formulas]))
    kripke_structure = AigKripkeStructure(aig_path, ctl_formula.get_atomic_propositions())
    omg = OmgModelChecker(kripke_structure, True)
    omg.check_all_initial_states(ctl_formula)

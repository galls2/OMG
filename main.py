import sys

from aig_parser import AvyAigParser
from omg import OmgModelChecker


def parse_input():
    aig_file_path = sys.argv[1]
    return aig_file_path


def aig_to_dimcas(aig_full_path):
    aig_parser = AvyAigParser()
    parts = aig_full_path.split('/')
    aig_dir_path = '/'.join(parts[:-1])
    aig_file_name = parts[-1]
    return aig_parser.parse(aig_dir_path, aig_file_name)


def get_kripke_structure(aig_full_path):
    dimacs = aig_to_dimcas(aig_full_path)


if __name__ == '__main__':
    aig_path = parse_input()
    kripkeStructure = get_kripke_structure(aig_path)

    omg = OmgModelChecker(kripkeStructure, True)

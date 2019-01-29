import functools
import os
import sys

from aig_parser import AvyAigParser
from ctl import CtlParser, is_balanced_brackets, CtlFormula
from kripke_structure import AigKripkeStructure
from omg import OmgModelChecker

BUG_LINE = '<------------------------------------------------------ BUG -------------------------------------'


def parse_input():
    aig_file_path = sys.argv[1]
    ctl_formula_path = sys.argv[2]
    return aig_file_path, ctl_formula_path


def legal_line_ending(line):
    last_letter_index = len(line) - 1
    while line[last_letter_index] in [' ', '\n', '\t']:
        last_letter_index -= 1
    for op in CtlFormula.allowed_operators:
        if op in CtlFormula.binary_temporal_operators:
            if line[last_letter_index] == op[-1] or line[last_letter_index] == op[-2]:
                return False
        else:
            start_index = last_letter_index - len(op)
            if start_index < 0:
                continue
            if line[start_index:last_letter_index + 1] == op:
                return False
    return True


def fix_equiv(txt):
    return txt.replace('==', ' == ')


def parse_ctl_chunk(chunk):
    chunk = filter(lambda line: line not in ['\n', '', ' '], chunk)
    try:
        first_line_not_header = next(i for i in range(len(chunk)) if not chunk[i].startswith('#'))
        header_part = chunk[:first_line_not_header]
        formula_part = chunk[first_line_not_header:]

        header_result = True if 'PASS' in ' '.join(header_part) else False

        ctl_parser = CtlParser()
        raw_formulas = formula_part
        raw_formulas = filter(
            lambda raw_formula: raw_formula.replace('\n', '').replace(' ', '').replace('\t', '') != '',
            raw_formulas)
        f_indexes = [0] + [i + 1 for i in range(len(raw_formulas)) if
                           is_balanced_brackets(' '.join(raw_formulas[:(i + 1)])) and legal_line_ending(
                               raw_formulas[i])]

        ctl_formulas_borders = [(f_indexes[i], f_indexes[i + 1] if i != len(f_indexes) - 1 else len(raw_formulas))
                                for i in range(len(f_indexes))]
        raw_ctl_formulas = [raw_formulas[start: end] for (start, end) in ctl_formulas_borders if start != end]

        single_line_raw_formulas = map(lambda multiline: fix_equiv(' '.join(multiline)), raw_ctl_formulas)
        '''
        print 'CHUNK'
        for r in single_line_raw_formulas:
            print r
            print '----'
        '''

        ctl_formulas = map(lambda raw_formula: ctl_parser.parse_omg(raw_formula), single_line_raw_formulas)

        return [header_result] + ctl_formulas
    except StopIteration:
        return [None]


def parse_ctl_file(ctl_path):
    with open(ctl_path, 'r') as ctl_file:
        lines = ctl_file.readlines()
        lines = filter(lambda line: line not in ['', '\n'], lines)
        start_indexes = ([0] if lines[0].startswith('#') else []) + \
                        [i for i in range(len(lines)) if
                         i > 0 and
                         lines[i].startswith('#') and
                         not lines[i - 1].startswith('#')]

        chunk_borders = [(start_indexes[i], start_indexes[i + 1] if i != len(start_indexes) - 1 else len(lines))
                         for i in range(len(start_indexes))]
        chunks = [lines[start: end] for (start, end) in chunk_borders]
        '''
        for c in chunks:
            print c
        '''
        return [parse_ctl_chunk(chunk) for chunk in chunks]


def model_checking(aig_path, ctl_path):
    ctl_chunks = parse_ctl_file(ctl_path)
    # print ctl_chunks
    ctl_formulas = ctl_chunks[0][1:]
    aps = functools.reduce(lambda x, y: x | y,
                           [set(ctl_formula.get_aps()) for chunk in ctl_chunks for ctl_formula in
                            chunk[1:]])
    kripke_structure = AigKripkeStructure(aig_path, aps)
    omg = OmgModelChecker(kripke_structure)

    for chunk in ctl_chunks:

        expected_res = chunk[0]
        if expected_res is None:
            continue
        for spec in chunk[1:]:
            print_results_for_spec(omg, expected_res, spec)


def print_results_for_spec(omg, expected_res, spec):
    pos, neg = omg.check_all_initial_states(spec)
    spec_str = spec.str_math()
    for pos_s in pos:
        print 'M, ' + str(pos_s) + ' |= ' + spec_str + (BUG_LINE if not expected_res else "")
    for neg_s in neg:
        print 'M, ' + str(neg_s) + ' |=/= ' + spec_str + (BUG_LINE if expected_res else "")


def starts_with_l(str, ops):
    for op in ops:
        if str.startswith(op):
            return True
    return False


def check_properties():
    DIR = 'iimc_aigs/'
    file_names = os.listdir(DIR)
    instances = [(aig, aig[:-4] + '.ctl') for aig in file_names if
                 aig.endswith('.aig') and aig[:-4] + '.ctl' in file_names]

    bad, total = 0, 0
    good = []
    for instance in instances:
        ctl_path = DIR + instance[1]
        total += 1
        #   if not ctl_path.startswith(DIR + 'icctl'):
        #       continue

        print '--------' + ctl_path

        ctl_chunks = parse_ctl_file(ctl_path)
        chunk_aps = map(lambda f: f.get_aps(),
                        [formula for chunk in ctl_chunks for formula in chunk[1:]])
        ctl_aps = set(map(lambda ap: ap.get_ap_text(), functools.reduce(lambda r, y: set(r) | set(y), chunk_aps)))

        aig_parser = AvyAigParser('iimc_aigs/' + instance[0])
        ap_mapping = aig_parser.get_ap_mapping()
        latch_aps = set({k: ap_mapping[k] for k in ap_mapping.keys() if ap_mapping[k].startswith('l')}.keys())

        res = ctl_aps.issubset(latch_aps)
        if not res:
            bad += 1
            for x in ctl_aps.difference(latch_aps | {True, False}):
                if x not in ap_mapping.keys():
                    print '>>>>>>>>>>>>>>>>The AP ' + x + ' is missing in the aig file..'
                else:
                    print x + ' : ' + str(ap_mapping[x]) + ('<<<<<<<<<<<<<<' if (ap_mapping[x][0] == 'i') else '')
        else:
            good.append(instance[0])

    print 'BAD= ' + str(bad) + ' GOOD= ' + str(total - bad) + ' TOTAL= ' + str(total)
    print good


def check_files(aig_paths, ctl_paths):
    for i in range(len(aig_paths)):
        aig_file_path = aig_paths[i]
        ctl_formula_path = ctl_paths[i]

        file_name = ''.join(aig_file_path.split('/')[-1].split('.')[:-1])
        print 'Checking ' + file_name
        model_checking(aig_file_path, ctl_formula_path)
        print '------------------'


def test_propositional():
    print 'Checking Propositional:'
    aig_file_paths = ['iimc_aigs/af_ag.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_prop.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def test_nexts():
    print 'Checking Nexts:'
    aig_file_paths = ['iimc_aigs/af_ag.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_modal.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def test_AV():
    print 'Checking AVs:'
    aig_file_paths = ['iimc_aigs/af_ag.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_checkAV.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def regression_tests():
    test_propositional()
    test_nexts()
    test_AV()


if __name__ == '__main__':
    #    check_properties()

    regression_tests()
    model_checking(*parse_input())

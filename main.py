import functools
import sys
import os

from aig_parser import AvyAigParser
from ctl import CtlParser, is_balanced_brackets
from kripke_structure import AigKripkeStructure
from omg import OmgModelChecker


def parse_input():
    aig_file_path = sys.argv[1]
    ctl_formula_path = sys.argv[2]
    aig_file_path = 'iimc_aigs/af_ag.aig'
    ctl_formula_path = 'iimc_aigs/af_ag2.ctl'
    return aig_file_path, ctl_formula_path


def parse_ctl_chunk(chunk):
    chunk = filter(lambda line: line not in ['\n', '', ' '], chunk)
    first_line_not_header = next(i for i in range(len(chunk)) if not chunk[i].startswith('#'))
    header_part = chunk[:first_line_not_header]
    formula_part = chunk[first_line_not_header:]

    header_result = True if 'PASS' in ' '.join(header_part) else False

    ctl_parser = CtlParser()
    raw_formulas = formula_part
    f_indexes = [0] + [i + 1 for i in range(len(raw_formulas)) if
                       is_balanced_brackets(' '.join(raw_formulas[:(i + 1)]))]

    ctl_formulas_borders = [(f_indexes[i], f_indexes[i + 1] if i != len(f_indexes) - 1 else len(raw_formulas))
                            for i in range(len(f_indexes))]
    raw_ctl_formulas = [raw_formulas[start: end] for (start, end) in ctl_formulas_borders if start != end]

    single_line_raw_formulas = map(lambda multiline: ' '.join(multiline), raw_ctl_formulas)
    print 'CHUNK'
    for r in single_line_raw_formulas:
        print r
        print '----'
    ctl_formulas = map(lambda raw_formula: ctl_parser.parse_omg(raw_formula), single_line_raw_formulas)

    return [header_result] + ctl_formulas


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
                           [set(ctl_formula.get_atomic_propositions()) for chunk in ctl_chunks for ctl_formula in
                            chunk[1:]])
    kripke_structure = AigKripkeStructure(aig_path, aps)
    omg = OmgModelChecker(kripke_structure)
    for chunk in ctl_chunks:
        for spec in chunk[1:]:
            pos, neg = omg.check_all_initial_states(spec)

            spec_str = spec.str_math()
            for pos_s in pos:
                print 'M, ' + str(pos_s) + ' |= ' + spec_str
            for neg_s in neg:
                print 'M, ' + str(neg_s) + ' |=/= ' + spec_str


def starts_with_l(str, ops):
    for op in ops:
        if str.startswith(op):
            return True
    return False


def check_properties():
    file_names = os.listdir('iimc_aigs/')
    instances = [(aig, aig[:-4] + '.ctl') for aig in file_names if
                 aig.endswith('.aig') and aig[:-4] + '.ctl' in file_names]

    for instance in instances:
        ctl_path = instance[1]
        '''if starts_with_l(ctl_path,
                         ['priority', 'IFetchControl', 'am2910', 'minMax', 'amba16', 'vsa16a', 'simple16', 'icctl',
                          'simple8', 'amba8'] +
                         ['idu32', 'matrix', 'lock', 'anderson', 'reqAck', 'daio', 'bufferAlloc', 'rether', 'FIFO',
                          'twoFifo', 'spinner']):
            continue
            '''
        ctl_chunks = parse_ctl_file(ctl_path)
        chunk_aps = map(lambda f: f.get_atomic_propositions(),
                        [formula for chunk in ctl_chunks for formula in chunk[1:]])
        ctl_aps = set(map(lambda ap: ap.get_ap_text(), functools.reduce(lambda x, y: set(x) | set(y), chunk_aps)))

        aig_parser = AvyAigParser('iimc_aigs/' + instance[0])
        ap_mapping = aig_parser.get_ap_mapping()
        latch_aps = set({k: ap_mapping[k] for k in ap_mapping.keys() if ap_mapping[k].startswith('l')}.keys())

        res = ctl_aps.issubset(latch_aps)
        if not res:
            print instance[0]
            for x in ctl_aps.difference(latch_aps):
                print x


def test_propositional():
    aig_file_path = 'iimc_aigs/af_ag.aig'
    ctl_formula_path = 'iimc_aigs/af_ag_prop.ctl'
    model_checking(aig_file_path, ctl_formula_path)


def regression_tests():
    test_propositional()


def upupu():
    #    parse_ctl_file('iimc_aigs/priority.ctl')
    parse_ctl_file('iimc_aigs/priority.ctl')


if __name__ == '__main__':
    upupu()
    # regression_tests()
#  model_checking(*parse_input())

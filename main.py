import functools
import os
import sys
import time

from aig_parser import AvyAigParser
from ctl import CtlFileParser
from kripke_structure import AigKripkeStructure
from omg import OmgBuilder

BUG_LINE = '<------------------------------------------------------ BUG -------------------------------------'
SEP = '------------------------------------------------------------------------------------------'


def parse_input():
    aig_file_path = sys.argv[1]
    ctl_formula_path = sys.argv[2]
    return aig_file_path, ctl_formula_path


def model_checking(aig_path, ctl_path):
    ctl_chunks = CtlFileParser().parse_ctl_file(ctl_path)
    # print ctl_chunks
    aps = functools.reduce(lambda x, y: x | y,
                           [set(ctl_formula.get_aps()) for chunk in ctl_chunks for ctl_formula in
                            chunk[1:]])
    kripke_structure = AigKripkeStructure(aig_path, aps)
    omg = OmgBuilder().set_kripke(kripke_structure).build()

    for chunk in ctl_chunks:

        expected_res = chunk[0]
        if expected_res is None:
            continue
        for spec in chunk[1:]:
            print_results_for_spec(omg, expected_res, spec)
#            omg.get_abstract_trees_sizes()


def print_results_for_spec(omg, expected_res, spec):
    timer, (pos, neg) = time_me(omg.check_all_initial_states, [spec])
    spec_str = spec.str_math()
    for pos_s in pos:
        print 'M, ' + str(pos_s) + ' |= ' + spec_str + (BUG_LINE if not expected_res else "")
    for neg_s in neg:
        print 'M, ' + str(neg_s) + ' |=/= ' + spec_str + (BUG_LINE if expected_res else "")
    print 'Took: '+str(timer)
    print SEP


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

        ctl_chunks = CtlFileParser().parse_ctl_file(ctl_path)
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


def time_me(measuree, args):
    start = time.time()
    res = measuree(*args)
    end = time.time()
    return (end - start, res)

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
    aig_file_paths = ['iimc_aigs/af_ag.aig', 'iimc_aigs/gray.aig', 'iimc_aigs/gray.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_checkAV.ctl', 'iimc_aigs/gray_regression.ctl', 'iimc_aigs/gray_AV_abs.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def test_EV():
    print 'Checking EVs:'
    aig_file_paths = ['iimc_aigs/af_ag.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_checkEV.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def test_iimc():
    print 'Checking Actual IIMC examples:'
    TEST_NAMES = ['af_ag', 'debug', 'gray', 'gatedClock', 'microwave']
    aig_file_paths = ['iimc_aigs/' + test_name + '.aig' for test_name in TEST_NAMES]
    ctl_formula_paths = [(''.join(aig_path[:-4])+'.ctl') for aig_path in aig_file_paths]
    check_files(aig_file_paths, ctl_formula_paths)


def regression_tests():
    test_propositional()
    test_nexts()
    test_AV()
    test_EV()

    test_iimc()


if __name__ == '__main__':
    #    check_properties()

   regression_tests()
#    model_checking(*parse_input())

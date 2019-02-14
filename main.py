import functools
import time
from datetime import datetime

from arg_parser import OmgArgumentParser
from ctl import CtlFileParser
from kripke_structure import AigKripkeStructure
from omg import OmgBuilder

BUG_LINE = '<------------------------------------------------------ BUG -------------------------------------'
SEP = '------------------------------------------------------------------------------------------'

DEFAULT_FLAGS = {'-bu': True, '-tse': True}

import multiprocessing

OUTNAME = 'OUTPUTS.txt'
TIMEOUT = 300

def parse_input(src=None):
    arg_parser = OmgArgumentParser()
    return arg_parser.parse(src)


def model_checking(parsed_args):
    ctl_chunks = CtlFileParser().parse_ctl_file(parsed_args.ctl_path)
    # print ctl_chunks
    aps = functools.reduce(lambda x, y: x | y,
                           [set(ctl_formula.get_aps()) for chunk in ctl_chunks for ctl_formula in
                            chunk[1:]])

    timer, kripke_structure = time_me(AigKripkeStructure, [parsed_args.aig_path, aps])
    print 'Kripke Structure construction took: ' + str(timer)
    omg = OmgBuilder() \
        .set_kripke(kripke_structure) \
        .set_brother_unification(parsed_args.brother_unification) \
        .set_trivial_split_elimination(parsed_args.trivial_split_elimination) \
        .build()

    for chunk in ctl_chunks:

        expected_res = chunk[0]
        if expected_res is None:
            continue
        for spec in chunk[1:]:
            #            omg.get_abstract_trees_sizes()
            print_results_for_spec(omg, expected_res, spec)


def timeout_handler(signum, frame):
    print 'TIMEOUT!'
    raise Exception('End of time')


def print_results_for_spec(omg, expected_res, spec):
    timer, (pos, neg) = time_me(omg.check_all_initial_states, [spec])
    spec_str = spec.str_math()
    for pos_s in pos:
        print 'M, ' + str(pos_s) + ' |= ' + spec_str + (BUG_LINE if not expected_res else "")
    for neg_s in neg:
        print 'M, ' + str(neg_s) + ' |=/= ' + spec_str + (BUG_LINE if expected_res else "")
    print 'Model checking took: ' + str(timer)
    with open(OUTNAME, 'a') as f:
        f.write('Model checking took: ' + str(timer)+'\n')
    print SEP


def time_me(measuree, args):
    start = time.time()
    res = measuree(*args)
    end = time.time()
    return (end - start, res)


def check_files(aig_paths, ctl_paths):
    with open(OUTNAME, 'a') as f:
        f.write('$$$$$$$ '+str(datetime.now()))
    for i in range(len(aig_paths)):
        aig_file_path = aig_paths[i]
        ctl_formula_path = ctl_paths[i]

        file_name = ''.join(aig_file_path.split('/')[-1].split('.')[:-1])
        print 'Checking ' + file_name
        with open(OUTNAME, 'a') as f:
            f.write('Checking ' + file_name+'\n')

        input_line = '--aig-path {aig} --ctl-path {ctl} '.format(aig=aig_file_path, ctl=ctl_formula_path)
        input_line += ' '.join([flag for flag in DEFAULT_FLAGS.keys() if DEFAULT_FLAGS[flag]])
        parsed_args = parse_input(input_line.split())

        p = multiprocessing.Process(target=model_checking, args=(parsed_args,))
        p.start()
        p.join(TIMEOUT)
        if p.is_alive():
            print "TIMEOUT"
            with open(OUTNAME, 'a') as f:
                f.write('TIMEOUT\n')
            # Terminate
            p.terminate()
            p.join()
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
    ctl_formula_paths = [(''.join(aig_path[:-4]) + '.ctl') for aig_path in aig_file_paths]
    check_files(aig_file_paths, ctl_formula_paths)


def test_specific_test(test_name):
    print 'Checking {}:'.format(test_name)
    TEST_NAMES = [test_name]

    aig_file_paths = ['iimc_aigs/' + test_name + '.aig' for test_name in TEST_NAMES]
    ctl_formula_paths = [(''.join(aig_path[:-4]) + '.ctl') for aig_path in aig_file_paths]
    check_files(aig_file_paths, ctl_formula_paths)


def test_all_iimc():
    print 'Checking All IIMC examples:'
    with open('ordered_aigs.txt', 'r') as f:
        lines = f.readlines()
        TEST_NAMES = [line.split('.')[0] for line in lines if not line.startswith('#')]

    aig_file_paths = ['iimc_aigs/' + test_name + '.aig' for test_name in TEST_NAMES]
    ctl_formula_paths = [(''.join(aig_path[:-4]) + '.ctl') for aig_path in aig_file_paths]
    check_files(aig_file_paths, ctl_formula_paths)


def regression_tests():
    test_propositional()
    test_nexts()
    test_AV()
    test_EV()

    test_iimc()


if __name__ == '__main__':
    #    check_properties()
      test_specific_test('lock')
#    regression_tests()
#  model_checking(parse_input())
#  test_all_iimc()

import functools
import logging
import threading
import time
from datetime import datetime

from arg_parser import OmgArgumentParser
from ctl import CtlFileParser
from kripke_structure import AigKripkeStructure
from omg import OmgBuilder

TIMEOUT = 3600

BUG_LINE = '<------------------------------------------------------ BUG -------------------------------------'
SEP = '------------------------------------------------------------------------------------------'

DEFAULT_FLAGS = {'-bu': True, '-tse': True, '--qe_policy': 'qe-light', '-timeout': TIMEOUT}

DEBUG = True


def create_logger():
    logger = logging.getLogger('OMG')
    fh = logging.FileHandler('logs/run_' + str(datetime.now()) + '.log')
    fh.setLevel(logging.INFO)
    ch = logging.StreamHandler()
    ch.setLevel(logging.DEBUG)
    logger.addHandler(fh)
    logger.addHandler(ch)
    logger.setLevel(logging.DEBUG if DEBUG else logging.INFO)


def parse_input(src=None):
    arg_parser = OmgArgumentParser()
    return arg_parser.parse(src)


def check_files(aig_paths, ctl_paths):
    logging.getLogger('OMG').info('Run configurations: ' + str(DEFAULT_FLAGS))
    for i in range(len(aig_paths)):
        aig_file_path = aig_paths[i]
        ctl_formula_path = ctl_paths[i]

        input_line = get_input_line_for_files(aig_file_path, ctl_formula_path)

        parsed_args = parse_input(input_line.split())

        model_checking(parsed_args)
        logging.getLogger('OMG').info(SEP)


def get_input_line_for_files(aig_file_path, ctl_formula_path):
    file_name = ''.join(aig_file_path.split('/')[-1].split('.')[:-1])
    logging.getLogger('OMG').info('Checking ' + file_name)
    input_line = ''
    input_line += '-aig_path {aig} -ctl_path {ctl} '.format(aig=aig_file_path, ctl=ctl_formula_path)

    def flag_to_text(flag):
        if DEFAULT_FLAGS[flag] is True:
            return flag
        elif DEFAULT_FLAGS[flag] is False:
            return ''
        else:
            return flag + ' ' + str(DEFAULT_FLAGS[flag])

    input_line += ' '.join([flag_to_text(flag) for flag in DEFAULT_FLAGS.keys()])
    return input_line


def model_checking(parsed_args):
    ctl_chunks = CtlFileParser().parse_ctl_file(parsed_args.ctl_path)
    aps = functools.reduce(lambda x, y: x | y,
                           [set(ctl_formula.get_aps()) for chunk in ctl_chunks for ctl_formula in
                            chunk[1:]])

    try:
        timeout = parsed_args.timeout
        aig_path = parsed_args.aig_path
        timer, kripke_structure = time_me(AigKripkeStructure, [aig_path, aps, parsed_args.qe_policy], timeout)
        logging.getLogger('OMG').info('Kripke Structure construction took: ' + str(timer))
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
                print_results_for_spec(omg, expected_res, spec, timeout)

    except Exception as e:
        logging.getLogger('OMG').critical("Exception in model checking:: " + str(e))


def print_results_for_spec(omg, expected_res, spec, timeout):
    timer, (pos, neg) = time_me(omg.check_all_initial_states, [spec], timeout)
    spec_str = spec.str_math()
    for pos_s in pos:
        logging.getLogger('OMG').info('M, ' + str(pos_s) + ' |= ' + spec_str)
    for neg_s in neg:
        logging.getLogger('OMG').info('M, ' + str(neg_s) + ' |=/= ' + spec_str)

    is_property_satisfied = len(neg) == 0
    is_bug = is_property_satisfied != expected_res

    logging.getLogger('OMG').info('M |=' + ('' if is_property_satisfied else '/=') + spec_str +
                                  (BUG_LINE if is_bug else ''))
    logging.getLogger('OMG').info('Model checking took: ' + str(timer) + '\n' + SEP)


class DataWrapper(object):
    def __init__(self):
        self.data = None

def function_caller(to_run, args, ret):
   result = to_run(*args)
   ret.data = result


def time_me(measuree, args, timeout):
    e = threading.Event()
    res = DataWrapper()
    t = threading.Thread(target=function_caller, args=(measuree, args, res))
    start = time.time()
    t.start()

    t.join(int(timeout))
    if not t.is_alive():
        end = time.time()
        return end - start, res.data

    e.set()
    t.join()
    raise Exception('TIMEOUT')



def test_propositional():
    logging.getLogger('OMG').info('Checking Propositional:')
    aig_file_paths = ['iimc_aigs/af_ag.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_prop.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def test_nexts():
    logging.getLogger('OMG').info('Checking NEXTs:')
    aig_file_paths = ['iimc_aigs/af_ag.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_modal.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def test_AV():
    logging.getLogger('OMG').info('Checking AVs:')
    aig_file_paths = ['iimc_aigs/af_ag.aig', 'iimc_aigs/gray.aig', 'iimc_aigs/gray.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_checkAV.ctl', 'iimc_aigs/gray_regression.ctl', 'iimc_aigs/gray_AV_abs.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def test_EV():
    logging.getLogger('OMG').info('Checking EVs:')
    aig_file_paths = ['iimc_aigs/af_ag.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_checkEV.ctl']
    check_files(aig_file_paths, ctl_formula_paths)


def test_iimc():
    logging.getLogger('OMG').info('Checking Actual IIMC examples:')
    TEST_NAMES = ['af_ag', 'debug', 'gray', 'gatedClock', 'microwave', 'tstrst']

    aig_file_paths = ['iimc_aigs/' + test_name + '.aig' for test_name in TEST_NAMES]
    ctl_formula_paths = [(''.join(aig_path[:-4]) + '.ctl') for aig_path in aig_file_paths]
    check_files(aig_file_paths, ctl_formula_paths)


def test_specific_tests(test_names):
    logging.getLogger('OMG').info('Checking {}:'.format(test_names))

    aig_file_paths = ['iimc_aigs/' + test_name + '.aig' for test_name in test_names]
    ctl_formula_paths = [(''.join(aig_path[:-4]) + '.ctl') for aig_path in aig_file_paths]
    check_files(aig_file_paths, ctl_formula_paths)


def test_all_iimc():
    logging.getLogger('OMG').info('Checking All IIMC examples:')
    with open('goods.txt', 'r') as f:
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
    create_logger()

    #    test_specific_tests(['swap'])

    regression_tests()
#    model_checking(parse_input())
#    test_all_iimc()

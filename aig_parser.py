import itertools
import re
import os

OMG_EXE_PATH = '~/Desktop/extavy/cmake-build-debug/avy/src/omg'
AIG_SPLIT_EXE_PATH = '/home/galls2/Downloads/aiger-1.9.9/aigsplit'
AIG_EXAMPLE_PATH = 'AigFiles/'
IIMC_EXAMPLE_PATH = 'iimc_aigs/'
AIG_EXAMPLE_NAME = 'yakir4n.aig'
OUTPUT_PATH = 'iimc_dimacs/'

DIMACS_PREFIX = 'p'
HEADER_PREFIX = 'MAXVAR'


class AigParser(object):
    def parse(self):
        raise NotImplementedError()


class AvyAigParser(AigParser):
    def __init__(self, aig_path):
        super(AvyAigParser, self).__init__()
        self._aig_path = aig_path
        self._aig_lines = []
        with open(aig_path, 'r') as aig_file:
            self._aig_lines = aig_file.readlines()
            self._M, self._I, self._L, self._O, self._A = [int(val) for val in self._aig_lines[0].split(' ')[1:6]]

    def get_cnf(self, aig_path, cmd_arg):
        output_file_name = aig_path.split('/')[-1][:-4]
        out_path = "{}{}_{}.dimacs".format(OUTPUT_PATH, output_file_name, cmd_arg)
        cmd = "{} {} {} > {}".format(OMG_EXE_PATH, aig_path, cmd_arg, out_path)
        #    print cmd
        os.system(cmd)
        with open(out_path, 'r') as input_dimacs:
            txt = [line.replace('\n', '') for line in input_dimacs.readlines()]
        first_dimacs_line = next(line for line in txt if line.startswith(DIMACS_PREFIX))
        first_header_line = next(line for line in txt if line.startswith(HEADER_PREFIX))
        dimacs_content = txt[txt.index(first_dimacs_line):]
        metadata = txt[txt.index(first_header_line):txt.index(first_dimacs_line)]
        return metadata, dimacs_content

    def split_aig(self):
        if not os.path.isfile(AIG_SPLIT_EXE_PATH):
            raise IOError('No aigsplit file where you promised! Do you try to UPUPU??')

        cmd = AIG_SPLIT_EXE_PATH + ' ' + self._aig_path
        #    print cmd
        os.system(cmd)

    def delete_aux_files(self):
        pattern_to_remove = '.'.join(self._aig_path.split('.')[:-1]) + 'o*'
        #   print pattern_to_remove
        os.system('rm ' + pattern_to_remove)

    def parse(self):
        self.split_aig()

        def get_file_num_name(idx, O):
            return str(idx).zfill(len(str(O)))

        bad_file_names = ['.'.join(self._aig_path.split('.')[:-1]) + 'o' + get_file_num_name(i, self._O) + '.aig'
                          for i in range(self._O)]
        ltr_aig_path = bad_file_names[0]

        #  ltr_aig_path = '../../../../../PycharmProjects/OMG/iimc_aigs/'+ltr_aig_path.split('/')[-1]

        ltr_metadata, ltr_dimacs = self.get_cnf(ltr_aig_path, 'Tr')
        bads = [self.get_cnf(aig, 'Bad') for aig in bad_file_names]
        self.delete_aux_files()
        return [(ltr_metadata, ltr_dimacs)] + bads

    def get_num_latches(self):
        return self._L

    def get_initial_latch_values(self):
        def parse_latch_line(latch_line):
            parts = latch_line.replace('\n', '').split(' ')
            return [0] if len(parts) == 1 else ([int(parts[1])] if parts[1] in ['0', '1'] else [0, 1])

        latch_lines = self._aig_lines[1:self._L + 1]
        latch_options = [parse_latch_line(l_line) for l_line in latch_lines]
        return itertools.product(*latch_options)

    def get_ap_mapping(self):
        ap_line_regex = re.compile(".*[ilo][0-9]* .*")
        aps_lines = filter(lambda line: re.match(ap_line_regex, line.replace('\n', '')), self._aig_lines)

        ap_part_regex = re.compile("[ilo][0-9]* .*")
        aps = map(lambda ap_line: re.findall(ap_part_regex, ap_line)[0], aps_lines)
        return {' '.join(line.split(' ')[1:]): line.split(' ')[0] for line in aps}

    def get_num_outputs(self):
        return self._O

    def get_num_vars(self):
        return self._O + self._L

    def get_aig_after_reset(self):
        def reset_latch_line(_line):
            parts = _line.split(' ')
            return parts[0]+ ('\n' if len(parts) > 1 else '')

        return [self._aig_lines[0]] + \
               [reset_latch_line(line) for line in self._aig_lines[1:self._L + 1]] + \
               self._aig_lines[self._L + 1:]

    def get_aig_path(self):
        return self._aig_path
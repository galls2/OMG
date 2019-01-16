import os
import re

OMG_EXE_PATH = '~/Desktop/extavy/cmake-build-debug/avy/src/omg'
AIG_EXAMPLE_PATH = 'AigFiles/'
IIMC_EXAMPLE_PATH = 'iimc_aigs/'
AIG_EXAMPLE_NAME = 'yakir4n.aig'
OUTPUT_PATH = 'iimc_dimacs/'


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
            self._M, self._I, self._L, self._O, self._A = self._aig_lines[0].split(' ')[1:6]

    def parse(self):
        cmd_arg = 'Tr'
        output_file_name = self._aig_path.split('/')[-1][:-4]
        out_path = "{}{}_{}.dimacs".format(OUTPUT_PATH, output_file_name, cmd_arg)
        cmd = "{} {} {} > {}".format(OMG_EXE_PATH, self._aig_path, cmd_arg, out_path)
        os.system(cmd)
        with open(out_path, 'r') as input_dimacs:
            txt = input_dimacs.readlines()
        first_line = next(line for line in txt if line.startswith('p'))
        dimacs_content = txt[txt.index(first_line):]
        return dimacs_content

    def get_number_of_variables(self):
        return self._L

    def get_ap_mapping(self):
        ap_line_regex = re.compile(".*[ilo][0-9]* .*")
        aps_lines = filter(lambda line: re.match(ap_line_regex, line.replace('\n', '')), self._aig_lines)

        ap_part_regex = re.compile("[ilo][0-9]* .*")
        aps = map(lambda ap_line: re.findall(ap_part_regex, ap_line)[0], aps_lines)
        return aps


if __name__ == '__main__':
    fname = raw_input()
    print '%' + fname
    aig_parser = AvyAigParser(IIMC_EXAMPLE_PATH+fname)
    aig_parser.parse()

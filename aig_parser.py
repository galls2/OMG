import os

OMG_EXE_PATH = '~/Desktop/extavy/cmake-build-debug/avy/src/omg'
AIG_EXAMPLE_PATH = 'AigFiles/'
IIMC_EXAMPLE_PATH = 'iimc_aigs/'
AIG_EXAMPLE_NAME = 'yakir4n.aig'
OUTPUT_PATH = 'iimc_dimacs/'


class AigParser(object):
    def parse(self, aig_path, aig_name):
        raise NotImplementedError()


class AvyAigParser(AigParser):
    def __init__(self):
        super(AvyAigParser, self).__init__()

    def parse(self, aig_path, aig_name):
        cmd_arg = 'Tr'
        out_path = "{}{}_{}.dimacs".format(OUTPUT_PATH, aig_name[:-4], cmd_arg)
        in_path = aig_path + aig_name
        cmd = "{} {} {} > {}".format(OMG_EXE_PATH, in_path, cmd_arg, out_path)
        os.system(cmd)
        with open(out_path, 'r') as input_dimacs:
            txt = input_dimacs.readlines()
        first_line = next(line for line in txt if line.startswith('p'))
        txt = txt[txt.index(first_line):]
        return txt


if __name__ == '__main__':
    aig_parser = AvyAigParser()
    fname = raw_input()
    print '%' + fname
    aig_parser.parse(IIMC_EXAMPLE_PATH, fname)

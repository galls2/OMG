import os

OMG_EXE_PATH = '~/Desktop/extavy/cmake-build-debug/avy/src/omg'
AIG_EXAMPLE_PATH = 'AigFiles/'
AIG_EXAMPLE_NAME = 'yakir4n.aig'
OUTPUT_PATH = 'DimacsFiles/'
class AigParser(object):
    def parse(self, aig_path, aig_name):
        raise NotImplementedError()


class AvyAigParser(AigParser):
    def __init__(self):
        super(AvyAigParser, self).__init__()

    def parse(self, aig_path, aig_name):
        output = []
        for cmd_arg in ['Init', 'Tr', 'Bad']:
            out_path = "{}{}_{}.dimacs".format(OUTPUT_PATH,aig_name[:-4],cmd_arg)
            in_path = aig_path+aig_name
            cmd = "{} {} {} > {}".format(OMG_EXE_PATH, in_path, cmd_arg, out_path)
            os.system(cmd)
            txt = ''
            with open(out_path, 'r') as input_dimacs:
                txt = input_dimacs.readlines()
            first_line = next(line for line in txt if line.startswith('p'))
            txt = txt[txt.index(first_line):]
            output.append(txt)
        return output


if __name__ == '__main__':
    aig_parser = AvyAigParser()
    aig_parser.parse(AIG_EXAMPLE_PATH, AIG_EXAMPLE_NAME)

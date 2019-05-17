import argparse


class OmgArgumentParser(object):
    def __init__(self):
        super(OmgArgumentParser, self).__init__()

    def parse(self, src=None):
        parser = argparse.ArgumentParser()

        parser.add_argument('-bu', '--brother-unification', action='store_true')
        parser.add_argument('-tse', '--trivial-split-elimination', action='store_true')
        parser.add_argument('-f_aps', '--few-aps', action='store_true')
        parser.add_argument('--qbf_solver', choices=['z3', 'depqbf'], default='depqbf')
        parser.add_argument('-timeout', '--timeout', default=None)
        parser.add_argument('-ctl_path', action='store', required=True)
        parser.add_argument('-aig_path', action='store', required=True)

        res = parser.parse_args() if src is None else parser.parse_args(src)
        return res


if __name__ == '__main__':
    OmgArgumentParser().parse()

import argparse


class OmgArgumentParser(object):
    def __init__(self):
        super(OmgArgumentParser, self).__init__()

    def parse(self, src=None):
        parser = argparse.ArgumentParser()

        parser.add_argument('-bu', '--brother-unification', action='store_true')
        parser.add_argument('-tse', '--trivial-split-elimination', action='store_true')
        parser.add_argument('-few_aps', action='store_true')
        parser.add_argument('--qe_policy', choices=['qe', 'qe-light', 'no-qe'], default='no-qe')
        parser.add_argument('--qbf_solver', choices=['z3', 'caqe', 'depqbf'], default='no-qe')
        parser.add_argument('-timeout', default=None)
        parser.add_argument('-ctl_path', action='store', required=True)
        parser.add_argument('-aig_path', action='store', required=True)

        res = parser.parse_args() if src is None else parser.parse_args(src)
        return res


if __name__ == '__main__':
    OmgArgumentParser().parse()

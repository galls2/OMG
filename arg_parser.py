import argparse


class OmgArgumentParser(object):
    def __init__(self):
        super(OmgArgumentParser, self).__init__()

    def parse(self, src=None):
        parser = argparse.ArgumentParser()
        parser.add_argument('--aig-path')
        parser.add_argument('--ctl-path')
        parser.add_argument('-bu', '--brother-unification', action='store_true')
        parser.add_argument('-tse', '--trivial-split-elimination', action='store_true')
        res = parser.parse_args() if src is None else parser.parse_args(src)
        return res


if __name__ == '__main__':
    OmgArgumentParser().parse()

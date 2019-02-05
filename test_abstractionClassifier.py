import functools
from unittest import TestCase

from mockito import mock, when, args
from z3 import Bool

from abstract_structure import AbstractState
from abstraction_classifier import AbstractionClassifier, AbstractionCache
from ctl import CtlFileParser
from kripke_structure import AigKripkeStructure


class TestAbstractionClassifier(TestCase):
    def setUp(self):
        aig_path = 'iimc_aigs/af_ag.aig'
        ctl_path = 'iimc_aigs/af_ag_checkAV.ctl'
        ctl_chunks = CtlFileParser().parse_ctl_file(ctl_path)
        # print ctl_chunks
        aps = functools.reduce(lambda x, y: x | y,
                               [set(ctl_formula.get_aps()) for chunk in ctl_chunks for ctl_formula in
                                chunk[1:]])
        self._kripke_structure = AigKripkeStructure(aig_path, aps)

        self._my_cache = AbstractionCache()

    def test_cache_is_used(self):
        def get_cache():
            return self._my_cache

        classifier = AbstractionClassifier(self._kripke_structure, get_cache)
        state = (0, 0, 0)

        abst = AbstractState({}, self._kripke_structure, self._kripke_structure.get_bis0_formula(state, [Bool('x'+str(i)) for i in range(3)]))

        classifier.add_classification((), abst)
        classifier.classify(state)
        assert self._my_cache.exists_key(state)
        assert self._my_cache[state] == abst

        self._my_cache[state] = None
        assert classifier.classify(state) is None


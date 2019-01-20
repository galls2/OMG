from aig_parser import AvyAigParser
from cnf_parser import CnfParser
from formula_wrapper import FormulaWrapper
from z3_utils import Z3Utils


class KripkeStructure(object):
    def __init__(self, atomic_propositions):
        super(KripkeStructure, self).__init__()
        self._atomic_propositions = atomic_propositions

    def get_atomic_propositions(self):
        return self._atomic_propositions

    def get_successors(self, state):
        raise NotImplementedError()

    def get_initial_states(self):
        raise NotImplementedError()

    def is_state_labeled_with(self, state, ap):
        raise NotImplementedError()

    def get_formula_for_ap(self, ap, var_vector):
        raise NotImplementedError()

    def get_formula_for_bis0(self, state, var_vector):
        raise NotImplementedError()

    def get_tr_formula(self):
        raise NotImplementedError()


class AigKripkeStructure(KripkeStructure):
    def __init__(self, aig_path, atomic_propositions):
        super(AigKripkeStructure, self).__init__(atomic_propositions)
        self._aig_parser = AvyAigParser(aig_path)
        metadata, tr_dimcas = self._aig_parser.parse()
        self._tr = CnfParser.z3_formula_from_dimacs(metadata, tr_dimcas)
        self._ap_conversion = self._aig_parser.get_ap_mapping()

    def get_successors(self, state):
        return Z3Utils.get_all_successors(self._tr, state)

    def get_initial_states(self):
        return [0] * self._aig_parser.get_number_of_variables()

    def _get_var_num_for_ap(self, ap):
        ap_symb = self._ap_conversion[ap]
        if ap_symb[0] != 'l':
            raise Exception('Not state AP :( Talk to yakir dude...')
        var_num = int(ap_symb[1:])
        return var_num

    def is_state_labeled_with(self, state, ap):
        var_num = self._get_var_num_for_ap(ap)
        return True if int(state[var_num]) > 0 else False

    def get_formula_for_ap(self, ap, var_vector):
        return FormulaWrapper(var_vector[self._get_var_num_for_ap(ap)], [var_vector])

    def get_formula_for_bis0(self, state, var_vector):
        return FormulaWrapper(And(*[self.get_formula_for_ap(ap, var_vector) for ap in self.get_atomic_propositions()]),
                              var_vector)

    def get_tr_formula(self):
        return self._tr


class DummyKripkeStructure(KripkeStructure):
    def __init__(self, atomic_propositions, states, transitions, initial_states, labeling):
        super(DummyKripkeStructure, self).__init__(atomic_propositions)
        self._states = states
        self._transitions = transitions
        self._initial_states = initial_states
        self._labeling = labeling

    def get_successors(self, state):
        return self._transitions

    def get_initial_states(self):
        return self._initial_states

    def is_state_labeled_with(self, state, ap_str):
        # ap is assumed to be a string
        return ap_str in self._labeling[state]

    def __str__(self):
        acc = '--- States ---\n'
        for state in self._states:
            if state in self.get_initial_states():
                acc += '-> '
            acc += str(state) + ': '
            for ap in self._atomic_propositions:
                acc += (str(ap) if self.is_state_labeled_with(state, ap) else '~' + str(ap)) + ' '
            acc += '\n'

        acc += '\n--- Transitions ---\n'
        for state in self._states:
            acc += str(state) + ' -> '
            for destination in self._transitions[state]:
                acc += str(destination) + ' '
            acc += '\n'
        return acc

    def get_aps(self, state):
        return self._labeling[state]


def get_simple_kripke_structure():
    return DummyKripkeStructure({'p', 'q'},
                                [i for i in range(3)],
                                {i: [(i + 1) % 3] for i in range(3)},
                                [0, 1, 2],
                                {0: ['p'], 1: ['p', 'q'], 2: ['q']})


def test_kripke_printing():
    print str(get_simple_kripke_structure())


if __name__ == '__main__':
    test_kripke_printing()

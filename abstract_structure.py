from kripke_structure import get_simple_kripke_structure


class AbstractState(object):
    def __init__(self, atomic_labels, kripke_structure, formula):
        super(AbstractState, self).__init__()
        self._kripke_structure = kripke_structure

        self.positive_labels = set(atomic_labels)
        self.negative_labels = set(self._kripke_structure.get_atomic_propositions()) - self.positive_labels

        self.atomic_labels = atomic_labels
        self._classification_node = None

        self._formula = formula

    def get_descriptive_formula(self):
        return self._formula

    def add_positive_labels(self, labels):
        self.positive_labels |= labels
        return self

    def add_negative_labels(self, labels):
        self.negative_labels |= labels
        return self

    def is_positive_label(self, label):
        return label in self.positive_labels

    def is_negative_label(self, label):
        return label in self.negative_labels

    def update_classification(self, concrete_state):
        if self._classification_node.is_leaf():
            return self._classification_node.get_value()

        classification_node = self.get_classification_node()
        classifier = classification_node.get_classifier()
        new_classification = classifier.update_classification(classification_node, concrete_state)
        return new_classification

    def get_classification_node(self):
        return self._classification_node

    def set_classification_node(self, classification_leaf):
        self._classification_node = classification_leaf
        return self


class AbstractStructure(object):
    """docstring for AbstractStructure."""

    def __init__(self, kripke_structure):
        super(AbstractStructure, self).__init__()
        self._kripke_structure = kripke_structure
        self._abstract_states = set()
        #  self._existing_may_transitions = {}
        self._non_existing_may_transitions = {}
        self._may_transitions_over_approximations = {}
        self._non_existing_may_transitions_over_approximations = {}
        self._existing_must_transitions = {}
        self._non_existing_must_transitions = {}

    def add_abstract_state(self, abstract_state):
        self._abstract_states.add(abstract_state)
        return self

    '''
    def add_may_transition(self, src, dst):
        if src not in self._existing_may_transitions.keys():
            self._existing_may_transitions[src] = set()
        self._existing_may_transitions[src].add(dst)
    '''

    def add_must_hyper_transition(self, src, hyper_dst):
        if src not in self._existing_must_transitions.keys():
            self._existing_must_transitions[src] = set()
        self._existing_must_transitions[src].add(hyper_dst)
        return self

    def is_EE_closure(self, to_close, close_with):
        if to_close in self._may_transitions_over_approximations.keys():
            known_closers = self._may_transitions_over_approximations[to_close]
            if close_with.issubset(known_closers):
                return True

        # Check actually! Return Either True or CEX
        raise NotImplementedError()  # TODO

    def split_abstract_state(self, to_close, witness_abstract_state):
        new_abs_has_sons = AbstractState(to_close.atomic_labels, self._kripke_structure) \
            .add_positive_labels(to_close.positive_labels) \
            .add_negative_labels(to_close.negative_labels)

        new_abs_no_sons = AbstractState(to_close.atomic_labels, self._kripke_structure) \
            .add_positive_labels(to_close.positive_labels) \
            .add_negative_labels(to_close.negative_labels)

        self._abstract_states.remove(to_close[0])
        self._abstract_states.update([new_abs_has_sons, new_abs_no_sons])

        # must-from

        old_dst = self._existing_must_transitions.pop(to_close[0])
        self._existing_must_transitions.update({new_abs_has_sons: old_dst, new_abs_no_sons: old_dst})

        self._non_existing_must_transitions.pop(to_close[0])

        # must-to
        replace_old_value = lambda dct: dct.updare({key: dict[key]
                                                   .difference(to_close[0])
                                                   .union([new_abs_has_sons, new_abs_no_sons])
                                                    for key in dct.keys()
                                                    if to_close[0] in dct[key]})
        replace_old_value(self._existing_must_transitions)
        replace_old_value(self._non_existing_must_transitions)

        # split info
        self._existing_must_transitions[new_abs_has_sons].add({witness_abstract_state})
        self._non_existing_may_transitions[new_abs_no_sons].append(witness_abstract_state)

        return new_abs_has_sons, new_abs_no_sons


def test_dummy():
    kripke = get_simple_kripke_structure()

    abs_state = AbstractState(['p'], kripke)
    abs_state2 = AbstractState(['q'], kripke)
    abs_structure = AbstractStructure(kripke)


if __name__ == '__main__':
    test_dummy()

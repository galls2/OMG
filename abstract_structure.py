class AbstractState(object):
    def __init__(self, atomic_labels, kripke_structure):
        super(AbstractState, self).__init__()
        self._kripke_structure = kripke_structure

        self._positive_labels = set(atomic_labels)
        self._negative_labels = set(self._kripke_structure.get_atomic_propositions()) - self._positive_labels

        self._classification_leaf = None

    def add_positive_label(self, label):
        self._positive_labels.add(label)

    def add_negative_label(self, label):
        self._negative_labels.add(label)

    def is_positive_label(self, label):
        return label in self._positive_labels

    def is_negative_label(self, label):
        return label in self._negative_labels

    def get_classification_leaf(self):
        return self._classification_leaf

    def set_classification_leaf(self, classification_leaf):
        self._classification_leaf = classification_leaf


class AbstractStructure(object):
    """docstring for AbstractStructure."""
    def __init__(self, kripke_structure):
        super(AbstractStructure, self).__init__()
        self._kripke_structure = kripke_structure
        self._existing_may_transitions = []
        self._non_existing_may_transitions = []
        self._may_transitions_over_approximations = []
        self._non_existing_may_transitions_over_approximations = []
        self._existing_must_transitions = []
        self._non_existing_must_transitions = []


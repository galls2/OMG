class AbstractState(object):

    def __init__(self, atomic_labels):
        super(AbstractState, self).__init__()
        self._labels = atomic_labels

    def add_label(self, label):
        self._labelings.append(label)

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


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
        raise NotImplementedError


class DummyKripkeStructure(KripkeStructure):
    def get_successors(self, state):
        return self._transitions[state]

    def get_initial_states(self):
        return self._initial_states

    def is_state_labeled_with(self, state, ap):
        return ap in self._labeling[state]

    def __init__(self, atomic_propositions, states, transitions, initial_states, labeling):
        super(KripkeStructure, self).__init__(atomic_propositions)
        self._states = states
        self._transitions = transitions
        self._initial_states = initial_states
        self._labeling = labeling





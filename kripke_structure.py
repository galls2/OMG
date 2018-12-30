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
    def __init__(self, atomic_propositions):
        super(KripkeStructure, self).__init__(atomic_propositions)



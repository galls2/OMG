class AbstractionClassifier(object):
    """docstring for AbstractionClassifier."""
    def __init__(self, kripke_structure):
        super(AbstractionClassifier, self).__init__()
        self._kripke_structure = kripke_structure

    def classify(self, concrete_state):
        raise NotImplementedError()


class AbstractionClassifierInternal(AbstractionClassifier):
    """docstring for AbstractionClassifier."""
    def __init__(self, kripke_structure, query, successors):
        super(AbstractionClassifierInternal, self).__init__(kripke_structure)
        self._query = query
        self._successors = successors

    def classify(self, concrete_state):
        return self._successors[self._query(concrete_state)].classify(concrete_state)

    def split(self, abstract_state, criteria):
        raise NotImplementedError()


class AbstractionClassifierLeaf(AbstractionClassifier):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke_structure, value):
        super(AbstractionClassifierLeaf, self).__init__(kripke_structure)
        self._value = value

    def classify(self, concrete_state):
        return self._value

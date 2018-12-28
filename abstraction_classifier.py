class AbstractionClassifier(object):
    """docstring for AbstractionClassifier."""
    def __init__(self, kripke_structure):
        super(AbstractionClassifier, self).__init__()
        self._kripke_structure = kripke_structure

    def classify(self, concrete_state):
        raise NotImplementedError()

class AbstractState(object):

    def __init__(self):
        super(AbstractState, self).__init__()


class AbstractStructure(object):
    """docstring for AbstractStructure."""
    def __init__(self, kripke_structure):
        super(AbstractStructure, self).__init__()
        self._kripke_structure = kripke_structure

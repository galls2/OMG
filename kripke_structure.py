class KripkeStructure(object):
    def __init__(self):
        super(KripkeStructure, self).__init__()

    def get_successors(self, state):
        raise NotImplementedError()

    def get_initial_states(self):
        raise NotImplementedError()

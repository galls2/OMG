class OmgModelChecker(object):
    """
    This is the main tool's class.
    Create a new one for each structure.
    """

    def __init__(self, kripke_structure):
        super(OmgModelChecker, self).__init__()
        self._kripke_structure = kripke_structure
        self.initialize_abstraction()
        self._unwinding_trees = [] ## TODO: ## OPTIMIZE: in the future

    def initialize_abstraction(self):
        self._abstract_structure = AbstractStructure(self._kripke_structure)
        self._abstraction = AbstractionClassifier()

    def clean_intermediate_data(self):
        self.initialize_abstraction()
        self._unwinding_trees = []

    def check_all_initial_states(self, specification):
        positive_answer = []
        negative_answer = []
        for initial_state in self._kripke_structure.get_initial_states():
            model_checking_result = self.check(initial_state, specification)
            if model_checking_result:
                positive_answer.append(initial_state)
            else:
                negative_answer.append(initial_state)
        return positive_answer, negative_answer

    def check(self, state, specification):
        pass



if __name__ == '__main__':
    print 'Welcome to the OMG model checker!'

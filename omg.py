from abstract_structure import AbstractStructure
from abstraction_classifier import AbstractionClassifier


class OmgModelChecker(object):
    """
    This is the main tool's class.
    Create a new one for each structure.
    """

    def __init__(self, kripke_structure):
        super(OmgModelChecker, self).__init__()
        self._kripke_structure = kripke_structure
        self.initialize_abstraction()
        self._unwinding_trees = []  ## TODO: ## OPTIMIZE: in the future

    def initialize_abstraction(self):

        self._abstract_structure = AbstractStructure(self._kripke_structure)
        self._abstraction = AbstractionClassifier(self._kripke_structure)

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

    def handle_atomic_propositions(self, state, specification):
        return self._kripke_structure.is_state_labeled_with(state, specification)

    def handle_and(self, state, left_operand, right_operand):
        return self.check(state, left_operand) and self.check(state, right_operand)

    def handle_or(self, state, left_operand, right_operand):
        return self.check(state, left_operand) or self.check(state, right_operand)

    def handle_arrow(self, state, left_operand, right_operand):
        return (not self.check(state, left_operand)) or (self.check(state, right_operand))

    def handle_not(self, state, operand):
        return not self.check(state, operand)

    def handle_AV(self, state, left_operand, right_operand):
        raise NotImplementedError()

    def handle_EV(self, state, left_operand, right_operand):
        raise NotImplementedError()

    def handle_EU(self, state, left_operand, right_operand):
        raise NotImplementedError()

    def handle_AU(self, state, left_operand, right_operand):
        raise NotImplementedError()

    def handle_AG(self, state, operand):
        raise NotImplementedError()

    def handle_EG(self, state, operand):
        raise NotImplementedError()

    def handle_AF(self, state, operand):
        raise NotImplementedError()

    def handle_EF(self, state, operand):
        raise NotImplementedError()

    def handle_AX(self, state, operand):
        raise NotImplementedError()

    def handle_EX(self, state, operand):
        raise NotImplementedError()

    def check(self, state, specification):
        if specification.is_atomic_proposition():
            return self.handle_atomic_propositions(state, specification)
        main_connective = specification.get_main_connective()
        operands = specification.get_operands()
        method_mapping = {'&': OmgModelChecker.handle_and,
                          '|': OmgModelChecker.handle_or,
                          '->': OmgModelChecker.handle_arrow,
                          '~': OmgModelChecker.handle_not,
                          '!': OmgModelChecker.handle_not,
                          'AV': OmgModelChecker.handle_AV,
                          'EV': OmgModelChecker.handle_EV,
                          'AU': OmgModelChecker.handle_AU,
                          'EU': OmgModelChecker.handle_EU,
                          'AG': OmgModelChecker.handle_AG,
                          'EG': OmgModelChecker.handle_EG,
                          'EX': OmgModelChecker.handle_EX,
                          'AX': OmgModelChecker.handle_AX,
                          'AF': OmgModelChecker.handle_AF,
                          'EF': OmgModelChecker.handle_EF,
                          }
        return method_mapping[main_connective](self, state, *operands)


if __name__ == '__main__':
    print 'Welcome to the OMG model checker!'
    print 'a'

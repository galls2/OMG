from abstract_structure import AbstractStructure
from abstraction_classifier import AbstractionClassifier
from heapq import *

class OmgModelChecker(object):
    """
    This is the main tool's class.
    Create a new one for each structure.
    """

    def __init__(self, kripke_structure):
        super(OmgModelChecker, self).__init__()
        self._kripke_structure = kripke_structure
        self._abstract_structure = None
        self._abstraction = None
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

    def handle_and(self, state, left_operand, right_operand, full_spec):
        raise NotImplementedError()
      #  return self.check(state, left_operand) and self.check(state, right_operand)

    def handle_or(self, state, left_operand, right_operand, full_spec):
        raise NotImplementedError()
        res = self.check(state, left_operand) or self.check(state, right_operand)
        #if res:

      #  return
    def handle_arrow(self, state, left_operand, right_operand, full_spec):
        raise NotImplementedError()
     #   return (not self.check(state, left_operand)) or (self.check(state, right_operand))

    def handle_not(self, state, operand, full_spec):
        raise NotImplementedError()
    #    return not self.check(state, operand)

    def handle_av(self, state, p, q, full_spec):
        to_visit = heapify([state])
        while to_visit:
            node_to_explore = heappop(to_visit)
            self.check(node_to_explore, q)
            if node_to_explore.is_labeled_negatively_with(q):
                current = node_to_explore
                while current is not None:
                    current.add_negative_label(full_spec)
                return False


    def handle_ev(self, state, p, q, full_spec):
        raise NotImplementedError()

    def handle_eu(self, state, p, q, full_spec):
        raise NotImplementedError()

    def handle_au(self, state, p, q, full_spec):
        raise NotImplementedError()

    def handle_ag(self, state, operand, full_spec):
        raise NotImplementedError()

    def handle_eg(self, state, operand, full_spec):
        raise NotImplementedError()

    def handle_af(self, state, operand, full_spec):
        raise NotImplementedError()

    def handle_ef(self, state, operand, full_spec):
        raise NotImplementedError()

    def handle_ax(self, state, operand, full_spec):
        raise NotImplementedError()

    def handle_ex(self, state, operand, full_spec):
        raise NotImplementedError()

    def check(self, state, specification):
        if specification in [True, False]:
            return specification

        if specification.is_atomic_proposition():
            return self.handle_atomic_propositions(state, specification)

        main_connective = specification.get_main_connective()
        operands = specification.get_operands()
        method_mapping = {'&': OmgModelChecker.handle_and,
                          '|': OmgModelChecker.handle_or,
                          '->': OmgModelChecker.handle_arrow,
                          '~': OmgModelChecker.handle_not,
                          '!': OmgModelChecker.handle_not,
                          'AV': OmgModelChecker.handle_av,
                          'EV': OmgModelChecker.handle_ev,
                          'AU': OmgModelChecker.handle_au,
                          'EU': OmgModelChecker.handle_eu,
                          'AG': OmgModelChecker.handle_ag,
                          'EG': OmgModelChecker.handle_eg,
                          'EX': OmgModelChecker.handle_ex,
                          'AX': OmgModelChecker.handle_ax,
                          'AF': OmgModelChecker.handle_af,
                          'EF': OmgModelChecker.handle_ef,
                          }
        return method_mapping[main_connective](self, state, *operands)


if __name__ == '__main__':
    print 'Welcome to the OMG model checker!'
    print 'a'

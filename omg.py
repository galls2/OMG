from abstract_structure import AbstractStructure
from abstraction_classifier import AbstractionClassifier
from heapq import *

from ctl import CtlParser
from kripke_structure import get_simple_kripke_structure
from unwinding_tree import UnwindingTree


def _label_state(check_result, node_to_label, spec):
    if check_result:
        node_to_label.add_positive_label(spec)
    else:
        node_to_label.add_negative_label(spec)
    return check_result


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
        self._initialize_abstraction()
        self._unwinding_trees = []

    def _initialize_abstraction(self):
        self._abstract_structure = AbstractStructure(self._kripke_structure)
        self._abstraction = AbstractionClassifier(self._kripke_structure)

    def clean_intermediate_data(self):
        self._initialize_abstraction()
        self._unwinding_trees = []

    def check_all_initial_states(self, specification):
        positive_answer = []
        negative_answer = []
        for initial_state in self._kripke_structure.get_initial_states():
            model_checking_result = self.handle_ctl(initial_state, specification)
            if model_checking_result:
                positive_answer.append(initial_state)
            else:
                negative_answer.append(initial_state)
        return positive_answer, negative_answer

    def _handle_atomic_propositions(self, node, spec):
        concrete_state = node.concrete_label
        return self._kripke_structure.is_state_labeled_with(concrete_state, spec)

    def _handle_and(self, node, left_operand, right_operand, spec):
        concrete_state = node.concrete_label
        return _label_state(self._handle_ctl_and_recur(concrete_state, left_operand) and self._handle_ctl_and_recur(concrete_state, right_operand),
                            node, spec)

    def _handle_or(self, node, left_operand, right_operand, spec):
        concrete_state = node.concrete_label
        return _label_state(self._handle_ctl_and_recur(concrete_state, left_operand) or self._handle_ctl_and_recur(concrete_state, right_operand),
                            node, spec)

    def _handle_arrow(self, node, left_operand, right_operand, spec):
        concrete_state = node.concrete_label
        return _label_state(
            (not self._handle_ctl_and_recur(concrete_state, left_operand)) or (self._handle_ctl_and_recur(concrete_state, right_operand)),
            node, spec)

    def _handle_not(self, node, operand, spec):
        res = self._handle_ctl_and_recur(node, operand)
        if res:
            node.add_negative_label(spec)
        else:
            node.add_positive_label(spec)
        return res

    def _handle_av(self, node, p, q, spec):
        to_visit = heapify([node])
        while to_visit:
            node_to_explore = heappop(to_visit)
            self._handle_ctl_and_recur(node_to_explore, q)
            if node_to_explore.is_labeled_negatively_with(q):
                current = node_to_explore
                while current is not None:
                    current.add_negative_label(spec)
                return False
            self._handle_ctl_and_recur(node_to_explore, p)
            if node_to_explore.is_labeled_negatively_with(p):
                children_nodes = node_to_explore.unwind_further()
                for child_node in children_nodes:
                    heappush(to_visit, child_node)
            else:
                current = node_to_explore
                while current is not None:
                    current.add_positive_label(spec)
                continue
            #update abstract things

        node.add_positive_label(spec)
        return True

            #update abstract data structures according to transitions

    def _handle_ev(self, node, p, q, spec):
        raise NotImplementedError()

    def _handle_eu(self, node, p, q, spec):
        raise NotImplementedError()

    def _handle_au(self, node, p, q, spec):
        raise NotImplementedError()

    def _handle_ag(self, node, operand, spec):
        raise NotImplementedError()

    def _handle_eg(self, node, operand, spec):
        raise NotImplementedError()

    def _handle_af(self, node, operand, spec):
        raise NotImplementedError()

    def _handle_ef(self, node, operand, spec):
        raise NotImplementedError()

    def _handle_ax(self, node, operand, spec):
        raise NotImplementedError()

    def _handle_ex(self, node, operand, spec):
        raise NotImplementedError()

    def handle_ctl(self, state, specification):
        unwinding_tree = UnwindingTree(self._kripke_structure, None, [], state)
        # TODO check or add to the collection of unwinding trees that are saved in this omg_checker as a member.
        return self._handle_ctl_and_recur(unwinding_tree, specification)

    def _handle_ctl_and_recur(self, node, specification):
        method_mapping = {'&': OmgModelChecker._handle_and,
                          '|': OmgModelChecker._handle_or,
                          '->': OmgModelChecker._handle_arrow,
                          '~': OmgModelChecker._handle_not,
                          '!': OmgModelChecker._handle_not,
                          'AV': OmgModelChecker._handle_av,
                          'EV': OmgModelChecker._handle_ev,
                          'AU': OmgModelChecker._handle_au,
                          'EU': OmgModelChecker._handle_eu,
                          'AG': OmgModelChecker._handle_ag,
                          'EG': OmgModelChecker._handle_eg,
                          'EX': OmgModelChecker._handle_ex,
                          'AX': OmgModelChecker._handle_ax,
                          'AF': OmgModelChecker._handle_af,
                          'EF': OmgModelChecker._handle_ef,
                          }

        if specification in [True, False]:
            return specification

        if specification.is_atomic_proposition():
            return self._handle_atomic_propositions(node, specification)

        main_connective = specification.get_main_connective()
        operands = specification.get_operands()

        return method_mapping[main_connective](self, node, *operands)


def test_propositional_logic():
    kripke_structure = get_simple_kripke_structure()

    ctl_parser = CtlParser()
    raw_specification = '(q & p) | (q -> p)'
    specification = ctl_parser.parse_math_format(raw_specification)

    omg_model_checker = OmgModelChecker(kripke_structure)
    pos, neg = omg_model_checker.check_all_initial_states(specification)
    print 'M, s |= '+specification.str_math() + 'for s in '+str(pos)
    print 'M, s |/= '+specification.str_math() + 'for s in '+str(neg)


if __name__ == '__main__':
    print 'Welcome to the OMG model checker!'
    test_propositional_logic()

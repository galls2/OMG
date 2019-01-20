from heapq import *

from abstract_structure import AbstractStructure, AbstractState
from abstraction_classifier import AbstractionClassifier
from ctl import CtlParser
from kripke_structure import get_simple_kripke_structure
from unwinding_tree import UnwindingTree


def _label_state(check_result, node_to_label, spec):
    if check_result:
        node_to_label.add_positive_label(spec)
    else:
        node_to_label.add_negative_label(spec)
    return check_result


def _map_upward_from_node(node, mapper):
    current = node
    while current is not None:
        mapper(current)
        current = current.get_parent()


class OmgModelChecker(object):
    """
    This is the main tool's class.
    Create a new one for each structure.
    """

    def __init__(self, kripke_structure, produce_abstraction=False):
        super(OmgModelChecker, self).__init__()
        self._kripke_structure = kripke_structure
        self._abstract_structure = None
        self._abstraction = None
        self._initialize_abstraction()
        self._unwinding_trees = []
        self._produce_abstraction = produce_abstraction

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
        res = self._kripke_structure.is_state_labeled_with(concrete_state, spec.get_ap_text())
        return res

    def _handle_and(self, node, spec, left_operand, right_operand):
        return _label_state(
            self._handle_ctl_and_recur(node, left_operand) and self._handle_ctl_and_recur(node, right_operand),
            node, spec)

    def _handle_or(self, node, spec, left_operand, right_operand):
        return _label_state(
            self._handle_ctl_and_recur(node, left_operand) or self._handle_ctl_and_recur(node, right_operand),
            node, spec)

    def _handle_arrow(self, node, spec, left_operand, right_operand):
        return _label_state(
            (not self._handle_ctl_and_recur(node, left_operand)) or (self._handle_ctl_and_recur(node, right_operand)),
            node, spec)

    def _handle_not(self, node, spec, operand):
        res = self._handle_ctl_and_recur(node, operand)
        if res:
            node.add_negative_label(spec)
        else:
            node.add_positive_label(spec)
        return res

    def _handle_av(self, node, spec, p, q):  ##goover
        to_visit = heapify([node])
        while to_visit:
            node_to_explore = heappop(to_visit)
            abstract_state = self.find_abstract_classification_for_node(node_to_explore)

            self._handle_ctl_and_recur(node_to_explore, q)
            if node_to_explore.is_labeled_negatively_with(q):
                _map_upward_from_node(node_to_explore, lambda current_node: current_node.add_negative_label(spec))
                if self._produce_abstraction:
                    self._strengthen_trace(node_to_explore)
                return False

            self._handle_ctl_and_recur(node_to_explore, p)
            if node_to_explore.is_labeled_negatively_with(p):
                children_nodes = node_to_explore.unwind_further()
                for child_node in children_nodes:
                    heappush(to_visit, child_node)
            else:
                _map_upward_from_node(node_to_explore, lambda current_node: current_node.add_positive_label(spec))
                continue

            #  self._add_may_edge_to(node_to_explore)

            abs_states_with_nodes = node.get_abstract_labels_in_tree()  # tuples of the form (abstract_label, node)
            abs_states_lead = filter(lambda abs_state: abs_state.is_negative_label(p), abs_states_with_nodes)
            while abs_states_lead:
                to_close = abs_states_lead[0]
                witness_state = self._abstract_structure.is_EE_closure(to_close, abs_states_with_nodes)
                if witness_state is True:
                    abs_states_lead = abs_states_lead[1:]
                    self._abstract_structure.add_must_hyper_transition(to_close, abs_states_with_nodes)
                else:
                    concretization_result = self._is_witness_concrete(to_close, witness_state)
                    if concretization_result:
                        to_close_node = to_close[1]
                        to_close_node.set_urgent()
                    else:
                        self.refine_abstract_label(to_close, witness_state)
                    break

            if not abs_states_lead:
                node.add_positive_label(spec)
                return True

        node.add_positive_label(spec)
        return True

        # update abstract data structures according to transitions

    def _handle_ev(self, node, spec, p, q):
        raise NotImplementedError()

    def _handle_ex(self, node, spec, operand):
        children_nodes = node.unwind_further()
        for child_node in children_nodes:
            res = self.handle_ctl(child_node, operand)
            if res:
                self._strengthen_transition_ex(node, child_node)
                return True

        self._strengthen_transition_ex(node, children_nodes)
        return False

    def find_abstract_classification_for_state(self, concrete_state):  ##goover
        kripke = self._kripke_structure
        abstract_state = self._abstraction.classify(concrete_state)
        if abstract_state is None:
            atomic_propositions = kripke.get_aps(concrete_state)
            abstract_state = AbstractState(atomic_propositions, kripke, kripke.get_formula_for_bis0(concrete_state))

            classification_leaf = self._abstraction.add_classification(atomic_propositions, abstract_state)
            abstract_state.set_classification_node(classification_leaf)

            self._abstract_structure.add_abstract_state(abstract_state)

        return abstract_state

    def find_abstract_classification_for_node(self, node):  ##govoer

        concrete_state = node.concrete_label
        abstract_classification = self.find_abstract_classification_for_state(concrete_state)
        node.set_abstract_label(abstract_classification)
        abstract_classification.get_classification_node().add_classifee(node)
        return abstract_classification

    def handle_ctl(self, state, specification):
        unwinding_tree = UnwindingTree(self._kripke_structure, None, [], state)
        self.find_abstract_classification_for_node(unwinding_tree)
        # TODO check or add to the collection of unwinding trees that are saved in this omg_checker as a member.
        return self._handle_ctl_and_recur(unwinding_tree, specification)

    def _handle_ctl_and_recur(self, node, specification):
        method_mapping = {'&': OmgModelChecker._handle_and,
                          '|': OmgModelChecker._handle_or,
                          '->': OmgModelChecker._handle_arrow,
                          '~': OmgModelChecker._handle_not,
                          'AV': OmgModelChecker._handle_av,
                          'EV': OmgModelChecker._handle_ev,
                          'EX': OmgModelChecker._handle_ex,
                          }
        if node.get_abstract_label().is_positive_label(specification):
            return True

        if node.get_abstract_label().is_negative_label(specification):
            return False

        if specification in [True, False]:
            return specification

        if specification.is_atomic_proposition():
            return self._handle_atomic_propositions(node, specification)

        main_connective = specification.get_main_connective()
        operands = specification.get_operands()

        return method_mapping[main_connective](self, node, specification, *operands)

    def _is_witness_concrete(self, to_close, witness_node):
        pass
    #  TODO fill holes

    def refine_abstract_label(self, to_close, witness_state):
        original_classification_leaf = to_close[0].get_classification_node()
        witness_abstract_state = self.find_abstract_classification_for_state(witness_state)
        new_abs_has_sons, new_abs_no_sons = self._abstract_structure.split_abstract_state(to_close,
                                                                                          witness_abstract_state)
        query = None  # TODO implement this
        query_labeling_mapper = {True: new_abs_has_sons, False: new_abs_no_sons}
        new_internal = original_classification_leaf.split(query, original_classification_leaf, query_labeling_mapper)

        new_abs_has_sons.set_classification_node(new_internal.get_successors()[True])
        new_abs_no_sons.set_classification_node(new_internal.get_successors()[False])

        # TODO implement reclassification logic. This is just the splitting.

    def _split_overapprox(self, src_node, dst_nodes):
        raise NotImplementedError()

    def _strengthen_transition_ex(self, src_node, dst_node):
        raise NotImplementedError()

    def _strengthen_trace(self, node_to_explore):  ##todo
        raise NotImplementedError()


def test_propositional_logic():
    kripke_structure = get_simple_kripke_structure()
    print kripke_structure
    ctl_parser = CtlParser()
    raw_specification = '(q & p) | (q -> p)'
    specification = ctl_parser.parse_omg(raw_specification)

    omg_model_checker = OmgModelChecker(kripke_structure)
    pos, neg = omg_model_checker.check_all_initial_states(specification)
    print 'M, s |= ' + specification.str_math() + 'for s in ' + str(pos)
    print 'M, s |/= ' + specification.str_math() + 'for s in ' + str(neg)


if __name__ == '__main__':
    print 'Welcome to the OMG model checker!'
    test_propositional_logic()

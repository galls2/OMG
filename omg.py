from heapdict import *

from abstract_structure import AbstractStructure, AbstractState
from abstraction_classifier import AbstractionClassifier
from unwinding_tree import UnwindingTree
from z3_utils import Z3Utils

DEBUG = True


def DEBUG_PRINT(txt, newline=True):
    if DEBUG:
        if newline:
            print txt
        else:
            print txt,


def unique(collection):
    return list(set(collection))


def node_to_heapq(node):
    return (0, node) if node.URGENT else (node.depth + 1, node)


def _label_state(check_result, node_to_label, spec):
    if check_result:
        node_to_label.add_positive_label(spec)
    else:
        node_to_label.add_negative_label(spec)
    return check_result


def _map_upward_from_node(node, mapper, stop):
    current = node
    while current is not stop:
        mapper(current)
        current = current.get_parent()


def label_subtree(node, spec, positivity):
    if not node.is_developed():
        return positivity

    if positivity:
        node.add_positive_label(spec)
    else:
        node.add_negative_label(spec)

    successors = node.get_successors()
    if successors is not None:
        for successor in successors:
            label_subtree(successor, spec, positivity)

    return positivity


def _init_heap_with(node):
    to_visit = heapdict()
    to_visit[node] = node.priority()
    return to_visit


class OmgModelChecker(object):
    """
    This is the main tool's class.
    Create a new one for each structure.
    """

    def __init__(self, kripke):
        super(OmgModelChecker, self).__init__()
        self._kripke = kripke
        self._abstract_structure = None
        self._abstraction = None
        self._initialize_abstraction()
        self._unwinding_trees = []
        self._method_mapping = {'&': OmgModelChecker._handle_and,
                                '|': OmgModelChecker._handle_or,
                                '->': OmgModelChecker._handle_arrow,
                                '~': OmgModelChecker._handle_not,
                                'AV': OmgModelChecker._handle_av,
                                'EV': OmgModelChecker._handle_ev,
                                'EX': OmgModelChecker._handle_ex,
                                }

    def _initialize_abstraction(self):
        self._abstract_structure = AbstractStructure(self._kripke)
        self._abstraction = AbstractionClassifier(self._kripke)

    def clean_intermediate_data(self):
        self._initialize_abstraction()
        self._unwinding_trees = []

    def check_all_initial_states(self, specification):
        positive_answer = []
        negative_answer = []
        for initial_state in self._kripke.get_initial_states():
            model_checking_result = self.handle_ctl(initial_state, specification)
            if model_checking_result:
                positive_answer.append(initial_state)
            else:
                negative_answer.append(initial_state)
        return positive_answer, negative_answer

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
        return not res

    def _handle_av(self, node, spec, p, q):

        to_visit = _init_heap_with(node)

        while to_visit:
            node_to_explore = (to_visit.popitem()[0]).reset_urgent()
            DEBUG_PRINT('AV:: NOW EXPLORING ' + node_to_explore.description())

            abstract_state = self._find_abstract_classification_for_node(node_to_explore)

            self._handle_ctl_and_recur(node_to_explore, q)
            if node_to_explore.is_labeled_negatively_with(q):
                self._strengthen_trace(node, node_to_explore)
                _map_upward_from_node(node_to_explore, lambda current_node: current_node.add_negative_label(spec),
                                      node.get_parent())
                DEBUG_PRINT('AV:: Returning FALSE for ' + node.description() +
                            ' due to finite trace to ' + node_to_explore.description())
                return False

            self._handle_ctl_and_recur(node_to_explore, p)
            if node_to_explore.is_labeled_negatively_with(p):
                children_nodes = node_to_explore.unwind_further()
                for child_node in children_nodes:
                    to_visit[child_node] = child_node.priority()
            else:
                node_to_explore.add_positive_label(spec)

            abs_states_with_nodes = node.get_abstract_labels_in_tree()  # tuples of the form (abstract_label, node)
            abs_states = unique([tup[0] for tup in abs_states_with_nodes])
            # TODO unify brothers
            abs_states_lead = [abs_tuple for abs_tuple in abs_states_with_nodes
                               if abs_tuple[1].is_labeled_negatively_with(p)]
            while abs_states_lead:
                abs_state_lead = abs_states_lead[0]
                to_close_abstract, to_close_node = abs_state_lead

                DEBUG_PRINT('AV:: Trying to close ' + to_close_node.description() + ' :', False)
                res = self._abstract_structure.is_EE_closure(to_close_abstract, abs_states)
                if res is True:
                    DEBUG_PRINT(' Success!')
                    abs_states_lead = abs_states_lead[1:]
                    self._abstract_structure.add_must_hyper(to_close_abstract, abs_states)  # GOOD?
                else:
                    src_to_witness, witness_state = res
                    DEBUG_PRINT(' Failed! Due to ' + str((src_to_witness, witness_state)))
                    concretization_result = self._is_witness_concrete(to_close_node, witness_state)
                    if concretization_result:
                        if to_close_node.get_successors() is None:
                            node_to_set = to_close_node
                        else:
                            node_to_set = [successor for successor in to_close_node.get_successors()
                                           if successor.concrete_label == concretization_result][0]

                        node_to_set.set_urgent()
                        to_visit[node_to_set] = node_to_set.priority()

                    else:
                        self._refine_split_ex(to_close_node, witness_state)
                    break

            if not abs_states_lead:
                DEBUG_PRINT('AV:: Found closure!')
                return label_subtree(node, spec, True)

        return label_subtree(node, spec, True)

    def _handle_ev(self, node, spec, p, q):
        to_visit = _init_heap_with(node)

        while to_visit:
            node_to_explore = (to_visit.popitem()[0]).reset_urgent()
            DEBUG_PRINT('EV:: NOW EXPLORING ' + node_to_explore.description())
            if node_to_explore.get_depth() >= 5:
                print 'HERH'

            self._find_abstract_classification_for_node(node_to_explore)

            self._handle_ctl_and_recur(node_to_explore, q)
            if node_to_explore.is_labeled_negatively_with(q):
                continue  # This is not the druid we're looking for

            self._handle_ctl_and_recur(node_to_explore, p)
            if node_to_explore.is_labeled_positively_with(p):
                self._strengthen_trace(node, node_to_explore)
                _map_upward_from_node(node_to_explore, lambda current_node: current_node.add_positive_label(spec),
                                      node.get_parent())
                DEBUG_PRINT(
                    'EV:: Found finite trace from ' + node.description() + ' to ' + node_to_explore.description())
                return True
            else:
                children_nodes = node_to_explore.unwind_further()
                for child_node in children_nodes:
                    to_visit[child_node] = child_node.priority()

            lasso_res = node_to_explore.is_lasso(node.get_parent())
            while lasso_res is not False:
                if lasso_res is True:
                    DEBUG_PRINT('EV:: Found concrete lasso to: ' + node_to_explore.description())
                    self._strengthen_trace(node, node_to_explore)
                    _map_upward_from_node(node_to_explore, lambda current_node: current_node.add_positive_label(spec),
                                          node.get_parent())
                    return True

                DEBUG_PRINT('EV:: STARTING ABSTRACT CLOSURE ATTEMPT')

                base, abstract_states_nodes_loop = lasso_res
                abstract_states_nodes_loop = list(abstract_states_nodes_loop)
                loop_abstract_states = [pair[0] for pair in abstract_states_nodes_loop]
                loop_nodes = [pair[1] for pair in abstract_states_nodes_loop]

                while abstract_states_nodes_loop:
                    (to_close_abs, to_close_node) = abstract_states_nodes_loop[0]
                    DEBUG_PRINT('EV:: Trying to close ' + to_close_node.description() + ' :', False)
                    res = self._abstract_structure.is_AE_closure(to_close_abs, loop_abstract_states)
                    if res is True:
                        DEBUG_PRINT(' Success!')
                        abstract_states_nodes_loop = abstract_states_nodes_loop[1:]
                    else:
                        DEBUG_PRINT(' Failed!')
                        self._refine_split_ax(to_close_node, loop_nodes)
                        break

                if not abstract_states_nodes_loop:
                    self._strengthen_trace(node, base)
                    _map_upward_from_node(node_to_explore, lambda current_node: current_node.add_positive_label(spec),
                                          node.get_parent())
                    DEBUG_PRINT('EV:: Found closure!')
                    return True

                lasso_res = node_to_explore.is_lasso(node.get_parent())

        DEBUG_PRINT('EV:: Pruned all paths from ' + node.description() + ': returning FALSE')
        return False

    def _handle_ex(self, node, spec, operand):
        children_nodes = node.unwind_further()
        for child_node in children_nodes:
            DEBUG_PRINT('EX:: NOW EXPLORING ' + child_node.description())
            res = self._handle_ctl_and_recur(child_node, operand)
            if res:
                DEBUG_PRINT('EX:: FOUND! ' + child_node.description() + ' is good!')
                self._refine_split_ex(node, child_node.concrete_label)
                return True
        DEBUG_PRINT('EX:: NO APPROPRIATE SUCCESSOR FOUND')
        self._refine_split_ax(node, children_nodes)
        return False

    def _find_abstract_classification_for_state(self, concrete_state):
        kripke = self._kripke
        abstract_state = self._abstraction.classify(concrete_state)
        if abstract_state is None:
            atomic_propositions = kripke.get_aps_for_state(concrete_state)
            bis0_formula = kripke.get_bis0_formula(concrete_state)
            abstract_state = AbstractState(atomic_propositions, kripke, bis0_formula)

            classification_leaf = self._abstraction.add_classification(atomic_propositions, abstract_state)
            abstract_state.set_classification_node(classification_leaf)

            self._abstract_structure.add_abstract_state(abstract_state)

        return abstract_state

    def _find_abstract_classification_for_node(self, node):
        concrete_state = node.concrete_label
        abstract_classification = self._find_abstract_classification_for_state(concrete_state)
        node.set_abstract_label(abstract_classification)
        '''
        abstract_classification.get_classification_node().add_classifee(concrete_state)
        '''
        return abstract_classification

    def handle_ctl(self, state, specification):
        unwinding_tree = UnwindingTree(self._kripke, None, None, state)
        # TODO check or add to the collection of unwinding trees that are saved in this omg_checker as a member.
        res = self._handle_ctl_and_recur(unwinding_tree, specification)
        DEBUG_PRINT(str(unwinding_tree))
        #      print str(self._abstraction)
        return res

    def _handle_ctl_and_recur(self, node, specification):

        DEBUG_PRINT(
            'handle_ctl_and_recur: node=(' + str(node.concrete_label) + ',' + str(node.get_depth()) + '), spec=' + \
            specification.str_math())

        if specification.get_main_connective() == 'EX':
            print 'upu'
        self._find_abstract_classification_for_node(node)

        if node.get_abstract_label().is_positive_label(specification):
            DEBUG_PRINT('Returning TRUE due to abstract label')
            return True

        if node.get_abstract_label().is_negative_label(specification):
            DEBUG_PRINT('Returning FALSE due to abstract label')
            return False

        if specification.is_boolean():
            return specification.get_bool_value()

        main_connective = specification.get_main_connective()
        operands = specification.get_operands()

        final_res = self._method_mapping[main_connective](self, node, specification, *operands)
        node.add_label(specification, final_res)
        return final_res

    def _is_witness_concrete(self, to_close, concrete_witness):
        abstract_witness = self._find_abstract_classification_for_state(concrete_witness)
        return Z3Utils.has_successor_in_abstract(to_close.concrete_label, abstract_witness)

    def _refine_split_next(self, src_node, witness_abstract_states, split_state_function, query_getter):

        abs_pos, abs_neg = split_state_function(src_node, witness_abstract_states)

        query_formula_wrapper = query_getter(witness_abstract_states, self._kripke.get_tr_formula())

        def query(concrete_state):
            return query_formula_wrapper.substitute(Z3Utils.int_vec_to_z3(concrete_state)).is_sat()

        query_labeling_mapper = {True: abs_pos, False: abs_neg}

        original_classification_leaf = src_node.get_abstract_label().get_classification_node()
        new_internal = self._abstraction.split(query, original_classification_leaf, query_labeling_mapper)

        abs_pos.set_classification_node(new_internal.get_successors()[True])
        abs_neg.set_classification_node(new_internal.get_successors()[False])

        # re-assign abs label
        src_node.get_abstract_label()

    def _refine_split_ex(self, node_src, witness_concrete_state):
        witness_abstract_state = self._find_abstract_classification_for_state(witness_concrete_state)

        self._refine_split_next(node_src, [witness_abstract_state], self._abstract_structure.split_abstract_state_ex,
                                Z3Utils.get_exists_successors_in_formula)

    def _refine_split_ax(self, src_node, dst_nodes):

        witness_abstract_states = [self._find_abstract_classification_for_node(dst) for dst in dst_nodes]

        self._refine_split_next(src_node, witness_abstract_states, self._abstract_structure.split_abstract_state_ax,
                                Z3Utils.get_forall_successors_in_formula)

    def _strengthen_trace(self, src, dst):
        while dst is not src:
            self._refine_split_ex(dst.get_parent(), dst.concrete_label)
            dst = dst.get_parent()

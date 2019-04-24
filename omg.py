import functools
import logging
from heapdict import *
from z3 import sat

from abstract_structure import AbstractStructure, AbstractState
from abstraction_classifier import AbstractionClassifier
from common import ConcretizationResult
from qbf_solver import Z3QbfSolver, CaqeQbfSolver, DepQbfSimpleSolver, QbfSolverSelector
from unwinding_tree import UnwindingTree
from z3_utils import Z3Utils

logger = logging.getLogger('OMG')


def _big_cup(list_of_sets):
    return functools.reduce(lambda x, y: x | y, list_of_sets)


def unique(collection):
    return list(set(collection))


def node_to_heapq(node):
    return (0, node) if node.URGENT else (node.depth + 1, node)


def _label_state(check_result, node_to_label, spec):
    node_to_label.add_label(spec, check_result)
    return check_result


def _map_upward(node, mapper, stop):
    current = node
    while current is not stop:
        mapper(current)
        current = current.get_parent()


def label_subtree(node, spec, positivity, goal):
    if not node.is_developed(goal):
        return positivity

    node.add_label(spec, positivity)

    successors = node.get_successors()
    [label_subtree(successor, spec, positivity, goal) for successor in (successors if successors is not None else [])]
    return positivity


def _init_heap_with(node):
    to_visit = heapdict()
    to_visit[node] = node.unwinding_priority()
    return to_visit


class Goal(object):
    def __init__(self, node, specification):
        self.node = node
        self.specification = specification

    def __str__(self):
        return '({node},{spec})'.format(node=self.node.description(), spec=self.specification.str_math())


class OmgBuilder(object):
    def __init__(self):
        super(OmgBuilder, self).__init__()
        self._kripke = None
        self._brother_unification = None
        self._trivial_split = None

    def set_kripke(self, kripke):
        self._kripke = kripke
        return self

    def set_brother_unification(self, val=True):
        self._brother_unification = val
        return self

    def set_trivial_split_elimination(self, val=True):
        self._trivial_split = val
        return self

    def build(self):
        if self._kripke is None:
            raise Exception('Cannot build OMG without Kripke structure!')
        if self._brother_unification is None:
            raise Exception('Cannot build OMG without deciding on a brother unification policy!')
        if self._trivial_split is None:
            raise Exception('Cannot build OMG without deciding on a trivial split elimination policy!')
        return OmgModelChecker(self._kripke, self._brother_unification, self._trivial_split)


class UnifPart(object):
    def __init__(self, cl_node, cn_nodes):
        self.cl_node = cl_node
        self.cn_nodes = cn_nodes


def get_next_to_av_close(abs_states_lead):  # (abs_label, nodes)
    def avg_depth(nodes_collection):
        return sum([node.get_depth() for node in nodes_collection]) / len(abs_states_lead)

    sorted_by_depth = {avg_depth(tup[1]): tup for tup in abs_states_lead}
    max_avg_depth = max(k for k in sorted_by_depth.keys())
    return sorted_by_depth[max_avg_depth]


class OmgModelChecker(object):
    """
    This is the main tool's class.
    Create a new one for each structure.
    """

    def __init__(self, kripke, brother_unification, trivial_split):
        super(OmgModelChecker, self).__init__()
        self._kripke = kripke
        self._trivial_split = trivial_split
        self._abs_structure = None
        self._abstraction = None
        self._initialize_abstraction()
        self._unwinding_trees = {}
        self._brother_unification = brother_unification
        self._method_mapping = {'&': OmgModelChecker._handle_and,
                                '|': OmgModelChecker._handle_or,
                                '->': OmgModelChecker._handle_arrow,
                                '~': OmgModelChecker._handle_not,
                                'AV': OmgModelChecker._handle_av,
                                'EV': OmgModelChecker._handle_ev,
                                'EX': OmgModelChecker._handle_ex,
                                }

    def _initialize_abstraction(self):
        self._abs_structure = AbstractStructure(self._kripke, self._trivial_split)
        self._abstraction = AbstractionClassifier(self._kripke)

    def clean_intermediate_data(self):
        self._initialize_abstraction()
        self._unwinding_trees = []

    def check_all_initial_states(self, specification):
        positive_answer = []
        negative_answer = []
        for initial_state in self._kripke.get_initial_states():
            #  self._kripke.get_graph(initial_state)
            model_checking_result = self.handle_ctl(initial_state, specification)
            if model_checking_result:
                positive_answer.append(initial_state)
            else:
                negative_answer.append(initial_state)
                break
        return positive_answer, negative_answer

    def _handle_and(self, node, spec, is_strengthen, left_op, right_op):
        return _label_state(
            self._handle_ctl_and_recur(node, left_op, is_strengthen) and self._handle_ctl_and_recur(node, right_op,
                                                                                                    is_strengthen),
            node, spec)

    def _handle_or(self, node, spec, is_strengthen, left_op, right_op):
        return _label_state(
            self._handle_ctl_and_recur(node, left_op, is_strengthen) or self._handle_ctl_and_recur(node,
                                                                                                   right_op,
                                                                                                   is_strengthen),
            node, spec)

    def _handle_arrow(self, node, spec, is_strengthen, left_op, right_op):
        return _label_state(
            (not self._handle_ctl_and_recur(node, left_op, is_strengthen)) or (
                self._handle_ctl_and_recur(node, right_op, is_strengthen)),
            node, spec)

    def _handle_not(self, node, spec, is_strengthen, operand):
        res = self._handle_ctl_and_recur(node, operand, is_strengthen)
        return not res

    def _handle_av(self, node, spec, is_strengthen, p, q):
        to_visit = _init_heap_with(node)
        visited = set()
        goal = Goal(node, spec)
        while to_visit:
            node_to_explore = (to_visit.popitem()[0]).reset_urgent()
            if node_to_explore.concrete_label in visited:
                continue
            visited.add(node_to_explore.concrete_label)
            # logger.debug('AV:: NOW EXPLORING ' + node_to_explore.description()+ ' FOR GOAL:: '+str(goal))
            #  logger.debug(str(node))

            abstract_state = self._find_abs_classification_for_node(node_to_explore)
            node_to_explore.set_developed(goal)

            self._handle_ctl_and_recur(node_to_explore, q)
            if node_to_explore.is_labeled_negatively_with(q):
                # logger.debug(str(goal) + ':: AV:: FALSE DUE TO TRACE' + node_to_explore.description())
                return self._handle_proving_trace(is_strengthen, node, node_to_explore, spec, to_return=False)

            self._handle_ctl_and_recur(node_to_explore, p)
            if node_to_explore.is_labeled_negatively_with(p):
                children_nodes = node_to_explore.unwind_further(visited)
                for child_node in children_nodes:
                    if child_node.concrete_label in visited:
                        continue
                    to_visit[child_node] = child_node.unwinding_priority()
            else:
                node_to_explore.add_positive_label(spec)

            inductive_res = self._check_inductive_av(goal, p, to_visit)
            if inductive_res:
                return label_subtree(node, spec, True, goal)

        if is_strengthen:
            self._strengthen_subtree(node, lambda _n: _n.is_developed(goal))
            return label_subtree(node, spec, True, goal)
        else:
            return True

    def _check_inductive_av(self, goal, p, to_visit):
        node = goal.node
        abs_states_with_nodes_b = node.get_abstract_labels_in_tree(goal)  # tuples of the form (abstract_label, node)
        if self._brother_unification:
            abs_states_with_nodes = self._unify_brothers(abs_states_with_nodes_b, p)
        else:
            abs_states_with_nodes = [(a, [n]) for (a, n) in abs_states_with_nodes_b]
        abs_states = unique([tup[0] for tup in abs_states_with_nodes])
        abs_states_lead = [abs_tuple for abs_tuple in abs_states_with_nodes
                           if abs_tuple[1][0].is_labeled_negatively_with(p)]
        while abs_states_lead:
            abs_state_lead = get_next_to_av_close(abs_states_lead)
            to_close_abstract, to_close_nodes = abs_state_lead

            # logger.debug('AV:: Trying to close '+ to_close_abstract.get_debug_name()+ ' FOR GOAL :'+str(goal))
            res = self._abs_structure.is_EE_closure(to_close_abstract, abs_states)
            if res is True:
                # logger.debug(' Success!')
                abs_states_lead.remove(abs_state_lead)
            else:
                src_to_witness, witness_state = res.conc_src, res.conc_dst

                # logger.debug(' Failed! Due to ' + str(src_to_witness) + ' to ' + str(witness_state))

                concretization_result = self._is_concrete_violation(to_close_nodes, witness_state)
                if concretization_result.exists():
                    witness_concrete_state = concretization_result.dst_conc
                    to_close_node = concretization_result.src_node
                    # logger.debug("CONC")

                    if to_close_node.get_successors() is None:
                        node_to_set = to_close_node
                    else:
                        node_to_set = next(successor for successor in to_close_node.get_successors()
                                           if successor.concrete_label == witness_concrete_state)

                    node_to_set.set_urgent()
                    to_visit[node_to_set] = node_to_set.unwinding_priority()

                else:

                    # logger.debug("REFINE")
                    abs_src_witness = self._find_abs_classification_for_state(src_to_witness)
                    to_close_node = next((_to for _to in to_close_nodes
                                          if _to.get_abstract_label() == abs_src_witness), None)

                    '''
                    if to_close_node is None:
                        print 'nodes: ' + str(len(to_close_nodes))
                        for _t in to_close_nodes:
                            print _t.description()
                        print str(src_to_witness)

                    
                    logger.debug(
                        'Splitting ' + abs_src_witness.get_classification_node().get_binary_string() + ' w.r.t. ' + \
                        self._find_abstract_classification_for_state(
                            witness_state).get_classification_node().get_binary_string())
                    '''
                    self._refine_split_ex(to_close_node, [witness_state], check_trivial=False,
                                          known_reclassification=False)
                return False
        return True

    def _is_concrete_violation(self, to_close_nodes, witness_state):

        abstract_witness = self._find_abs_classification_for_state(witness_state)
        res = Z3Utils.concrete_transition_to_abstract(to_close_nodes, abstract_witness)
        return ConcretizationResult() if res is False else ConcretizationResult(*res)

    def _handle_ev(self, node, spec, is_strengthen, p, q):
        to_visit = _init_heap_with(node)
        visited = set()
        goal = Goal(node, spec)

        while to_visit:
            node_to_explore = (to_visit.popitem()[0]).reset_urgent()

            # logger.debug('EV:: NOW EXPLORING ' + node_to_explore.description())
            self._find_abs_classification_for_node(node_to_explore)

            if node_to_explore.concrete_label in visited:
                lasso_res = node_to_explore.is_lasso(node.get_parent())
                if lasso_res is True:
                    return self._handle_proving_trace(is_strengthen, node, node_to_explore, spec, to_return=True)
                else:
                    continue

            node_to_explore.set_developed(goal)

            self._handle_ctl_and_recur(node_to_explore, q)
            if node_to_explore.is_labeled_negatively_with(q):
                continue  # This is not the druid we're looking for

            visited.add(node_to_explore.concrete_label)
            self._handle_ctl_and_recur(node_to_explore, p)
            if node_to_explore.is_labeled_positively_with(p):
                # logger.debug('EV:: PROVING trace from ' + node.description() + ' to ' + node_to_explore.description())
                return self._handle_proving_trace(is_strengthen, node, node_to_explore, spec,
                                                  to_return=True)
            else:
                children_nodes = node_to_explore.unwind_further()
                f_set_priority = to_visit.__setitem__
                [f_set_priority(child_node, child_node.unwinding_priority()) for child_node in children_nodes]

            inductive_res = self._check_inductive_ev(is_strengthen, node, node_to_explore, spec)
            if inductive_res:
                return True
        # logger.debug('EV:: Pruned all paths from ' + node.description() + ': returning FALSE')
        if is_strengthen:
            self._strengthen_subtree(node, lambda _n: _n.is_developed(goal))
            return label_subtree(node, spec, False, goal)
        else:
            return False

    def _check_inductive_ev(self, is_strengthen, node, node_to_explore, spec):
        lasso_res = node_to_explore.is_lasso(node.get_parent())
        if lasso_res is True:  # concrete lasso found! ## THIS GOES UP
            # logger.debug('EV:: Found concrete lasso to: ' + node_to_explore.description())
            return self._handle_proving_trace(is_strengthen, node, node_to_explore, spec, to_return=True)

        while lasso_res is not False:

            # logger.debug('EV:: STARTING ABSTRACT CLOSURE ATTEMPT')

            base, abstract_states_nodes_loop = lasso_res
            abstract_states_nodes_loop = list(abstract_states_nodes_loop)
            if self._brother_unification:
                abstract_states_nodes_loop = self._unify_brothers(abstract_states_nodes_loop, True)
            else:
                abstract_states_nodes_loop = [(a, [n]) for (a, n) in abstract_states_nodes_loop]

            loop_abstract_states = [tup[0] for tup in abstract_states_nodes_loop]
            loop_nodes = [_node for pair in abstract_states_nodes_loop for _node in pair[1]]

            while abstract_states_nodes_loop:
                to_close_abs, to_close_nodes = abstract_states_nodes_loop[0]
                # logger.debug('EV:: Trying to close abstract state of' + to_close_nodes[0].description() + ' :')
                res = self._abs_structure.is_AE_closure(to_close_abs, loop_abstract_states)
                if res is True:
                    # logger.debug(' Success!')
                    abstract_states_nodes_loop = abstract_states_nodes_loop[1:]
                else:
                    # logger.debug(' Failed!')
                    abs_src_witness = self._find_abs_classification_for_state(res)
                    to_close_node = next(_to for _to in to_close_nodes
                                         if _to.get_abstract_label() == abs_src_witness)

                    self._refine_split_ex(to_close_node, [_node.concrete_label for _node in loop_nodes],
                                          check_trivial=False,
                                          known_reclassification=False)
                    break

            if not abstract_states_nodes_loop:
                # logger.debug(' EV:: FOUND ABSTRACT CLOSURE!')

                if is_strengthen:
                    self._strengthen_trace(node, base)
                    _map_upward(node_to_explore, lambda curr: curr.add_positive_label(spec), node.get_parent())
                else:
                    _map_upward(node_to_explore, lambda curr: curr.add_positive_label(spec), base.get_parent())
                return True

            lasso_res = node_to_explore.is_lasso(node.get_parent())

        return False

    def _handle_proving_trace(self, is_strengthen, node, node_to_explore, spec, to_return):
        if is_strengthen:
            self._strengthen_trace(node, node_to_explore)
            _map_upward(node_to_explore, lambda curr: curr.add_label(spec, to_return), node.get_parent())
        return to_return

    def _handle_ex(self, node, spec, is_strengthen, operand):
        children_nodes = node.unwind_further()
        for child in children_nodes:
            # logger.debug('EX:: NOW EXPLORING ' + child_node.description())
            res = self._handle_ctl_and_recur(child, operand)
            if res:
                # logger.debug('EX:: FOUND! ' + child_node.description() + ' is good!')
                if is_strengthen:
                    self._refine_split_ex(node, [child.concrete_label], check_trivial=True, known_reclassification=True)
                return True
        # logger.debug('EX:: NO APPROPRIATE SUCCESSOR FOUND')
        if is_strengthen:
            self._refine_split_ax(node, children_nodes, check_trivial=True, known_reclassification=True)
        return False

    def __validate_abstract_classification(self, concrete_state, abstract_label):
        cl_node = abstract_label.get_classification_node()

        #      logger.debug("VALIDATING VALVAL")
        def is_papa(possible_dad):
            _l = abstract_label.get_classification_node()
            while _l is not None:
                if _l is possible_dad:
                    return True
                _l = _l.get_parent()
            return False

        while cl_node.get_parent() is not None:
            cl_node = cl_node.get_parent()

        to_visit = [cl_node]
        while to_visit:
            c_node = to_visit.pop(0)
            if c_node.get_successors() is not None:
                to_visit += c_node.get_successors().values()
            if is_papa(c_node):
                if not abstract_label.get_descriptive_formula().assign_state(concrete_state).is_sat():
                    assert False
            else:
                if c_node.get_value().get_descriptive_formula().assign_state(concrete_state).is_sat():
                    assert False

    def _find_abs_classification_for_state(self, concrete_state):
        kripke = self._kripke
        abstract_state = self._abstraction.classify(concrete_state)
        if abstract_state is None:
            atomic_propositions = concrete_state.get_sat_aps()
            bis0_formula = concrete_state.get_bis0_formula()
            abstract_state = AbstractState(atomic_propositions, kripke, bis0_formula)

            classification_leaf = self._abstraction.add_classification(atomic_propositions, abstract_state)
            abstract_state.set_classification_node(classification_leaf)

            self._abs_structure.add_abstract_state(abstract_state)

        #   self.__validate_abstract_classification(concrete_state, abstract_state)
        return abstract_state

    def _find_abs_classification_for_node(self, node):

        concrete_state = node.concrete_label
        abstract_classification = self._find_abs_classification_for_state(concrete_state)
        node.set_abstract_label(abstract_classification)
        return abstract_classification

    def handle_ctl(self, state, specification):
        if state in self._unwinding_trees.keys():
            unwinding_tree = self._unwinding_trees[state]
        else:
            unwinding_tree = UnwindingTree(self._kripke, None, None, state)
        unwinding_tree.reset_developed_in_tree()

        res = self._handle_ctl_and_recur(unwinding_tree, specification, False)
        # logger.debug(str(unwinding_tree))
        # self.get_abstract_trees_sizes()
        self._unwinding_trees[state] = unwinding_tree

        return res

    def _handle_ctl_and_recur(self, node, specification, is_strengthen=True):

        # logger.debug( 'handle_ctl_and_recur: node=(' + str(node.concrete_label) + ',' + str(node.get_depth()) + '), spec=' + specification.str_math())

        self._find_abs_classification_for_node(node)

        if node.get_abstract_label().is_positive_label(specification):
            # logger.debug('Returning TRUE due to abstract label')
            return True

        if node.get_abstract_label().is_negative_label(specification):
            # logger.debug('Returning FALSE due to abstract label')
            return False

        if specification.is_boolean():
            return specification.get_bool_value()

        main_connective = specification.get_main_connective()
        operands = specification.get_operands()

        final_res = self._method_mapping[main_connective](self, node, specification, is_strengthen, *operands)
        if is_strengthen:
            node.add_label(specification, final_res)

        return final_res

    def _refine_split_next(self, src_node, witness_abstract_states, split_state_function, query_getter, check_trivial,
                           known_reclassification):

        res = split_state_function(src_node, witness_abstract_states, check_trivial)
        if res[0] is not None:
            return

        abs_pos, abs_neg = res[1]
        query_formula_wrapper = query_getter(witness_abstract_states, self._kripke.get_tr_formula())

        def query(concrete_state):
            return (QbfSolverSelector.QbfSolverCtor if not query_formula_wrapper.is_prop() else Z3QbfSolver)().solve(
                query_formula_wrapper.assign_state(concrete_state))[0] == sat

        query_labeling_mapper = {True: abs_pos, False: abs_neg}

        original_classification_leaf = src_node.get_abstract_label().get_classification_node()
        new_internal = self._abstraction.split(query, original_classification_leaf, query_labeling_mapper,
                                               '#'.join([_abs.get_debug_name() for _abs in witness_abstract_states]))

        abs_pos.set_classification_node(new_internal.get_successors()[True])
        abs_neg.set_classification_node(new_internal.get_successors()[False])

        # re-assign abs label
        if known_reclassification is None:
            src_node.get_abstract_label()
        elif known_reclassification is True:
            src_node.set_abstract_label(abs_pos)
        elif known_reclassification is False:
            src_node.set_abstract_label(abs_neg)

    def _refine_split_ex(self, node_src, dst_states, check_trivial, known_reclassification=None):
        dst_abs_states = [self._find_abs_classification_for_state(dst) for dst in dst_states]
        #    logger.debug('EX SPLIT:: '+self._find_abs_classification_for_node(node_src).get_debug_name() + ' by ['+','.join([_d.get_debug_name() for _d in dst_abs_states])+']')

        if self._abs_structure.is_known_E_must_between(node_src.get_abstract_label(), dst_abs_states):
            #       logger.debug('SPLIT AVERTED DUE TO KNOWN E_MUST')
            return
        self._refine_split_next(node_src, dst_abs_states, self._abs_structure.split_abstract_state_ex,
                                Z3Utils.get_exists_successors_in_formula, check_trivial, known_reclassification)

        # p = self._find_abs_classification_for_node(node_src).get_classification_node().get_parent()
        # if p is not None:
        #     logger.debug('SPLIT PRODUCTS: [FALSE]: {} [True]: {}'.format(p.get_successors()[False].get_value().get_debug_name(), p.get_successors()[True].get_value().get_debug_name()))
        # else:
        #     logger.debug('NO SPLIT WAS DONE')

    def _refine_split_ax(self, src_node, dst_nodes, check_trivial, known_reclassification=None):
        dst_abs_states = unique([dst.get_abstract_label() for dst in dst_nodes])

        if self._abs_structure.is_known_may_over_between(src_node.get_abstract_label(), dst_abs_states):
            return
        self._refine_split_next(src_node, dst_abs_states, self._abs_structure.split_abstract_state_ax,
                                Z3Utils.get_forall_successors_in_formula, check_trivial, known_reclassification)

    def _strengthen_trace(self, src, dst):
        dsts = []
        while dst is not src:
            dsts += [dst.concrete_label]
            self._refine_split_ex(dst.get_parent(), dsts, check_trivial=True, known_reclassification=True)
            dst = dst.get_parent()

    def _strengthen_subtree(self, src_node, stop_condition):
        if stop_condition(src_node):
            return {src_node}

        successors = src_node.unwind_further()
        child_sets = [self._strengthen_subtree(successor, stop_condition).add(successor) for successor in successors]
        all_kids = _big_cup(child_sets)
        self._refine_split_ax(src_node, all_kids, check_trivial=True, known_reclassification=True)

    def _unify_brothers(self, abs_states_with_nodes, agree_upon):  # of the form (abs, node)
        abstract_states, concrete_nodes = zip(*abs_states_with_nodes)
        cl_nodes = {abs_state.get_classification_node() for abs_state in abstract_states}
        cn_to_cl = {tup[1]: tup[0].get_classification_node() for tup in abs_states_with_nodes}
        depths = {cl_node.get_depth() for cl_node in cl_nodes}
        with_depth = {depth:  # d-> {(cl_node, {conc_nodes})}
                          tuple([UnifPart(cl, [cn for cn in cn_to_cl.keys() if cn_to_cl[cn] == cl]) for cl in
                                 cl_nodes if cl.get_depth() == depth]) for depth in depths}

        to_return = []
        while with_depth.keys():
            max_depth = max(with_depth.keys())
            bottom_layer = list(with_depth.pop(max_depth))
            if max_depth > 0:
                unchanged, next_level = self._unify_same_level_brothers(bottom_layer, agree_upon)

                to_return += unchanged
                if next_level:
                    next_depth = max_depth - 1
                    if next_depth not in with_depth.keys():
                        with_depth[next_depth] = []
                    with_depth[next_depth] += tuple(next_level)
            else:
                to_return += bottom_layer
        res = [(unif.cl_node.get_value(), unif.cn_nodes) for unif in to_return]

        # logger.debug('BROTHER UNIFICATION:: reduced from ' + str(len(abs_states_with_nodes)) + ' to ' + str(len(res))  if len(res) < len(abs_states_with_nodes) else '')
        return res

    def _unify_same_level_brothers(self, bottom_layer, agree_upon):  # set of (classification_node,
        # {concrete_nodes that are classified by it})

        def agree(b1, b2):
            abs1 = b1.cl_node.get_value()
            abs2 = b2.cl_node.get_value()
            return (abs1.is_positive_label(agree_upon) and abs2.is_positive_label(agree_upon)) or (
                    abs1.is_negative_label(agree_upon) and abs2.is_negative_label(agree_upon)) or (
                       (not abs1.is_labeled(agree_upon) and not abs2.is_labeled(agree_upon))
                   )

        parent_mapping = {u_part.cl_node.get_parent():
                              tuple([u_brother for u_brother in bottom_layer if
                                     u_brother.cl_node.get_parent() == u_part.cl_node.get_parent() and agree(u_brother,
                                                                                                             u_part)])
                          for u_part in bottom_layer}

        unif_brothers = [list(tup_val) for tup_val in parent_mapping.values()]
        unchanged = [l[0] for l in unif_brothers if len(l) == 1]
        to_unify = [UnifPart(u_part[0].cl_node.get_parent(), [cn_node for uf in u_part for cn_node in uf.cn_nodes])
                    for u_part in unif_brothers if len(u_part) == 2]

        return unchanged, to_unify

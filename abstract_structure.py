import logging

from common import abstract_states_to_int, subset_abs, in_abs, add_elems_to_abs, remove_elems
from formula_wrapper import FormulaWrapper, unsat, QBF
from qbf_solver import DepQbfSimpleSolver, Z3QbfSolver
from var_manager import VarManager
from z3_utils import Z3Utils, Solver, And, Not, Bool, Implies
from z3 import *

logger = logging.getLogger('OMG')


def init_dict_by_key(d, key, val):
    if key not in d.keys():
        d[key] = {val}
    else:
        d[key].add(val)
    return d


def exists_superset_for_key(_dict, key, superset_of):
    if key not in _dict.keys():
        return False
    val = abstract_states_to_int(superset_of)
    return any([subset_abs(val, _e) for _e in _dict[key]])


class AbstractState(object):
    def __init__(self, atomic_labels, kripke, formula):
        super(AbstractState, self).__init__()
        self._kripke = kripke

        self.positive_labels = set(atomic_labels)
        self.negative_labels = set(self._kripke.get_aps()) - self.positive_labels

        self.atomic_labels = atomic_labels
        self._classification_node = None
        self._id = VarManager.new_abs_name()
        self._formula = formula

    def get_id(self):
        return self._id

    def get_debug_name(self):
        return 'A' + str(self._id)

    def get_descriptive_formula(self):
        return self._formula

    def add_positive_labels(self, labels):
        self.positive_labels |= labels
        return self

    def add_negative_labels(self, labels):
        self.negative_labels |= labels
        return self

    def is_positive_label(self, label):
        return label in self.positive_labels

    def is_negative_label(self, label):
        return label in self.negative_labels

    def is_labeled(self, label):
        return label in self.negative_labels or label in self.positive_labels

    def get_input_vector(self):
        return self.get_descriptive_formula().get_input_vectors()[0]

    def update_classification(self, concrete_state):
        if self._classification_node.is_leaf():
            return self._classification_node.get_value()

        classification_node = self.get_classification_node()
        classifier = classification_node.get_classifier()
        new_classification = classifier.update_classification(classification_node, concrete_state)
        return new_classification

    def get_classification_node(self):
        return self._classification_node

    def set_classification_node(self, classification_leaf):
        self._classification_node = classification_leaf
        return self

    def get_kripke(self):
        return self._kripke

    def get_split_string(self):
        return self._classification_node.get_split_string()


class AbstractStructure(object):
    """docstring for AbstractStructure."""

    def __init__(self, kripke, trivial_split):
        super(AbstractStructure, self).__init__()
        self.kripke = kripke
        self._abstract_states = set()
        self._NE_may = {}
        self._E_may_over = {}
        self._NE_may_over = {}
        self._E_must = {}  # if in may over approx than also in must !!!!!!!!!!
        self._trivial_split = trivial_split

    def add_abstract_state(self, abstract_state):
        self._abstract_states.add(abstract_state)
        return self

    def add_must_hyper(self, src, abs_states):
        val = abstract_states_to_int(abs_states)
        init_dict_by_key(self._E_must, src, val)
        return self

    def add_NE_may(self, src, abs_state):
        init_dict_by_key(self._NE_may, src, abs_state.get_id())
        return self

    def add_E_may_over(self, src, abs_states):
        val = abstract_states_to_int(abs_states)
        init_dict_by_key(self._E_may_over, src, val)
        return self

    def add_NE_may_over(self, src, _dst):
        val = abstract_states_to_int(_dst[1])
        if src in self._NE_may_over.keys():  # tuple of (violation, non-closers)
            self._NE_may_over[src] = {ent for ent in self._NE_may_over[src] if not subset_abs(ent[1], val)}
        init_dict_by_key(self._NE_may_over, src, (_dst[0], val))
        return self

    def is_EE_closure(self, to_close, close_with):
        if to_close in self._NE_may:
            close_with = [cl for cl in close_with if cl.get_id() not in self._NE_may[to_close]]

        def exists_subset(_n_over):
            if to_close not in _n_over.keys():
                return False
            candidates = (op[0] for op in _n_over[to_close] if
                          subset_abs(c_idx, op[1]) and op[0] is not None)
            return next(candidates, False)

        c_idx = abstract_states_to_int(close_with)
        if to_close in self._E_may_over.keys() and any([subset_abs(c, c_idx) for c in self._E_may_over[to_close]]):
            return True

        subset_res = exists_subset(self._NE_may_over)
        if subset_res:
            return subset_res

        closure_result = Z3Utils.is_EE_closed(to_close, close_with)

        if closure_result is True:
            self.add_E_may_over(to_close, close_with)
        else:
            self.add_NE_may_over(to_close, (closure_result, close_with))

        return closure_result

    def is_known_E_must_between(self, src, dsts):
        return exists_superset_for_key(self._E_must, src, dsts) or exists_superset_for_key(self._E_may_over, src, dsts)

    def is_known_may_over_between(self, src, dsts):
        return exists_superset_for_key(self._E_may_over, src, dsts)

    def is_AE_closure(self, to_close, close_with):
        if to_close in self._NE_may:
            close_with = [cl for cl in close_with if cl.get_id() not in self._NE_may[to_close]]

        if self.is_known_E_must_between(to_close, close_with):
            return True

        closure_result = Z3Utils.is_AE_closed(to_close, close_with)

        if closure_result is True:
            self.add_must_hyper(to_close, close_with)

        return closure_result

    def split_abstract_state(self, node_to_close, abstract_sons, formula_getter, check_trivial_split):
        kripke = self.kripke
        abs_to_close = node_to_close.get_abstract_label()
        pos_formula, neg_formula, (base, pos_op) = \
            formula_getter(abs_to_close, abstract_sons, kripke.get_tr_formula())

        if self._trivial_split and check_trivial_split:  #######HERE AND Z3UTILS
            solver = DepQbfSimpleSolver()
            res, _ = solver.solve(pos_formula.get_qbf())
            if res == unsat:
                logger.debug('TSE applied!')
                return False, abs_to_close
            res, _ = solver.solve(neg_formula.get_qbf())
            if res == unsat:
                logger.debug('TSE applied!')
                return True, abs_to_close
            '''
            flags = {f_name: Bool(f_name) for f_name in ['Y', 'N']}
            neg_op = pos_op.negate()
            inner = And(base.get_qbf().get_prop(),
                        Or(Not(flags['Y']), pos_op.get_qbf().get_prop()),
                        Or(Not(flags['N']), neg_op.get_qbf().get_prop()))
            q_list = base.get_qbf().get_q_list() + pos_op.get_qbf().get_q_list()
            f = FormulaWrapper(QBF(inner, q_list), pos_formula.get_var_vectors(), pos_formula.get_input_vectors())
            res = solver.incremental_solve_flags(f, flags.values(), stop_res=unsat)
            if res:
                idx_empty, _ = res
                if idx_empty is 0:
                    logger.debug('TSE applied!')
                    return False, abs_to_close
                if idx_empty is 1:
                    logger.debug('TSE applied!')
                    return True, abs_to_close
            '''

        def create_abs_state(formula):
            return AbstractState(abs_to_close.atomic_labels, kripke, formula) \
                .add_positive_labels(abs_to_close.positive_labels) \
                .add_negative_labels(abs_to_close.negative_labels)

        abs_pos, abs_neg = create_abs_state(pos_formula), create_abs_state(neg_formula)

        self._abstract_states = (self._abstract_states - {abs_to_close}) | {abs_pos, abs_neg}

        def replace_old_values_dst(d):
            d.update(
                {k: {add_elems_to_abs([abs_pos, abs_neg] if in_abs(abs_to_close, _n) else [], _n) for _n in v} for k, v
                 in d.items()})
            '''dct.update({key: dct[key]
                       .union([abs_pos, abs_neg])
                        for key in dct.keys()
                        if abs_to_close in dct[key]})
            '''

        def replace_old_value(dct):
            # from
            if abs_to_close in dct.keys():
                old_dst = dct[abs_to_close]
                dct.update({abs_pos: old_dst, abs_neg: old_dst})
            # to
            replace_old_values_dst(dct)

        replace_old_value(self._E_must)
        replace_old_value(self._E_may_over)

        replace_old_values_dst(self._NE_may)
        _ne = self._NE_may_over
        _ne.update({k: {(op[0], add_elems_to_abs([abs_pos, abs_neg], op[1]) if in_abs(abs_to_close, op[1]) else op[1])
                        for op in v}
                    for k, v in _ne.items()})

        return None, (abs_pos, abs_neg)

    def split_abstract_state_ex(self, node_to_close, abs_sons, check_trivial):
        abs_to_split = node_to_close.get_abstract_label()

        res = self.split_abstract_state(node_to_close, abs_sons, Z3Utils.get_ex_split_formulas, check_trivial)

        if res[0] is not None:
            if res[0] is True:
                self.add_must_hyper(abs_to_split, abs_sons)
            else:
                [self.add_NE_may(abs_to_split, abs_son) for abs_son in abs_sons]
            return res[0], abs_to_split

        new_abs_has_sons, new_abs_no_sons = res[1]
        # split info

        updated_abstract_sons = set(abs_sons) if abs_to_split not in abs_sons else \
            (set(abs_sons) - {abs_to_split}) | {new_abs_has_sons, new_abs_no_sons}

        self.add_must_hyper(new_abs_has_sons, updated_abstract_sons)

        [self.add_NE_may(new_abs_no_sons, abs_son) for abs_son in updated_abstract_sons]

        if new_abs_no_sons in self._E_may_over.keys():
            self._E_may_over[new_abs_no_sons] = {remove_elems(updated_abstract_sons, _cl)
                                                 for _cl in self._E_may_over[new_abs_no_sons]}
        if new_abs_no_sons in self._E_must.keys():
            self._E_must[new_abs_no_sons] = {remove_elems(updated_abstract_sons, _cl)
                                             for _cl in self._E_must[new_abs_no_sons]}
        return None, (new_abs_has_sons, new_abs_no_sons)

    def split_abstract_state_ax(self, node_to_close, abs_sons, check_trivial):
        abs_to_split = node_to_close.get_abstract_label()
        res = self.split_abstract_state(node_to_close, abs_sons, Z3Utils.get_ax_split_formulas, check_trivial)

        if res[0] is not None:
            if res[0] is True:
                self.add_E_may_over(abs_to_split, abs_sons)
            else:
                self.add_NE_may_over(abs_to_split, (None, abs_sons))
            return res[0], abs_to_split

        new_abs_sons_closed, new_abs_sons_not_closed = res[1]

        # split info

        updated_abstract_sons = set(abs_sons) if abs_to_split not in abs_sons else \
            (set(abs_sons) - {abs_to_split}) | {new_abs_sons_closed, new_abs_sons_not_closed}

        self.add_E_may_over(new_abs_sons_closed, updated_abstract_sons)
        self.add_NE_may_over(new_abs_sons_not_closed, (None, updated_abstract_sons))

        return None, (new_abs_sons_closed, new_abs_sons_not_closed)

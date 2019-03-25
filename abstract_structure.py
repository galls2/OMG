import logging

from abstraction_classifier import collection_to_sorted_tuple
from formula_wrapper import FormulaWrapper, unsat
from z3_utils import Z3Utils, Solver, And, Not, Bool, Implies

logger = logging.getLogger('OMG')


def init_dict_by_key(dict, key, default_val):
    if key not in dict.keys():
        dict[key] = {collection_to_sorted_tuple(default_val)}
    else:
        dict[key].add(collection_to_sorted_tuple(default_val))
    return dict


class AbstractState(object):
    def __init__(self, atomic_labels, kripke, formula):
        super(AbstractState, self).__init__()
        self._kripke = kripke

        self.positive_labels = set(atomic_labels)
        self.negative_labels = set(self._kripke.get_aps()) - self.positive_labels

        self.atomic_labels = atomic_labels
        self._classification_node = None

        self._formula = formula

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

    def add_must_hyper(self, src, hyper_dst):
        init_dict_by_key(self._E_must, src, hyper_dst)
        return self

    def add_NE_may(self, src, dst):
        init_dict_by_key(self._NE_may, src, [dst])
        return self

    def add_E_may_over(self, src, dst):
        init_dict_by_key(self._E_may_over, src, dst)
        return self

    def add_NE_may_over(self, src, dst):
        if src in self._NE_may_over.keys():  # tuple of (violation, non-closers)
            self._NE_may_over[src] = {ent for ent in self._NE_may_over[src] if not set(ent[1]).issubset(set(dst[1]))}
        init_dict_by_key(self._NE_may_over, src, dst)  ###MINIMZE
        return self

    def is_EE_closure(self, to_close, close_with):
        #     print len(close_with)
        close_with = [cl for cl in close_with if
                      to_close not in self._NE_may.keys() or cl not in self._NE_may[to_close]]

        # this is not empty
        #    print len(close_with)
        def exists_superset(over_approxs):
            return True if to_close in over_approxs.keys() and \
                           any([set(close_with).issuperset(set(op)) for op in over_approxs[to_close]]) else None

        def exists_subset(n_over_approxs):
            if to_close not in n_over_approxs.keys():
                return False
            candidates = [op[0]
                          for op in n_over_approxs[to_close] if
                          set(close_with).issubset(set(op[1])) and op[0] is not None]
            return candidates[0] if candidates else False

        if exists_superset(self._E_may_over) is True:
            return True

        subset_res = exists_subset(self._NE_may_over)
        if subset_res:
            return subset_res

        #  logger.debug('Z3ing')
        closure_result = Z3Utils.is_EE_closed(to_close, close_with)

        if closure_result is True:
            self.add_E_may_over(to_close, close_with)
        else:
            self.add_NE_may_over(to_close, (closure_result, tuple(close_with)))

        return closure_result

    def is_known_E_must_between(self, src, dsts):
        def exists_superset(over_approxs):
            return True if src in over_approxs.keys() and \
                           any([set(dsts).issuperset(set(op)) for op in over_approxs[src]]) else None

        return exists_superset(self._E_must) is True or exists_superset(self._E_may_over) is True

    def is_known_may_over_between(self, src, dsts):
        def exists_superset(over_approxs):
            return True if src in over_approxs.keys() and \
                           any([set(dsts).issuperset(set(op)) for op in over_approxs[src]]) else None

        return exists_superset(self._E_may_over)

    def is_AE_closure(self, to_close, close_with):
        close_with = [cl for cl in close_with if
                      to_close not in self._NE_may.keys() or cl not in self._NE_may[to_close]]

        # this is not empty

        if self.is_known_E_must_between(to_close, close_with):
            return True

        closure_result = Z3Utils.is_AE_closed(to_close, close_with)

        if closure_result is True:
            self.add_must_hyper(to_close, close_with)
        else:
            [self.add_NE_may(to_close, closer) for closer in close_with]

        return closure_result

    def split_abstract_state(self, node_to_close, abstract_sons, formula_getter, check_trivial_split):
        kripke = self.kripke
        abs_to_close = node_to_close.get_abstract_label()
        base_formula, quantified_part, vars = \
            formula_getter(abs_to_close, abstract_sons, kripke.get_tr_formula())

        if self._trivial_split and check_trivial_split:
            s = Solver()
            s.add(base_formula)
            Y_flag, N_flag = Bool('Y'), Bool('N')
            s.add(Implies(Y_flag, quantified_part))
            s.add(Implies(N_flag, Not(quantified_part)))
            if s.check(Y_flag) == unsat:
                return False, abs_to_close
            if s.check(N_flag) == unsat:
                return True, abs_to_close

        pos_formula = FormulaWrapper(And(base_formula, quantified_part), [vars])
        neg_formula = FormulaWrapper(And(base_formula, Not(quantified_part)), [vars])

        def create_abstract_state_split(formula):
            return AbstractState(abs_to_close.atomic_labels, kripke, formula) \
                .add_positive_labels(abs_to_close.positive_labels) \
                .add_negative_labels(abs_to_close.negative_labels)

        abs_pos = create_abstract_state_split(pos_formula)
        abs_neg = create_abstract_state_split(neg_formula)

        self._abstract_states.remove(abs_to_close)
        self._abstract_states.update([abs_pos, abs_neg])

        def replace_old_values_dst(dct):
            dct.update({key: dct[key]
                       .union([abs_pos, abs_neg])
                        for key in dct.keys()
                        if abs_to_close in dct[key]})

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
        ne_may_over = self._NE_may_over
        ne_may_over.update({key:
                                tuple({(n_cl_opt[0], n_cl_opt[1] if abs_to_close not in n_cl_opt[1] else
                                tuple(set(n_cl_opt[1]) | {abs_pos, abs_neg})) for n_cl_opt in
                                       ne_may_over[key]})
                            for key in ne_may_over.keys()})

        return None, (abs_pos, abs_neg)

    def split_abstract_state_ex(self, node_to_close, abstract_sons, check_trivial):
        abstract_state_to_split = node_to_close.get_abstract_label()

        res = self.split_abstract_state(node_to_close, abstract_sons, Z3Utils.get_ex_split_formulas, check_trivial)

        if res[0] is not None:
            if res[0] is True:
                self.add_must_hyper(abstract_state_to_split, abstract_sons)
            else:
                self.add_NE_may(abstract_state_to_split, abstract_sons)
            return res[0], abstract_state_to_split

        new_abs_has_sons, new_abs_no_sons = res[1]
        # split info

        updated_abstract_sons = abstract_sons if abstract_state_to_split not in abstract_sons else \
            ([a for a in abstract_sons if a != abstract_state_to_split] + [new_abs_has_sons,
                                                                           new_abs_no_sons])

        self.add_must_hyper(new_abs_has_sons, updated_abstract_sons)

        for abs_son in updated_abstract_sons:
            self.add_NE_may(new_abs_no_sons, abs_son)

        if new_abs_no_sons in self._E_may_over.keys():
            self._E_may_over[new_abs_no_sons] = tuple([set(closers).difference(set(updated_abstract_sons))
                                                       for closers in self._E_may_over[new_abs_no_sons]])
        if new_abs_no_sons in self._E_must.keys():
            self._E_must[new_abs_no_sons] = tuple([set(closers).difference(set(updated_abstract_sons))
                                                       for closers in self._E_must[new_abs_no_sons]])
        return None, (new_abs_has_sons, new_abs_no_sons)

    def split_abstract_state_ax(self, node_to_close, abstract_sons, check_trivial):
        abstract_state_to_split = node_to_close.get_abstract_label()
        res = self.split_abstract_state(node_to_close, abstract_sons, Z3Utils.get_ax_split_formulas, check_trivial)

        if res[0] is not None:
            if res[0] is True:
                self.add_E_may_over(abstract_state_to_split, abstract_sons)
            else:
                self.add_NE_may_over(abstract_state_to_split, (None, abstract_sons))
            return res[0], abstract_state_to_split

        new_abs_sons_closed, new_abs_sons_not_closed = res[1]

        # split info

        updated_abstract_sons = tuple(abstract_sons if abstract_state_to_split not in abstract_sons else \
                                          ([a for a in abstract_sons if a != abstract_state_to_split] + [
                                              new_abs_sons_closed,
                                              new_abs_sons_not_closed]))

        self.add_E_may_over(new_abs_sons_closed, updated_abstract_sons)
        self.add_NE_may_over(new_abs_sons_not_closed, (None, updated_abstract_sons))

        return None, (new_abs_sons_closed, new_abs_sons_not_closed)

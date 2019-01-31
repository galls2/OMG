from abstraction_classifier import collection_to_sorted_tuple
from z3_utils import Z3Utils


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

    def __init__(self, kripke):
        super(AbstractStructure, self).__init__()
        self.kripke = kripke
        self._abstract_states = set()
        self._E_may = {}
        self._NE_may = {}
        self._E_may_over_approx = {}
        self._NE_may_over_approx = {}
        self._E_must = {}  # if in may over approx than also in must !!!!!!!!!!
        self._NE_must = {}

    def add_abstract_state(self, abstract_state):
        self._abstract_states.add(abstract_state)
        return self

    '''
    def add_may(self, src, dst):
        init_dict_by_key(self._E_may, src, dst)
        return self
    '''

    def add_must_hyper(self, src, hyper_dst):
        init_dict_by_key(self._E_must, src, hyper_dst)
        return self

    def is_EE_closure(self, to_close, close_with):

        def exists_superset(over_approxs):
            return True if to_close in over_approxs.keys() and \
                           any([set(close_with).issuperset(set(op)) for op in over_approxs[to_close]]) else None

        if exists_superset(self._E_may_over_approx) is True:
            return True

        closure_result = Z3Utils.is_EE_closed(to_close, close_with)

        conclusion_dict = self._E_may_over_approx if closure_result is True else self._NE_may_over_approx
        init_dict_by_key(conclusion_dict, to_close, close_with)

        return closure_result

    def is_AE_closure(self, to_close, close_with):
        def exists_superset(over_approxs):
            return True if to_close in over_approxs.keys() and \
                           any([set(close_with).issuperset(set(op)) for op in over_approxs[to_close]]) else None

        if exists_superset(self._E_must) is True:
            return True

        closure_result = Z3Utils.is_AE_closed(to_close, close_with)

        conclusion_dict = self._E_must if closure_result is True else self._NE_must
        init_dict_by_key(conclusion_dict, to_close, close_with)

        return closure_result

    def split_abstract_state(self, node_to_close, abstract_sons, formula_getter):
        kripke = self.kripke
        abs_to_close = node_to_close.get_abstract_label()
        pos_formula, neg_formula = \
            formula_getter(abs_to_close, abstract_sons, kripke.get_tr_formula())

        def create_abstract_state_split(formula):
            return AbstractState(abs_to_close.atomic_labels, kripke, formula) \
                .add_positive_labels(abs_to_close.positive_labels) \
                .add_negative_labels(abs_to_close.negative_labels)

        abs_pos = create_abstract_state_split(pos_formula)
        abs_neg = create_abstract_state_split(neg_formula)

        self._abstract_states.remove(abs_to_close)
        self._abstract_states.update([abs_pos, abs_neg])

        # may
        #       self._E_may = {k: self._E_may[k] for k in self._E_may.keys() if abs_to_close not in [k, self._E_may[k]]}

        # must-from

        if abs_to_close in self._E_must.keys():
            old_dst = self._E_must.pop(abs_to_close)
            self._E_must.update({abs_pos: old_dst, abs_neg: old_dst})

        self._NE_must.pop(abs_to_close, None)

        # must-to
        def replace_old_value(dct):
            dct.update({key: dict[key]
                       .difference(abs_to_close)
                       .union([abs_pos, abs_neg])
                        for key in dct.keys()
                        if abs_to_close in dct[key]})

        replace_old_value(self._E_must)
        replace_old_value(self._NE_must)

        return abs_pos, abs_neg

    def split_abstract_state_ex(self, node_to_close, abstract_sons):
        abstract_state_to_split = node_to_close.get_abstract_label()

        new_abs_has_sons, new_abs_no_sons = self.split_abstract_state(node_to_close, abstract_sons,
                                                                      Z3Utils.get_ex_split_formulas)
        # split info

        updated_abstract_sons = abstract_sons if abstract_state_to_split not in abstract_sons else \
            ([a for a in abstract_sons if a != abstract_state_to_split] + [new_abs_has_sons,
                                                                           new_abs_no_sons])

        self._E_must = init_dict_by_key(self._E_must, new_abs_has_sons, updated_abstract_sons)
        self._NE_may = init_dict_by_key(self._NE_may, new_abs_no_sons, updated_abstract_sons)

        return new_abs_has_sons, new_abs_no_sons

    def split_abstract_state_ax(self, node_to_close, abstract_sons):
        abstract_state_to_split = node_to_close.get_abstract_label()
        new_abs_sons_closed, new_abs_sons_not_closed = self.split_abstract_state(node_to_close, abstract_sons,
                                                                                 Z3Utils.get_ax_split_formulas)
        # split info

        updated_abstract_sons = abstract_sons if abstract_state_to_split not in abstract_sons else \
            ([a for a in abstract_sons if a != abstract_state_to_split] + [new_abs_sons_closed,
                                                                           new_abs_sons_not_closed])
        self._E_may_over_approx = init_dict_by_key(
            self._E_may_over_approx, new_abs_sons_closed, updated_abstract_sons)

        self._NE_may_over_approx = init_dict_by_key(
            self._NE_may_over_approx, new_abs_sons_not_closed, updated_abstract_sons)

        return new_abs_sons_closed, new_abs_sons_not_closed

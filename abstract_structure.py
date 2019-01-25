from abstraction_classifier import _collection_to_sorted_tuple
from z3_utils import Z3Utils


def init_dict_by_key(dict, key, default_val):
    if key not in dict.keys():
        dict[key] = {_collection_to_sorted_tuple(default_val)}
    else:
        dict[key].add(_collection_to_sorted_tuple(default_val))
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
        #  self._existing_may_transitions = {}
        self._NE_may = {}
        self._E_may_over_approx = {}
        self._NE_may_over_approx = {}
        self._E_must = {}
        self._NE_must = {}

    def add_abstract_state(self, abstract_state):
        self._abstract_states.add(abstract_state)
        return self

    '''
    def add_may_transition(self, src, dst):
        if src not in self._existing_may_transitions.keys():
            self._existing_may_transitions[src] = set()
        self._existing_may_transitions[src].add(dst)
    '''

    def add_must_hyper_transition(self, src, hyper_dst):
        if src not in self._E_must.keys():
            self._E_must[src] = set()
        self._E_must[src].add(hyper_dst)
        return self

    def is_EE_closure(self, to_close, close_with):

        def exists_subset(over_approxs, conclusion):
            return conclusion if to_close in over_approxs.keys() and \
                    any([close_with.issubset(op) for op in over_approxs[to_close]]) else None

        if exists_subset(self._E_may_over_approx, True) is True:
            return True
        if exists_subset(self._NE_may_over_approx, False) is False:
            return False

        return Z3Utils.is_EE_closed(to_close, close_with)


    def split_abstract_state(self, node_to_close, abstract_sons, formula_getter):
        kripke = self.kripke
        abs_to_close = node_to_close.get_abstract_label()
        pos_formula, neg_formula = \
            formula_getter(abs_to_close, abstract_sons, kripke.get_tr_formula())

        abs_pos = AbstractState(abs_to_close.atomic_labels, kripke, pos_formula) \
            .add_positive_labels(abs_to_close.positive_labels) \
            .add_negative_labels(abs_to_close.negative_labels)

        abs_neg = AbstractState(abs_to_close.atomic_labels, kripke, neg_formula) \
            .add_positive_labels(abs_to_close.positive_labels) \
            .add_negative_labels(abs_to_close.negative_labels)

        self._abstract_states.remove(abs_to_close)
        self._abstract_states.update([abs_pos, abs_neg])

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

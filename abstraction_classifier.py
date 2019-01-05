def ap_collection_to_ap_tuple(ap_collection):
    ap_list = list(ap_collection)
    ap_tuple = tuple(sorted(ap_list))
    return ap_tuple


class AbstractionClassifier(object):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke_structure):
        super(AbstractionClassifier, self).__init__()
        self._kripke_structure = kripke_structure
        self._abstract_classification_trees = {}
        self._cache = {}

    def classify(self, concrete_state):
        if concrete_state in self._cache.keys():
            return self._cache[concrete_state]

        concrete_labels = ap_collection_to_ap_tuple(self._kripke_structure.get_labels(concrete_state))
        if concrete_labels not in self._abstract_classification_trees.keys():
            return None
        abstract_label = self._abstract_classification_trees[concrete_labels].classify(concrete_state)
        self._cache[concrete_state] = abstract_label
        return abstract_label

    def add_classification_tree(self, atomic_labels, classification_tree):
        assert atomic_labels not in self._abstract_classification_trees.keys()
        ap_tuple = ap_collection_to_ap_tuple(atomic_labels)
        self._abstract_classification_trees[ap_tuple] = classification_tree
        return classification_tree

    def is_exists_tree_for_atomic_labels(self, atomic_labels):
        return ap_collection_to_ap_tuple(atomic_labels) in self._abstract_classification_trees.keys()

    def _update_cache(self, abstract_state_to_remove):
        cache = self._cache
        self._cache = {key: cache[key] for key in cache.keys() if cache[key] != abstract_state_to_remove}


class AbstractionClassifierTree(object):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke_structure, abstract_classifier):
        super(AbstractionClassifierTree, self).__init__()
        self._kripke_structure = kripke_structure
        self._abstract_classifier = abstract_classifier

    def classify(self, concrete_state):
        raise NotImplementedError()

    def is_leaf(self):
        raise NotImplementedError()


class AbstractionClassifierInternal(AbstractionClassifierTree):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke_structure, query, successors):
        super(AbstractionClassifierInternal, self).__init__(kripke_structure)
        self._query = query
        self._successors = successors

    def classify(self, concrete_state):
        return self._successors[self._query(concrete_state)].classify(concrete_state)

    def is_leaf(self):
        return False

    def replace_successor(self, old_successor, new_successor):
        self._successors.update({key: new_successor for key in self._successors \
                                 if self._successors[key] == old_successor})


class AbstractionClassifierLeaf(AbstractionClassifierTree):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke_structure, value, parent, abstract_classifier):
        super(AbstractionClassifierLeaf, self).__init__(kripke_structure)
        self._value = value
        self._parent = parent
        self._classifees = set()  # Elements that are classified
        self._abstract_classifier = abstract_classifier

    def add_classifee(self, classifee):
        self._classifees.add(classifee)

    def classify(self, concrete_state):
        return self._value

    def split(self, query, successors):
        parent = self._parent
        new_classification_node = AbstractionClassifierInternal(self._kripke_structure, query, successors)
        parent.replace_successor(self, new_classification_node)

        self._abstract_classifier.update_cache(self)

    def is_leaf(self):
        return True

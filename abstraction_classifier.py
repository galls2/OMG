def _ap_collection_to_ap_tuple(ap_collection):
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

    def update_classification(self, classification_node, concrete_state):
        new_abstract_label = classification_node.classify(concrete_state)
        new_classification_node = new_abstract_label.get_classification_node()

        classification_node.remove_classifee(concrete_state)
        new_classification_node.add_classifee(concrete_state)

        self._update_cache(classification_node.get_value())
        return new_abstract_label

    def classify(self, concrete_state):
        if concrete_state in self._cache.keys():
            return self._cache[concrete_state]

        concrete_labels = _ap_collection_to_ap_tuple(self._kripke_structure.get_labels(concrete_state))
        if concrete_labels not in self._abstract_classification_trees.keys():
            return None
        abstract_label = self._abstract_classification_trees[concrete_labels].classify(concrete_state)
        self._cache[concrete_state] = abstract_label
        return abstract_label

    def add_classification(self, atomic_labels, abstract_state):
        assert atomic_labels not in self._abstract_classification_trees.keys()
        ap_tuple = _ap_collection_to_ap_tuple(atomic_labels)
        classification_tree = AbstractionClassifierTree(self._kripke_structure, None, None, self, abstract_state)
        self._abstract_classification_trees[ap_tuple] = classification_tree
        return classification_tree

    def is_exists_tree_for_atomic_labels(self, atomic_labels):
        return _ap_collection_to_ap_tuple(atomic_labels) in self._abstract_classification_trees.keys()

    def _update_cache(self, abstract_state_to_remove):
        cache = self._cache
        self._cache = {key: cache[key] for key in cache.keys() if cache[key] != abstract_state_to_remove}
        return self

    def split(self, query, classification_node_to_split, query_labeling_mapper):

        classification_node_to_split._query = query

        successors = {}
        for query_result in query_labeling_mapper.keys():
            new_leaf = AbstractionClassifierTree(self._kripke_structure, None, None,
                                                 self, query_labeling_mapper[query_result])
            successors[query_result] = new_leaf

        new_internal = classification_node_to_split.split(query, successors)
        for successor in new_internal.get_successors():
            successor.set_parent(new_internal)

        self._update_cache(classification_node_to_split.get_value())
        return new_internal


class AbstractionClassifierTree(object):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke_structure, query, successors, parent, classifier, value=None):
        super(AbstractionClassifierTree, self).__init__()
        self._kripke_structure = kripke_structure
        self._query = query
        self._successors = successors
        self._value = value
        self._parent = parent
        self._classifees = set()  # Elements that are classified
        self._classifier = classifier

    def classify(self, concrete_state):
        if self.is_leaf():
            self._value.set_classification_node(self)
            return self._value

        classification = self._successors[self._query(concrete_state)].classify(concrete_state)
        return classification

    def is_leaf(self):
        return not len(self._successors)

    def get_value(self):
        return self._value

    def get_parent(self):
        return self._parent

    def set_parent(self, parent):
        self._parent = parent
        return self

    def get_successors(self):
        return self._successors

    def get_classifees(self):
        return self._classifees

    def add_classifee(self, node):
        self._classifees.add(node)
        return self

    def remove_classifee(self, classifee):
        self._classifees.remove(classifee)
        return self

    def _split(self, query, successors):
        if not self.is_leaf():
            raise Exception('Cannot split non-leaf')

        parent = self._parent
        new_internal = AbstractionClassifierTree(self._kripke_structure, query, successors, parent, self._classifier)
        if parent is not None:
            parent.get_successors().update({k: new_internal
                                            for k in parent.get_successors().keys()
                                            if parent.get_successors()[k] == self})
        return new_internal

    def get_classifier(self):
        return self._classifier

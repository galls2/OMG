class AbstractionClassifier(object):
    """docstring for AbstractionClassifier."""
    def __init__(self, kripke_structure):
        super(AbstractionClassifier, self).__init__()
        self._kripke_structure = kripke_structure

    def classify(self, concrete_state):
        raise NotImplementedError()

    def is_leaf(self):
        raise NotImplementedError()


class AbstractionClassifierInternal(AbstractionClassifier):
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


class AbstractionClassifierLeaf(AbstractionClassifier):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke_structure, value, parent):
        super(AbstractionClassifierLeaf, self).__init__(kripke_structure)
        self._value = value
        self._parent = parent
        self._classifees = [] # Elements that are classified

    def add_classifee(self, classifee):
        self._classifees.append(classifee)

    def classify(self, concrete_state):
        return self._value

    def split(self, query, successors):
        parent = self._parent
        new_classification_node = AbstractionClassifierInternal(self._kripke_structure, query, successors)
        parent.replace_successor(self, new_classification_node)

    def is_leaf(self):
        return True

import functools


class UnwindingTree(object):
    def __init__(self, kripke_structure, parent, successors, concrete_label, abstract_label=None):
        super(UnwindingTree, self).__init__()
        self._kripke_structure = kripke_structure
        self._parent = parent
        self._successors = successors
        self.concrete_label = concrete_label  # concrete state that is represented by this node
        self.abstract_label = abstract_label  # abstract state that is represented by this node
        self.depth = 0 if parent is None else parent.get_depth()
        self.URGENT = False

    def unwind_further(self):
        if self._successors is None:
            concrete_successors = self._kripke_structure.get_successors(self.concrete_label)
            successor_nodes = [UnwindingTree(self._kripke_structure, self, [], concrete_successor, None) \
                               for concrete_successor in concrete_successors]
            self._successors = successor_nodes
            return successor_nodes

    def is_abstract_lasso(self):
        current = self._parent
        abstract_labels = {self.abstract_label}
        while current is not None:
            if current._abstract_label == self.abstract_label:
                return True, current, abstract_labels
            abstract_labels.add(current._abstract_label)
            current = current._parent
        return False

    def get_abstract_labels_in_tree(self):
        partial_abstract_labels = [self.abstract_label] + [successor.get_abstract_labels_in_tree() for successor in
                                                           self._successors]
        abs_labels = functools.reduce(lambda x, y: x | y, partial_abstract_labels)
        return abs_labels

    def get_depth(self):
        return self.depth

    def set_urgent(self):
        self.URGENT = True

    def is_labeled_positively_with(self, label):
        return self.abstract_label.is_positive_label(label)

    def is_labeled_negatively_with(self, label):
        return self.abstract_label.is_negative_label(label)

    def add_positive_label(self, label):
        self.abstract_label.add_positive_label(label)

    def add_negative_label(self, label):
        self.abstract_label.add_negative_label(label)

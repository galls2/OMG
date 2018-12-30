class UnwindingTree(object):
    def __init__(self, kripke_structure, parent, successors, concrete_label, abstract_label):
        super(UnwindingTree, self).__init__()
        self._kripke_structure = kripke_structure
        self._parent = parent
        self._successors = successors
        self._concrete_label = concrete_label
        self._abstract_label = abstract_label

    def unwind_further(self):
        concrete_successors = self._kripke_structure.get_successors(self._concrete_label)
        self._successors = [UnwindingTree(self._kripke_structure, self, [], concrete_successor, None) for concrete_successor in concrete_successors]

    def is_abstract_lasso(self):
        current = self._parent
        abstract_labels = {self._abstract_label}
        while current is not None:
            if current._abstract_label == self._abstract_label:
                return True, current, abstract_labels
            abstract_labels.add(current._abstract_label)
            current = current._parent
        return False

    def get_abstract_labels_in_tree(self):
        abs_labelings = {self._abstract_label}
        successors_labelings = [successor.get_abstract_labels_in_tree() for successor in self._successors]
        for successor_labelings in successors_labelings:
            abs_labelings |= successor_labelings
        return abs_labelings

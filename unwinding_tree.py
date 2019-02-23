import functools

'''
Due to the fact that we agreed that for all proper subformulas of the original specification, we must keep the 
invariant that when finished check s|=f, it follows that either [s] |= f or [s] |= ~f, we do not make a STATE class. 
'''

'''
Moreover, as of the fact that we have to recognize loops, we remain with a tree form. 
'''


def print_tree(node, successors_function, printer_function, depth=0):
    ret = "\t" * depth + printer_function(node) + "\n"
    succ = successors_function(node)
    if succ is None:
        succ = []
    for child in succ:
        ret += print_tree(child, successors_function, printer_function, depth + 1)
    return ret


class UnwindingTree(object):
    def __init__(self, kripke, parent, successors, concrete_label, abstract_label=None):
        super(UnwindingTree, self).__init__()
        self._kripke = kripke
        self._parent = parent
        self._successors = successors
        self.concrete_label = concrete_label  # concrete state that is represented by this node
        self._abstract_label = abstract_label  # abstract state that is represented by this node
        self.depth = 0 if parent is None else parent.get_depth() + 1
        self.URGENT = False
        self._developed = set()

    def unwind_further(self):
        if self._successors is None:
            concrete_successors = self._kripke.get_successors(self.concrete_label)
            self._successors = [UnwindingTree(self._kripke, self, None, concrete_successor)
                                for concrete_successor in concrete_successors]

        return self._successors

    def get_successors(self):
        return self._successors

    def is_developed(self, goal):
        return goal in self._developed

    def set_developed(self, goal):
        self._developed.add(goal)
        return self

    def _get_developed(self):
        return self._developed

    def reset_developed_in_tree(self):
        self._developed.clear()
        successors = [] if self._successors is None else self._successors
        [s.reset_developed_in_tree() for s in successors]
        return self

    def is_lasso(self, stop_node):
        current = self._parent
        head_abstract_label = self.get_abstract_label()
        abstract_states_and_nodes = {(head_abstract_label, self)}
        head_concrete_label = self.concrete_label
        while current is not stop_node:
            current_concrete_label = current.concrete_label
            if current_concrete_label == head_concrete_label:
                return True
            current_abstract_label = current.get_abstract_label()
            if current_abstract_label == head_abstract_label:
                return current, abstract_states_and_nodes

            abstract_states_and_nodes.add((current_abstract_label, current))
            current = current.get_parent()
        return False

    def get_abstract_labels_in_tree(self, goal):
        if not self.is_developed(goal):
            return set()
        successors = [] if self._successors is None else self._successors
        partial_abstract_labels = [{(self.get_abstract_label(), self)}] + [successor.get_abstract_labels_in_tree(goal)
                                                                           for successor in successors]
        abs_labels = functools.reduce(lambda x, y: x | y, partial_abstract_labels)
        return abs_labels

    def get_depth(self):
        return self.depth

    def set_urgent(self):
        self.URGENT = True
        return self

    def reset_urgent(self):
        self.URGENT = False
        return self

    def is_labeled_positively_with(self, label):
        if label.is_boolean():
            return label.get_bool_value()
        return self.get_abstract_label().is_positive_label(label)

    def is_labeled_negatively_with(self, label):
        if label.is_boolean():
            return not label.get_bool_value()
        return self.get_abstract_label().is_negative_label(label)

    def add_positive_label(self, label):
        self.get_abstract_label().add_positive_labels({label})
        return self

    def get_abstract_label(self):
        known_abstract_state = self._abstract_label
        current_abstract_state = known_abstract_state.update_classification(self.concrete_label)
        self._abstract_label = current_abstract_state
        return current_abstract_state

    def add_negative_label(self, label):
        self.get_abstract_label().add_negative_labels({label})
        return self

    def add_label(self, label, polarity):
        if polarity:
            self.add_positive_label(label)
        else:
            self.add_negative_label(label)
        return self

    def set_abstract_label(self, abstract_label):
        self._abstract_label = abstract_label
        return self

    def get_parent(self):
        return self._parent

    def __lt__(self, other):
        if self.URGENT and not other.URGENT:
            return True
        if not self.URGENT and other.URGENT:
            return False
        return self.depth < other.depth

    def __cmp__(self, other):
        return self < other

    def description(self):
        return str(tuple(self.concrete_label))+','+str(self.depth)

    def __str__(self):
        return print_tree(self, lambda node: [] if node.get_successors() is None else node.get_successors(),
                          lambda node: str(node.concrete_label) if len(node._get_developed()) > 0
                          else str(tuple(node.concrete_label)))

    def priority(self):
        return 0 if self.URGENT else self.depth+1

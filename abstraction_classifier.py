import functools

from ctl import CtlFileParser
from kripke_structure import AigKripkeStructure
from unwinding_tree import print_tree
import inspect


def collection_to_sorted_tuple(ap_collection):
    ap_list = list(ap_collection)
    ap_tuple = tuple(sorted(ap_list))
    return ap_tuple


class AbstractionCache(object):

    def __init__(self):
        super(AbstractionCache, self).__init__()
        self._data = {}

    def exists_key(self, key):
        return key in self._data.keys()

    def __getitem__(self, item):
        return self._data[item]

    def __setitem__(self, key, value):
        self._data[key] = value
        return self

    def remove_by_value(self, value):
        self._data = {k: self._data[k] for k in self._data.keys() if self._data[k] != value}
        return self

class AbstractionClassifier(object):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke, cache=True):
        super(AbstractionClassifier, self).__init__()
        self._kripke = kripke
        self._classification_trees = {}
        self._cache = AbstractionCache()

    def update_classification(self, classification_node, concrete_state):
        new_abstract_label = classification_node.classify(concrete_state)
        '''
        new_classification_node = new_abstract_label.get_classification_node()
    
        
        classification_node.remove_classifee(concrete_state)
        new_classification_node.add_classifee(concrete_state)
        '''
        self._update_cache(classification_node.get_value())
        return new_abstract_label

    def classify(self, concrete_state):
        if self._cache.exists_key(tuple(concrete_state)):
            return self._cache[tuple(concrete_state)]

        concrete_atomic_labels = collection_to_sorted_tuple(self._kripke.get_aps_for_state(concrete_state))
        if concrete_atomic_labels not in self._classification_trees.keys():
            return None

        abstract_label = self._classification_trees[concrete_atomic_labels].classify(concrete_state)
        self._cache[tuple(concrete_state)] = abstract_label
        return abstract_label

    def add_classification(self, atomic_labels, abstract_state):
        assert atomic_labels not in self._classification_trees.keys()
        ap_tuple = collection_to_sorted_tuple(atomic_labels)
        classification_tree = AbstractionClassifierTree(self._kripke, None, dict(), None, self, abstract_state)
        self._classification_trees[ap_tuple] = classification_tree
        return classification_tree

    def is_exists_tree_for_atomic_labels(self, atomic_labels):
        return collection_to_sorted_tuple(atomic_labels) in self._classification_trees.keys()

    def _update_cache(self, abstract_state_to_remove):
        self._cache.remove_by_value(abstract_state_to_remove)
        return self

    def split(self, query, classification_node_to_split, query_labeling_mapper):

        successors = dict()
        for query_result in query_labeling_mapper.keys():
            new_leaf = AbstractionClassifierTree(self._kripke, None, dict(), classification_node_to_split,
                                                 self, query_labeling_mapper[query_result])
            successors[query_result] = new_leaf

        classification_node_to_split.split(query, successors)

        self._update_cache(classification_node_to_split.get_value())
        return classification_node_to_split

    def __str__(self):
        ret = ''
        for bis0 in self._classification_trees.keys():
            ret += 'Tree for APs: ' + str([ap.str_math() for ap in bis0]) + '\n'
            ret += '-------------\n'
            ret += print_tree(self._classification_trees[bis0],
                              lambda n: [] if n.get_successors() is None else n.get_successors().values(),
                              lambda l: inspect.getsource(l.get_query()) if not l.is_leaf() else
                              str(l.get_value().get_descriptive_formula().get_z3_formula()))
        return ret


class AbstractionClassifierTree(object):
    """docstring for AbstractionClassifier."""

    def __init__(self, kripke, query, successors, parent, classifier, value=None):
        super(AbstractionClassifierTree, self).__init__()
        self._kripke = kripke
        self._query = query
        self._successors = successors
        self._value = value
        self._parent = parent
        #    self._classifees = set()  # Elements that are classified
        self._classifier = classifier

    def classify(self, concrete_state):
        if self.is_leaf():
            self._value.set_classification_node(self)
            return self._value

        classification = self._successors[self._query(concrete_state)].classify(concrete_state)
        return classification

    def is_leaf(self):
        return not self._successors

    def get_value(self):
        return self._value

    def get_parent(self):
        return self._parent

    def set_parent(self, parent):
        self._parent = parent
        return self

    def get_successors(self):
        return self._successors

    '''
    def get_classifees(self):
        return self._classifees

    def add_classifee(self, node):
        self._classifees.add(tuple(node))
        return self

    def remove_classifee(self, classifee):
        self._classifees.discard(tuple(classifee))
        return self
    '''

    def split(self, query, successors):
        if not self.is_leaf():
            raise Exception('Cannot split non-leaf')

        self._query = query
        self._successors = successors

        return self

    def get_classifier(self):
        return self._classifier

    def get_query(self):
        return self._query

    def size(self):
        return 1 + sum([s.size() for s in self._successors.values()])


def test_cache_usage(ctl_path, aig_path):
    ctl_chunks = CtlFileParser().parse_ctl_file(ctl_path)
    # print ctl_chunks
    aps = functools.reduce(lambda x, y: x | y,
                           [set(ctl_formula.get_aps()) for chunk in ctl_chunks for ctl_formula in
                            chunk[1:]])
    kripke_structure = AigKripkeStructure(aig_path, aps)
    classifier = AbstractionClassifier(kripke_structure)


if __name__ == '__main__':
    aig_file_paths = ['iimc_aigs/af_ag.aig']
    ctl_formula_paths = ['iimc_aigs/af_ag_checkEV.ctl']

    test_cache_usage(ctl_formula_paths[0], aig_file_paths[0])

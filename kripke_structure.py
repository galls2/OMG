from aig_parser import PythonAigParser
from z3_utils import Z3Utils
# import networkx as nx
# import matplotlib.pyplot as plt


class KripkeStructure(object):
    def __init__(self, aps):
        super(KripkeStructure, self).__init__()
        self._aps = aps

    def get_aps(self):
        return self._aps

    def get_initial_states(self):
        raise NotImplementedError()

    def get_tr_formula(self):
        raise NotImplementedError()

    def get_var_vector(self):
        raise NotImplementedError()


class AigKripkeStructure(KripkeStructure):
    def __init__(self, aig_path, aps):
        super(AigKripkeStructure, self).__init__(aps)
        self._aig_parser = PythonAigParser(aig_path)
        self._num_latches = self._aig_parser.get_num_latches()

        self._tr, initial_states_gen, self._output_formula = self._aig_parser.get_tr_and_initial(self)
        self._input_vars = self._tr.get_input_vectors()[0]
        self._initial_states = initial_states_gen
  #      self._initial_states = list(initial_states_gen)

        self._ap_conversion = self._aig_parser.get_ap_mapping()
        self._known_successors = {}

    def get_output_formula(self):
        return self._output_formula

    def get_tr_formula(self):
        return self._tr

    def get_input_var_vector(self):
        return self._input_vars

    def get_var_vector(self):
        return self._tr.get_var_vectors()[0]

    def get_successors(self, state):
   #     return Z3Utils.get_all_successors(self._tr, state)

        if state in self._known_successors.keys():
            return list(self._known_successors[state])
        res = Z3Utils.get_all_successors(self._tr, state)
        self._known_successors[state] = tuple(res)
        return res


    def get_initial_states(self):
        return self._initial_states

    def get_var_num_for_ap(self, ap):
        ap_symb = self._ap_conversion[ap.get_ap_text()]
        var_num = int(ap_symb[1:]) + (self._num_latches if ap_symb[0] == 'o' else 0)
        return var_num

    # DEBUGGING
    def get_graph(self, src_state):
        edges = {}
        to_explore = {src_state}
        while to_explore:
            next_state = to_explore.pop()
            if next_state in edges.keys() or next_state in to_explore:
                continue
            successors = self.get_successors(next_state)
            edges[next_state] = successors

            print str(next_state) + '-> ' + ','.join([str(dst) for dst in edges[next_state]])

            to_explore |= set(successors)




        # G = nx.DiGraph()
        # for state in edges.keys():
        #     G.add_node(state, name=str(state))
        # G.add_edges_from([(v, u) for v in edges.keys() for u in edges[v]])
        #
        # nx.draw(G)
        # nx.draw_networkx_labels(G, pos = nx.shell_layout(G))
        # plt.savefig('fig.png')

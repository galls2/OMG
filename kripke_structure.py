from aig_parser import AvyAigParser, PythonAigParser
from z3_utils import Z3Utils


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
    def __init__(self, aig_path, aps, qe_policy):
        super(AigKripkeStructure, self).__init__(aps)
        self._qe_policy = qe_policy
        self._aig_parser = PythonAigParser(aig_path)
        self._num_latches = self._aig_parser.get_num_latches()

        self._tr, initial_states_gen = self._aig_parser.get_tr_and_initial(qe_policy, self)
        self._initial_states = list(initial_states_gen)
        self._ap_conversion = self._aig_parser.get_ap_mapping()

    def get_qe_policy(self):
        return self._qe_policy

    def get_tr_formula(self):
        return self._tr

    def get_var_vector(self):
        return self._tr.get_var_vectors()[0]

    def get_successors(self, state):
        return Z3Utils.get_all_successors(self._tr, state)

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
            to_explore |= set(successors)

        for s in edges.keys():
            print str(s) + '-> ' + ','.join([str(dst) for dst in edges[s]])

import itertools

from aig_parser import AvyAigParser
from cnf_parser import CnfParser
from common import time_me
from state import State
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
        self._aig_parser = AvyAigParser(aig_path)
        self._initial_states = None
        self._init_latch_values = self._get_initial_latch_values()

        self._overwrite_aig_reset_logic()

        parse_results = self._aig_parser.parse()
        self._num_latches = self._aig_parser.get_num_latches()
        self._cnf_parser = CnfParser(self._num_latches, qe_policy)
        self._tr = self._connect_aigs(parse_results)
        self._ap_conversion = self._aig_parser.get_ap_mapping()

    def get_qe_policy(self):
        return self._qe_policy

    def get_tr_formula(self):
        return self._tr

    def get_var_vector(self):
        return self._tr.get_var_vectors()[0]

    def _overwrite_aig_reset_logic(self):
        new_aig_lines = self._aig_parser.get_aig_after_reset()
        old_aig_path = self._aig_parser.get_aig_path()
        new_aig_path = '.'.join(old_aig_path.split('.')[:-1]) + '_reset.' + old_aig_path.split('.')[-1]
        with open(new_aig_path, 'w') as new_aig:
            new_aig.write(''.join(new_aig_lines))

        self._aig_parser = AvyAigParser(new_aig_path)

    def _get_initial_latch_values(self):
        return self._aig_parser.get_initial_latch_values()

    def get_successors(self, state):
        return Z3Utils.get_all_successors(self.get_tr_formula(), state)

    def get_initial_states(self):
        if self._initial_states is not None:
            return self._initial_states

        inits_latches = [list(init) for init in self._init_latch_values]

        def get_outputs_for_latch_values(l_vals):
            return itertools.product(*[out_val_list \
                                       for out_formula in self._output_formulas

                                       for out_val_list in Z3Utils.all_sat(out_formula.assign_int_vec(l_vals))])

        res = (State.from_int_list(i_latch + list(comb), self.get_var_vector(), self) for i_latch in inits_latches for
               comb in
               get_outputs_for_latch_values(i_latch))

        self._initial_states = res
        return res

    def get_var_num_for_ap(self, ap):
        ap_symb = self._ap_conversion[ap.get_ap_text()]
        var_num = int(ap_symb[1:]) + (self._aig_parser.get_num_latches() if ap_symb[0] == 'o' else 0)
        return var_num

    def _connect_aigs(self, parse_results):
        ltr_metadata, ltr_dimacs = parse_results[0]

        self._ltr_formula = self._cnf_parser.dimacs_to_z3(ltr_metadata, ltr_dimacs, self._cnf_parser.parse_metadata_tr)
        self._output_formulas = \
            [self._cnf_parser.dimacs_to_z3(output_metadata, output_dimacs, self._cnf_parser.parse_metadata_bad)
             for (output_metadata, output_dimacs) in parse_results[1:]]

        max_var_ltr = int(ltr_dimacs[0].split()[-1])
        return Z3Utils.combine_ltr_with_bad_formulas(self._ltr_formula, self._output_formulas, max_var_ltr + 1)

    '''
    For Debugging
    '''

    def get_graph(self, src_state):
        edges = {}
        to_explore = {src_state}
        while to_explore:
            next_state = to_explore.pop()
            if next_state in edges.keys() or next_state in to_explore:
                continue
            successors = next_state.kripke.get_successors(next_state)
            edges[next_state] = successors
            to_explore |= set(successors)

        for s in edges.keys():
            print str(s) + '-> ' + ','.join([str(dst) for dst in edges[s]])

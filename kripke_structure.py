import itertools

from BitVector import BitVector

from aig_parser import AvyAigParser
from cnf_parser import CnfParser
from common import State
from formula_wrapper import FormulaWrapper
from z3_utils import Z3Utils
from z3 import *


class KripkeStructure(object):
    def __init__(self, aps):
        super(KripkeStructure, self).__init__()
        self._aps = aps

    def get_aps(self):
        return self._aps

    def get_successors(self, state):
        raise NotImplementedError()

    def get_initial_states(self):
        raise NotImplementedError()

    def is_state_labeled_with(self, state, ap):
        raise NotImplementedError()

    def get_ap_formula(self, ap, var_vector):
        raise NotImplementedError()

    def get_bis0_formula(self, state, var_vector):
        raise NotImplementedError()

    def get_tr_formula(self):
        raise NotImplementedError()

    def get_aps_for_state(self, state):
        raise NotImplementedError()

    def get_var_vector(self):
        raise NotImplementedError()



class AigKripkeStructure(KripkeStructure):
    def __init__(self, aig_path, aps, qe_policy):
        super(AigKripkeStructure, self).__init__(aps)
        self._aig_parser = AvyAigParser(aig_path)
        self._initial_states = None
        self._init_latch_values = self.get_initial_latch_values()

        self._overwrite_aig_reset_logic()

        parse_results = self._aig_parser.parse()
        self._num_latches = self._aig_parser.get_num_latches()
        self._cnf_parser = CnfParser(self._num_latches, qe_policy)
        self._tr = self._connect_aigs(parse_results)
        self._ap_conversion = self._aig_parser.get_ap_mapping()
        self._qe_policy = qe_policy

    def get_qe_policy(self):
        return self._qe_policy

    def _overwrite_aig_reset_logic(self):
        new_aig_lines = self._aig_parser.get_aig_after_reset()
        old_aig_path = self._aig_parser.get_aig_path()
        new_aig_path = '.'.join(old_aig_path.split('.')[:-1]) + '_reset.' + old_aig_path.split('.')[-1]
        with open(new_aig_path, 'w') as new_aig:
            new_aig.write(''.join(new_aig_lines))

        self._aig_parser = AvyAigParser(new_aig_path)

    def get_successors(self, state):
        return Z3Utils.get_all_successors(self._tr, state)

    def get_initial_latch_values(self):
        return self._aig_parser.get_initial_latch_values()

    def get_initial_states(self):
        if self._initial_states is not None:
            return self._initial_states

        inits_latches = [list(init) for init in self._init_latch_values]

        #       inits_latches = [[0] * self._num_latches]

        def get_outputs_for_latch_values(l_vals):
            return itertools.product(*[out_val_list \
                                       for out_formula in self._output_formulas
                                       for out_val_list in Z3Utils.get_all_next_assignments(out_formula, l_vals)])

        init_outputs = {tuple(init_latches): get_outputs_for_latch_values(init_latches)
                        for init_latches in inits_latches}

        def list_to_state(lst):
            data = BitVector(bitlist=lst)
            return State(data)

        res = [list_to_state(init_latches + list(init_out_value)) for init_latches in inits_latches for init_out_value
               in
               init_outputs[tuple(init_latches)]]
        self._initial_states = res
        return res

    def _get_var_num_for_ap(self, ap):
        ap_symb = self._ap_conversion[ap.get_ap_text()]
        var_num = int(ap_symb[1:]) + (self._aig_parser.get_num_latches() if ap_symb[0] == 'o' else 0)
        return var_num

    def is_state_labeled_with(self, state, ap):
        var_num = self._get_var_num_for_ap(ap)
        return True if int(state[var_num]) > 0 else False

    def get_ap_formula(self, ap, var_vector):
        return FormulaWrapper(var_vector[self._get_var_num_for_ap(ap)], [var_vector])

    def _get_formula_for_ap_literal(self, ap, var_vector, state):
        positive_form = var_vector[self._get_var_num_for_ap(ap)]
        final_form = positive_form if self.is_state_labeled_with(state, ap) else Not(positive_form)
        return FormulaWrapper(final_form, [var_vector])

    def get_bis0_formula(self, state, var_vector=None):
        if var_vector is None:
            var_vector = self.get_var_vector()
        ap_subformulas = [self._get_formula_for_ap_literal(ap, var_vector, state) for ap in self.get_aps()]
        bis0_z3_formula = simplify(And(*[ap_subformula.get_z3_formula() for ap_subformula in ap_subformulas]))
        return FormulaWrapper(bis0_z3_formula, [var_vector])

    def get_tr_formula(self):
        return self._tr

    def get_aps_for_state(self, state):
        return [ap for ap in self.get_aps() if self.is_state_labeled_with(state, ap)]

    def get_var_vector(self):
        return self._tr.get_var_vectors()[0]

    def _connect_aigs(self, parse_results):
        ltr_metadata, ltr_dimacs = parse_results[0]

        self._ltr_formula = self._cnf_parser.dimacs_to_z3(ltr_metadata, ltr_dimacs, self._cnf_parser.parse_metadata_tr)
        self._output_formulas = \
            [self._cnf_parser.dimacs_to_z3(output_metadata, output_dimacs, self._cnf_parser.parse_metadata_bad)
             for (output_metadata, output_dimacs) in parse_results[1:]]

        max_var_ltr = int(ltr_dimacs[0].split(' ')[-1])
        return Z3Utils.combine_ltr_with_bad_formulas(self._ltr_formula, self._output_formulas, max_var_ltr + 1)

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

import itertools

from aig_parser import AvyAigParser
from cnf_parser import CnfParser
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
    def __init__(self, aig_path, aps):
        super(AigKripkeStructure, self).__init__(aps)
        self._aig_parser = AvyAigParser(aig_path)
        parse_results = self._aig_parser.parse()

        self._tr = self._connect_aigs(parse_results)
        self._ap_conversion = self._aig_parser.get_ap_mapping()

    def get_successors(self, state):
        return Z3Utils.get_all_successors(self._tr, state)

    def get_initial_states(self):
        init_latches = [0] * self._aig_parser.get_num_latches()
        init_outputs = [map(lambda state_list: state_list[0],
                            Z3Utils.get_all_successors(out_formula, init_latches)) \
                        for out_formula in self._output_formulas]

        init_out_values = itertools.product(*init_outputs)
        res =  [init_latches + list(init_out_value) for init_out_value in init_out_values]
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
        bis0_z3_formula = And(*[ap_subformula.get_z3_formula() for ap_subformula in ap_subformulas])
        return FormulaWrapper(bis0_z3_formula, [var_vector])

    def get_tr_formula(self):
        return self._tr

    def get_aps_for_state(self, state):
        return [ap for ap in self.get_aps() if self.is_state_labeled_with(state, ap)]

    def get_var_vector(self):
        return self._tr.get_var_vectors()[0]

    def _connect_aigs(self, parse_results):
        ltr_metadata, ltr_dimacs = parse_results[0]

        num_latches = self._aig_parser.get_num_latches()
        self._ltr_formula = CnfParser.z3_formula_from_dimacs(ltr_metadata, ltr_dimacs, CnfParser.parse_metadata_tr,
                                                             num_latches)
        self._output_formulas = \
            [CnfParser.z3_formula_from_dimacs(output_metadata, output_dimacs,
                                              CnfParser.parse_metadata_bad, num_latches)
             for (output_metadata, output_dimacs) in parse_results[1:]]

        max_var_ltr = int(ltr_dimacs[0].split(' ')[-1])
        return Z3Utils.combine_ltr_with_bad_formulas(self._ltr_formula, self._output_formulas, max_var_ltr + 1)

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
        metadata, tr_dimcas = self._aig_parser.parse()
        self._tr = CnfParser.z3_formula_from_dimacs(metadata, tr_dimcas)
        self._ap_conversion = self._aig_parser.get_ap_mapping()

    def get_successors(self, state):
        return Z3Utils.get_all_successors(self._tr, state)

    def get_initial_states(self):
        initial_states_singleton_vector = [[0] * self._aig_parser.get_number_of_variables()]
        return initial_states_singleton_vector

    def _get_var_num_for_ap(self, ap):
        ap_symb = self._ap_conversion[ap.get_ap_text()]
        if ap_symb[0] != 'l':
            raise Exception('Not state AP :( Talk to yakir dude...')
        var_num = int(ap_symb[1:])
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

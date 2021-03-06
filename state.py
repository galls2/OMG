import logging

from z3 import And, Not, is_true

from common import int_list_to_cube, z3_val_to_int
from formula_wrapper import FormulaWrapper, QBF
from sat_solver import SatSolverSelector

logger = logging.getLogger('OMG')


class State(object):
    def __init__(self, formula_wrapper, kripke):
        self.formula_wrapper = formula_wrapper
        self.kripke = kripke
        self.bis0 = None

    def __eq__(self, o):
        return self.formula_wrapper.get_qbf() == o.formula_wrapper.get_qbf()

    def __ne__(self, o):
        return not self == o

    def __str__(self):
        s = SatSolverSelector.SatSolverCtor()
        s.add(self.formula_wrapper.to_z3())
        s.check()
        model = s.model()
        vs = self.formula_wrapper.get_var_vectors()[0]
        return str([z3_val_to_int(model[v]) for v in vs])

    def var_for_ap(self, ap):
        var_num = self.kripke.get_var_num_for_ap(ap)
        return self.formula_wrapper.get_var_vectors()[0][var_num]

    def get_all_aps(self):
        return self.kripke.get_aps()

    def is_labeled_with(self, ap):
        ap_lit = self.var_for_ap(ap)
        _, model = self.formula_wrapper.sat_get_model()
        return is_true(model[ap_lit])

    def ap_lit_by_model(self, model, ap):
        var = self.var_for_ap(ap)
        return var if is_true(model[var]) else Not(var)

    def get_bis0_formula(self):
        if self.bis0 is not None:
            return self.bis0

        AP = self.kripke.get_aps()
        _, model = self.formula_wrapper.sat_get_model()

        state_formula = self.kripke.get_output_formula().get_qbf()
        prop = And(state_formula.to_z3(), *[self.ap_lit_by_model(model, ap) for ap in AP])
        bis0 = FormulaWrapper(QBF(prop), self.formula_wrapper.get_var_vectors(), [self.kripke.get_input_var_vector()])
        self.bis0 = bis0
        return bis0

    def get_sat_aps(self):
        _, model = self.formula_wrapper.sat_get_model()
        return [ap for ap in self.get_all_aps() if is_true(model[self.var_for_ap(ap)])]

    def __hash__(self):
        return hash(self.formula_wrapper)

    @staticmethod
    def from_int_list(int_list, _vars, kripke):
        cube = int_list_to_cube(int_list, _vars)
        f_wrap = FormulaWrapper(QBF(cube), [_vars], [kripke.get_input_var_vector()])
        return State(f_wrap, kripke)

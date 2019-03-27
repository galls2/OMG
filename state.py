from z3 import Solver, And, sat, Not

from common import int_list_to_cube
from formula_wrapper import FormulaWrapper
from common import z3_val_to_bool


class State(object):
    def __init__(self, formula_wrapper, kripke):
        self.formula_wrapper = formula_wrapper
        self.kripke = kripke
        self.bis0 = None

    def __eq__(self, o):
        return self.formula_wrapper.get_z3().eq(o.formula_wrapper.get_z3())

    def __ne__(self, o):
        return not self == o

    def __str__(self):
        return str([1 if Solver().check(And(self.formula_wrapper.get_z3(), v)) == sat else 0
                    for v in self.formula_wrapper.get_var_vectors()[0]])

    def var_for_ap(self, ap):
        var_num = self.kripke.get_var_num_for_ap(ap)
        return self.formula_wrapper.get_var_vectors()[0][var_num]

    def get_all_aps(self):
        return self.kripke.get_aps()

    def is_labeled_with(self, ap):
        ap_lit = self.var_for_ap(ap)
        _, model = self.formula_wrapper.sat_get_model()
        return z3_val_to_bool(model[ap_lit])

    def ap_lit_by_model(self, model, ap):
        var = self.var_for_ap(ap)
        val = z3_val_to_bool(model[var])
        return var if val else Not(var)

    def get_bis0_formula(self):
        if self.bis0 is not None:
            return self.bis0

        AP = self.kripke.get_aps()
        _, model = self.formula_wrapper.sat_get_model()

        f = And(*[self.ap_lit_by_model(model, ap) for ap in AP])
        self.bis0 = FormulaWrapper(f, self.formula_wrapper.get_var_vectors())
        return self.bis0

    def get_sat_aps(self):
        return [ap for ap in self.get_all_aps() if self.is_labeled_with(ap)]

    def __hash__(self):
        return hash(self.formula_wrapper)

    @staticmethod
    def from_int_list(int_list, _vars, kripke):
        cube = int_list_to_cube(int_list, _vars)
        f_wrap = FormulaWrapper(cube, [_vars])
        return State(f_wrap, kripke)

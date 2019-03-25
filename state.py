from z3 import Solver, And, sat, Not

from common import int_list_to_cube
from formula_wrapper import FormulaWrapper


class State(object):
    def __init__(self, formula_wrapper, kripke):
        self.formula_wrapper = formula_wrapper
        self.kripke = kripke

    def __eq__(self, o):
        return self.formula_wrapper.get_z3().eq(o.formula_wrapper.get_z3())

    def __ne__(self, o):
        return not self == o

    def __str__(self):
        return str([1 if Solver().check(And(self.formula_wrapper.get_z3(),v)) == sat else 0
                for v in self.formula_wrapper.get_var_vectors()[0]])

    def lit_for_ap(self, ap):
        var_num = self.kripke.get_var_num_for_ap(ap)
        return self.formula_wrapper.get_var_vectors()[0][var_num]

    def lit_agrees_with_formula(self, lit):
        return Solver().check(And(self.formula_wrapper.get_z3(), lit)) == sat

    def is_labeled_with(self, ap):
        ap_lit = self.lit_for_ap(ap)
        return self.lit_agrees_with_formula(ap_lit)

    def get_bis0_formula(self):
        AP = self.kripke.get_aps()
        f = And(*[self.lit_for_ap(ap) if self.is_labeled_with(ap) else Not(self.lit_for_ap(ap)) for ap in AP])
        return FormulaWrapper(f, self.formula_wrapper.get_var_vectors())

    def get_all_aps(self):
        return self.kripke.get_aps()

    def get_sat_aps(self):
        return [ap for ap in self.get_all_aps() if self.is_labeled_with(ap)]

    def __hash__(self):
        return hash(self.formula_wrapper)

    @staticmethod
    def from_int_list(int_list, _vars, kripke):
        cube = int_list_to_cube(int_list, _vars)
        f_wrap = FormulaWrapper(cube, [_vars])
        return State(f_wrap, kripke)
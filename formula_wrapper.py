from z3 import *


class FormulaWrapper(object):
    def __init__(self, z3_formula, var_vectors): #TODO builder pattern
        super(FormulaWrapper, self).__init__()
        self._z3_formula = z3_formula
        self._var_vectors = var_vectors

    def get_z3_formula(self):
        return self._z3_formula

    def get_var_vectors(self):
        return self._var_vectors

    def substitute(self, substitute_with, vec_num_to_substitute=0, new_vars=None):
        substitutions = zip(self._var_vectors[vec_num_to_substitute], substitute_with)
    #    print self._z3_formula
        new_formula = substitute(self._z3_formula, *substitutions)
     #   print new_formula
        new_formula = simplify(new_formula)
     #   print new_formula
        if new_vars is not None:
            new_var_vectors = list(self._var_vectors)
            new_var_vectors[vec_num_to_substitute: vec_num_to_substitute+1] = [new_vars]
        else:
            new_var_vectors = self._var_vectors[:vec_num_to_substitute]+self._var_vectors[vec_num_to_substitute+1:]
        return FormulaWrapper(new_formula, new_var_vectors)

    def is_sat(self):
        s = Solver()
        return s.check(self.get_z3_formula()) == sat

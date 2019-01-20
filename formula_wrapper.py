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

    def substitute(self, substitute_with, vec_num_to_substitute, new_vars=None):
        substitute_with_z3_format = [BoolVal(True) if val == 1 else BoolVal(False) for val in substitute_with]
        substitutions = zip(self._var_vectors[vec_num_to_substitute], substitute_with_z3_format)
        print self._z3_formula
        new_formula = substitute(self._z3_formula, *substitutions)
        print new_formula
        new_formula = simplify(new_formula)
        print new_formula
        if new_vars is not None:
            new_var_vectors = list(self._var_vectors)
            new_var_vectors[vec_num_to_substitute: vec_num_to_substitute+1] = list(new_vars)
        else:
            new_var_vectors = self._var_vectors[:vec_num_to_substitute]+self._var_vectors[vec_num_to_substitute+1:]
        return FormulaWrapper(new_formula, new_var_vectors)
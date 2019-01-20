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
        new_formula = substitute(self._z3_formula, zip(self._var_vectors[vec_num_to_substitute], substitute_with)
        if new_vars is not None:
            new_var_vectors = copy(self._var_vectors)
            new_var_vectors[vec_num_to_substitute: vec_num_to_substitute+1] = copy(new_vars)
        else:
            new_var_vectors = self._var_vectors[:vec_num_to_substitute]+self._var_vectors[vec_num_to_substitute+1:]
        return FormulaWrapper(new_formula, new_var_vectors)
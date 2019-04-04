from z3 import *

from common import int_vec_to_z3, foldr


class FormulaWrapper(object):
    def __init__(self, z3_formula, var_vectors, input_vectors):
        super(FormulaWrapper, self).__init__()
        self._z3_formula = z3_formula
        self._var_vectors = var_vectors
        self._input_vectors = input_vectors

    def get_z3(self):
        return self._z3_formula

    def get_var_vectors(self):
        return self._var_vectors

    def get_input_vectors(self):
        return self._input_vectors

    def assign_state(self, state, v_num=0):
        base_formula, prev_vec = self._z3_formula, self._var_vectors
        cube_substituted = state.formula_wrapper.substitute(prev_vec[v_num], v_num).get_z3()
        inner = And(base_formula, cube_substituted)
        return FormulaWrapper(inner, prev_vec[:v_num] + prev_vec[v_num + 1:], self._input_vectors)

    def assign_int_vec(self, int_vec, v_num=0):
        base_formula, prev_vec = self._z3_formula, self._var_vectors
        substitutions = zip(prev_vec[v_num], int_vec_to_z3(int_vec))
        assigned_formula = simplify(substitute(base_formula, *substitutions))
        return FormulaWrapper(assigned_formula, prev_vec[:v_num] + prev_vec[v_num + 1:], self._input_vectors)

    def substitute(self, substitute_with, vec_num, new_vars=None):
        if new_vars is None:
            new_vars = substitute_with
        prev_vec = self._var_vectors

        substitutions = zip(prev_vec[vec_num], substitute_with)
        new_formula = simplify(substitute(self._z3_formula, *substitutions))

        return FormulaWrapper(new_formula, prev_vec[:vec_num] + [new_vars] + prev_vec[vec_num + 1:],
                              self._input_vectors)

    def substitute_inputs(self, substitute_with, vec_num, new_vars=None):
        if new_vars is None:
            new_vars = substitute_with
        prev_vec = self._input_vectors

        substitutions = zip(prev_vec[vec_num], substitute_with)
        new_formula = simplify(substitute(self._z3_formula, *substitutions))

        return FormulaWrapper(new_formula, self._var_vectors, prev_vec[:vec_num] + [new_vars] + prev_vec[vec_num + 1:])

    def is_sat(self):
        s = Solver()
        return s.check(self.get_z3()) == sat

    def sat_get_model(self):
        s = Solver()
        return True, s.model() if s.check(self._z3_formula) else False

    def __hash__(self):
        return hash(self._z3_formula)

    def __eq__(self, o):
        return self._z3_formula.eq(o.get_z3())

    def __ne__(self, o):
        return not self == o


class QBF(object):
    def __init__(self, q_list, prop_formula):
        super(QBF, self).__init__()
        self._q_list = q_list
        self._prop = prop_formula

    def connect(self):
        return foldr(lambda (_q, _v), f: (Exists if _q == 'E' else ForAll)(_v, f), self._prop, self._q_list)

    def negate(self):
        new_q_list = [(chr(134 - ord(_q)), _v) for (_q, _v) in self._q_list]
        return QBF(new_q_list, simplify(Not(self._prop)))


if __name__ == '__main__':
    x = [Bool('x' + str(i)) for i in range(5)]
    q = QBF([('A' if i % 2 == 0 else 'E', x[i]) for i in range(5)], And(*x))
    print q.connect()
    print q.negate().connect()
    print q.negate().negate().connect()

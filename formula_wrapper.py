from z3 import *

from common import int_vec_to_z3, foldr


class FormulaWrapper(object):
    def __init__(self, qbf, var_vectors, input_vectors):
        super(FormulaWrapper, self).__init__()
        self._qbf = qbf
        self._var_vectors = var_vectors
        self._input_vectors = input_vectors

    def get_qbf(self):
        return self._qbf

    def get_var_vectors(self):
        return self._var_vectors

    def get_input_vectors(self):
        return self._input_vectors

    def _substitute_inner(self, prev_vec, substitute_with, vec_num):
        substitutions = zip(prev_vec[vec_num], substitute_with)
        new_prop_formula = simplify(substitute(self._qbf.get_prop(), *substitutions))
        new_qbf = QBF(new_prop_formula, self._qbf.get_q_list())
        return new_qbf

    def substitute(self, substitute_with, vec_num, new_vars=None):
        if new_vars is None:
            new_vars = substitute_with
        prev_vec = self._var_vectors
        new_qbf = self._substitute_inner(prev_vec, substitute_with, vec_num)
        return FormulaWrapper(new_qbf, prev_vec[:vec_num] + [new_vars] + prev_vec[vec_num + 1:],
                              self._input_vectors)

    def substitute_inputs(self, substitute_with, vec_num, new_vars=None):
        if new_vars is None:
            new_vars = substitute_with
        prev_vec = self._input_vectors
        new_qbf = self._substitute_inner(prev_vec, substitute_with, vec_num)
        return FormulaWrapper(new_qbf, self._var_vectors, prev_vec[:vec_num] + [new_vars] + prev_vec[vec_num + 1:])

    def assign_state(self, state, v_num=0):
        base_formula = self._qbf.get_prop()
        prev_vec = self._var_vectors
        cube_substituted = state.formula_wrapper.substitute(prev_vec[v_num], v_num).get_z3()
        inner = And(base_formula, cube_substituted)
        assigned_qbf = QBF(inner, self._qbf.get_q_list())
        return FormulaWrapper(assigned_qbf, prev_vec[:v_num] + prev_vec[v_num + 1:], self._input_vectors)

    def assign_int_vec(self, int_vec, v_num=0):
        base_formula = self._qbf.get_prop()
        prev_vec = self._var_vectors
        substitutions = zip(prev_vec[v_num], int_vec_to_z3(int_vec))
        assigned_formula = simplify(substitute(base_formula, *substitutions))
        assigned_qbf = QBF(assigned_formula, self._qbf.get_q_list())
        return FormulaWrapper(assigned_qbf, prev_vec[:v_num] + prev_vec[v_num + 1:], self._input_vectors)

    def and_flag(self, flag):
        new_qbf = QBF(And(self._qbf.get_prop(), flag), self._qbf.get_q_list())
        return FormulaWrapper(new_qbf, self._var_vectors, self._input_vectors)

    def is_sat(self):
        s = Solver()
        return s.check(self._qbf.connect()) == sat

    def sat_get_model(self):
        s = Solver()
        return True, s.model() if s.check(self._qbf.connect()) else False

    def __hash__(self):
        return hash(self._qbf)

    def __eq__(self, o):
        return self._qbf == o.get_qbf()

    def __ne__(self, o):
        return not self == o


class QBF(object):
    def __init__(self, prop_formula, q_list=None):
        super(QBF, self).__init__()
        if q_list is None:
            q_list = []
        self._q_list = q_list
        self._prop = prop_formula

    def get_prop(self):
        return self._prop

    def get_q_list(self):
        return self._q_list

    def connect(self):
        return foldr(lambda (_q, _v), f: (Exists if _q == 'E' else ForAll)(_v, f), self._prop, self._q_list)

    def negate(self):
        new_q_list = [(chr(134 - ord(_q)), _v) for (_q, _v) in self._q_list]
        return QBF(simplify(Not(self._prop)), new_q_list)

    def __eq__(self, o):
        return self._prop.eq(o.get_prop()) and self._q_list == o.get_q_list()

    def __ne__(self, o):
        return not self == o

    def __hash__(self):
        hash((hash(self._prop), hash(self._q_list)))

if __name__ == '__main__':
    x = [Bool('x' + str(i)) for i in range(5)]
    q = QBF(And(*x), [('A' if i % 2 == 0 else 'E', x[i]) for i in range(5)])
    print q.connect()
    print q.negate().connect()
    print q.negate().negate().connect()

    q2 = QBF(And(*x))
    print q2.connect()

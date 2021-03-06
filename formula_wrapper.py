from z3 import ForAll, Exists, simplify, substitute, And, is_not, Not

from common import int_vec_to_z3, foldr
from sat_solver import SatSolverSelector
from var_manager import VarManager

q_to_z3 = {1: ForAll, -1: Exists}


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
        cube_substituted = state.formula_wrapper.substitute(prev_vec[v_num], v_num).get_qbf().get_prop()
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

    def is_prop(self):
        return not self._qbf._q_list

    def is_sat(self):
        s = SatSolverSelector.SatSolverCtor()
        res = s.add(self.to_z3())
        return res and s.check()

    def sat_get_model(self):
        s = SatSolverSelector.SatSolverCtor()
        res = s.add(self.to_z3())
        return True, s.model() if (res is not False) and s.check() else False

    def __hash__(self):
        return hash(self._qbf)

    def __eq__(self, o):
        return self._qbf == o.get_qbf()

    def __ne__(self, o):
        return not self == o

    def negate(self):
        return FormulaWrapper(self._qbf.negate(), self._var_vectors, self._input_vectors)

    def renew_quantifiers(self):
        new_qbf = self._qbf.renew_quantifiers()
        return FormulaWrapper(new_qbf, self._var_vectors, self._input_vectors)

    def well_named(self):
        return self._qbf.well_named()

    def to_z3(self):
        return self._qbf.to_z3()


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

    def to_z3(self):
        return foldr(lambda (_q, _v), f: q_to_z3[_q](_v, f), self._prop, self._q_list)

    def negate(self):
        new_q_list = [(-_q, _v) for (_q, _v) in self._q_list]
        return QBF(self._prop.children()[0] if is_not(self._prop) else Not(self._prop), new_q_list)

    def renew_quantifiers(self):
        n_q_vecs = len(self._q_list)
        if n_q_vecs == 0:
            return self

        new_quantified_vectors = [VarManager.duplicate_vars(q_vars) for (_, q_vars) in self._q_list]
        new_q_list = [(self._q_list[_i][0], new_quantified_vectors[_i]) for _i in xrange(n_q_vecs)]
        substitutions = [(self._q_list[_i][1][_j], new_q_list[_i][1][_j]) for _i in xrange(n_q_vecs) for _j in
                         xrange(len(self._q_list[_i][1]))]
        new_prop = substitute(self._prop, *substitutions)
        return QBF(new_prop, new_q_list)

    def well_named(self):
        '''
	q_list = self.get_q_list()

        appeared = set()
        for _, var_vec in q_list:
            for _v in var_vec:
                if _v in appeared:
                    return False
                appeared.add(_v)
        return True
	'''
        return True

    def __eq__(self, o):
        return self._prop.eq(o.get_prop()) and self._q_list == o.get_q_list()

    def __ne__(self, o):
        return not self == o

    def __hash__(self):
        return hash((hash(self._prop), hash(tuple(self._q_list))))


import z3
from pysat.solvers import Glucose4
from z3 import BoolVal, sat, Not, Bool

from common import MyModel
from qbf_solver import get_cnf


class SatSolver(object):
    def check(self, ):
        raise NotImplementedError

    def model(self):
        raise NotImplementedError

    def add(self, f):
        raise NotImplementedError


class Z3SatSolver(SatSolver):

    def __init__(self):
        self._solver = z3.Solver()

    def check(self):
        return self._solver.check() == sat

    def model(self):
        return self._solver.model()

    def add(self, f):
        return self._solver.add(f)

    def add_clause(self, cl):
        return self._solver.add(cl)


class GlucoseSatSolver(SatSolver):
    def __init__(self):
        self._solver = Glucose4()
        self._name_to_nums = None
        self._num_to_name = None

    def check(self):
        return self._solver.solve()

    def model(self):
        raw_model = self._solver.get_model()

        model = MyModel({self._num_to_name[val]: BoolVal(val > 0) for val in raw_model})
        return model

    def add(self, f):
        clauses, dimacs, names_to_nums, num_to_name = get_cnf(f)
        if clauses is False:
            return False
        _names_to_nums = dict(names_to_nums)
        _names_to_nums.update({Not(Bool(k)): -v for (k, v) in names_to_nums.items()})
        _names_to_nums.update({(Bool(k)):  v for (k, v) in names_to_nums.items()})
        self._name_to_nums = _names_to_nums

        num_to_name.update({-k: v for (k, v) in num_to_name.items()})
        self._num_to_name = num_to_name
        self._solver.append_formula(clauses)
        return True

    def add_clause(self, cl):

        name_to_num = self._name_to_nums

        alt_cls = [name_to_num[lit] for lit in cl.children()]

        self._solver.add_clause(alt_cls)


class SatSolverSelector(object):
    SatSolverCtor = None

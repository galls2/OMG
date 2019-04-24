import math

from pysat.solvers import Glucose4
from z3 import Solver, BoolVal, sat

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
        self._solver = Solver()

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
        model = MyModel({self._num_to_name[abs(val)]: BoolVal(True) if val > 0 else BoolVal(False) for val in raw_model})
        return model

    def add(self, f):
        clauses, dimacs, names_to_nums, num_to_name = get_cnf(f)
        self._name_to_nums = names_to_nums
        self._num_to_name = num_to_name
        self._solver.append_formula(clauses)

    def add_clause(self, cl):
        cls, _, _, num_to_name = get_cnf(cl)
        name_to_num = self._name_to_nums
        alt_cls = [[int(math.copysign(name_to_num[num_to_name[abs(l)].decl().name()], l)) for l in cl] for cl in cls]
        self._solver.append_formula(alt_cls)


class SatSolverSelector(object):
    SatSolverCtor = None

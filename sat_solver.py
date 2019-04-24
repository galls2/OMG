from pysat.solvers import Glucose4
from z3 import Solver


class SatSolver(object):
    def check(self, *f):
        raise NotImplementedError

    def model(self):
        raise NotImplementedError

    def add(self, f):
        raise NotImplementedError

    def assertions(self):
        raise NotImplementedError


class Z3SatSolver(SatSolver):
    def assertions(self):
        return self._solver.assertions()

    def __init__(self):
        self._solver = Solver()

    def check(self, *f):
        return self._solver.check(*f)

    def model(self):
        return self._solver.model()

    def add(self, f):
        return self._solver.add(f)

class GlucoseSatSolver(SatSolver):
    def __init__(self):
        self._solver = Glucose4()

    def check(self, *f):
        return self._solver.solve(*f)



class SatSolverSelector(object):
    SatSolverCtor = None

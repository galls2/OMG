from z3 import *

class QbfSolver(object):
    def solve(self, formula):
        raise NotImplementedError()

    def incremental_solve(self, formulas, stop_res):
        raise NotImplementedError

    def incremental_solve_flags(self, formula, flags, stop_res):
        return self.incremental_solve([formula.and_flag(flag) for flag in flags], stop_res)


class DepQbfSimpleSolver(QbfSolver):
    def solve(self, formula):
        pass

    def incremental_solve(self, formulas, stop_res):
        for i in range(len(formulas)):
            print i
            is_sat, res = self.solve(formulas[i])
            if is_sat == stop_res:
                return i, res
        return False, False


class Z3QbfSolver(QbfSolver):

    def solve(self, formula):
        s = Solver()
        res = s.check(formula)
        if res == sat:
            return sat, s.model()
        return unsat, False

    def incremental_solve(self, formulas, stop_res):
        s = Solver()
        for i in range(len(formulas)):
            f = formulas[i].get_qbf().connect()
    #        print i
            res = s.check(f)
    #        print 'done' + str(i)
            if res == stop_res:
                return i, (s.model() if res == sat else False)
        return False, False
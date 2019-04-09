import pydepqbf

from z3 import *
from pydepqbf import *

from z3.z3util import get_vars

from common import MyModel


class QbfSolver(object):
    def solve(self, formula):
        raise NotImplementedError()

    def incremental_solve(self, formulas, stop_res):
        raise NotImplementedError

    def incremental_solve_flags(self, formula, flags, stop_res):
        return self.incremental_solve([formula.and_flag(flag) for flag in flags], stop_res)


class DepQbfSimpleSolver(QbfSolver):
    def __init__(self):
        super(DepQbfSimpleSolver, self).__init__()

    def solve(self, qbf):
        cnfer = Tactic('tseitin-cnf')

        cnf_prop = cnfer(qbf.get_prop()).as_expr()
        g = Goal()
        g.add(cnf_prop)
        dimacs = g.dimacs().split('\n')

        first_conversion_line = next(i for i in range(len(dimacs)) if dimacs[i].startswith('c'))
        conversion_lines = dimacs[first_conversion_line:]
        names_to_nums = {_l.split()[2]: int(_l.split()[1]) for _l in conversion_lines}

        quantifiers = [
            (_q, [names_to_nums[_v.decl().name()] for _v in v_list if _v.decl().name() in names_to_nums.keys()])
            for (_q, v_list) in qbf.get_q_list()]

        clause_lines = dimacs[1:first_conversion_line]
        clauses = [[int(_x) for _x in _line.split()[:-1]] for _line in clause_lines]

        is_sat, certificate = pydepqbf.solve(quantifiers, clauses)
     #   print is_sat, certificate
        if is_sat == QDPLL_RESULT_UNSAT:
            return unsat, False

        num_to_name = {a: Bool(b) for (b, a) in names_to_nums.items()}
        model = MyModel({num_to_name[abs(val)]: BoolVal(True) if val > 0 else BoolVal(False) for val in certificate})
        return sat, model

    def incremental_solve(self, formulas, stop_res):
        for i in range(len(formulas)):
            #print i
            is_sat, res = self.solve(formulas[i].get_qbf())
            if is_sat == stop_res:
                return i, res
        return False, False


class Z3QbfSolver(QbfSolver):
    def __init__(self):
        super(Z3QbfSolver, self).__init__()

    def solve(self, qbf):
        s = Solver()
        res = s.check(qbf.to_z3())
        if res == sat:
            return sat, s.model()
        return unsat, False

    def incremental_solve(self, formulas, stop_res):
        s = Solver()
        for i in range(len(formulas)):
            f = formulas[i].get_qbf().to_z3()
            #        print i
            res = s.check(f)
            #        print 'done' + str(i)
            if res == stop_res:
                return i, (s.model() if res == sat else False)
        return False, False

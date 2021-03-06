import pydepqbf
from pydepqbf import *

from z3 import *

from common import MyModel, foldr, time_me

CAQE_PATH = '/home/galls2/Desktop/caqe/target/release/caqe'


def to_file(path, txt_lines):
    f = open(path, 'w')
    f.write(txt_lines)
    f.close()


class QbfSolver(object):

    def solve(self, formula):
        raise NotImplementedError()

    def incremental_solve(self, formulas, stop_res):
        raise NotImplementedError

    def incremental_solve_flags(self, formula, flags, stop_res):
        return self.incremental_solve([formula.and_flag(flag) for flag in flags], stop_res)


def to_qdimacs(dimacs, quantifiers):
    q_lines = [('a' if _q == 1 else 'e') + ' ' + ' '.join([str(_t) for _t in _vs]) + ' 0' for (_q, _vs) in quantifiers]
    clasues_no_comments = [_l for _l in dimacs[1:] if not _l.startswith('c')]
    return '\n'.join(dimacs[0:1] + q_lines + clasues_no_comments)


def build_z3(quantifiers, clauses):
    def parse_clause(clause):
        return Or(*[Bool(str(lit)) if lit > 0 else Not(Bool(str(lit))) for lit in clause])

    cnf = And(*[parse_clause(clause) for clause in clauses])
    qs = [(_q, [Bool(_x) for _x in vs]) for (_q, vs) in quantifiers]
    return foldr(lambda (_q, _v), f: (Exists if _q == -1 else ForAll)(_v, f), cnf, qs)


def get_qcnf(formula_wrapper):
    old_qbf = formula_wrapper.get_qbf()
    prop = simplify(old_qbf.get_prop())

    clauses, dimacs, names_to_nums, num_to_name = get_cnf(prop)

    q_list = old_qbf.get_q_list()
    if q_list:
        new_vars_to_quantify = [_v for v_vec in
                                formula_wrapper.get_var_vectors() + formula_wrapper.get_input_vectors() for _v in
                                v_vec]
        q_list = [(QDPLL_QTYPE_EXISTS, new_vars_to_quantify)] + old_qbf.get_q_list()

        old_quantified_vars = set([_v for (_, _vs) in old_qbf.get_q_list() for _v in _vs])

        tseitin_vars = (set([Bool(_u) for _u in names_to_nums.keys()]) - old_quantified_vars) - set(
            new_vars_to_quantify)
        _o_q_list = q_list + [(QDPLL_QTYPE_EXISTS, list(tseitin_vars))]

        alt_idxs = [0] + [i for i in range(1, len(_o_q_list)) if _o_q_list[i][0] != _o_q_list[i - 1][0]] + [
            len(_o_q_list)]
        blocks = [_o_q_list[alt_idxs[i]:alt_idxs[i + 1]] for i in range(len(alt_idxs) - 1)]
        q_list = [(b[0][0], [_var for _tup in b for _var in _tup[1]]) for b in blocks]

    quantifiers = [
        (_q, [names_to_nums[_v.decl().name()] for _v in v_list if _v.decl().name() in names_to_nums.keys()])
        for (_q, v_list) in q_list]
    return dimacs, clauses, num_to_name, quantifiers


def get_cnf(prop):
    cnf_prop = Tactic('tseitin-cnf')(prop).as_expr()
    if is_false(cnf_prop):
        return False, False, False, False
    g = Goal()
    g.add(cnf_prop)
    dimacs = g.dimacs().split('\n')
    first_conversion_line = next(i for i in range(len(dimacs)) if dimacs[i].startswith('c'))
    conversion_lines = dimacs[first_conversion_line:]
    #        print conversion_lines
    names_to_nums = {_l.split()[2]: int(_l.split()[1]) for _l in conversion_lines}
    num_to_name = {a: Bool(b) for (b, a) in names_to_nums.items()}
    clause_lines = dimacs[1:first_conversion_line]
    clauses = [[int(_x) for _x in _line.split()[:-1]] for _line in clause_lines]
    return clauses, dimacs, names_to_nums, num_to_name


class DepQbfSimpleSolver(QbfSolver):
    def __init__(self):
        super(DepQbfSimpleSolver, self).__init__()

    def solve(self, formula_wrapper):
        dimacs, clauses, num_to_name, quantifiers = get_qcnf(formula_wrapper)

        is_sat, certificate = pydepqbf.solve(quantifiers, clauses)
        if is_sat == QDPLL_RESULT_UNSAT:
            return unsat, False

        model = MyModel({num_to_name[abs(val)]: BoolVal(True) if val > 0 else BoolVal(False) for val in certificate})
        return sat, model


    def incremental_solve(self, formulas, stop_res):
        for i in range(len(formulas)):
            # print i
            is_sat, res = self.solve(formulas[i])
            if is_sat == stop_res:
                return i, res
        return False, False


class Z3QbfSolver(QbfSolver):
    def __init__(self):
        super(Z3QbfSolver, self).__init__()

    def solve(self, formula_wrapper):
        s = Solver()
        res = s.check(formula_wrapper.to_z3())
        if res == sat:
            return sat, s.model()
        return unsat, False

    def incremental_solve(self, formulas, stop_res):
        s = Solver()
        for i in range(len(formulas)):
            f = formulas[i].to_z3()
            #        print i
            res = s.check(f)
            #        print 'done' + str(i)
            if res == stop_res:
                return i, (s.model() if res == sat else False)
        return False, False


def del_file(path):
    os.system('rm {}'.format(path))


class CaqeQbfSolver(QbfSolver):

    def solve(self, formula):
        dimacs, clauses, num_to_name, quantifiers = get_qcnf(formula)

        print 'BEFORE CAEQ'
        qdimacs = to_qdimacs(dimacs, quantifiers)
        path = '__qdimacs.txt'
        to_file(path, qdimacs)
        out_path = 'qdimacs_out.txt'
        cmd_do_caqe = '{caqe} {input} --qdo > {out}'.format(caqe=CAQE_PATH, input=path, out=out_path)
        os.system(cmd_do_caqe)

        is_sat, certificate = time_me(pydepqbf.solve, [quantifiers, clauses], 'QBF:: ')
        print 'CAQE  ', is_sat, certificate

        del_file(path)
        del_file(out_path)
        if is_sat == QDPLL_RESULT_UNSAT:
            return unsat, False

        model = MyModel({num_to_name[abs(val)]: BoolVal(True) if val > 0 else BoolVal(False) for val in certificate})
        return sat, model

    def incremental_solve(self, formulas, stop_res):
        for i in range(len(formulas)):
            # print i
            is_sat, res = self.solve(formulas[i])
            if is_sat == stop_res:
                return i, res
        return False, False


class QbfSolverSelector(object):
    QbfSolverCtor = None

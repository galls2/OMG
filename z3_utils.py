from z3 import *

from formula_wrapper import FormulaWrapper


class AstRefKey:
    def __init__(self, n):
        self.n = n

    def __hash__(self):
        return self.n.hash()

    def __eq__(self, other):
        return self.n.eq(other.n)

    def __repr__(self):
        return str(self.n)


def askey(n):
    assert isinstance(n, AstRef)
    return AstRefKey(n)


def get_vars(f):
    r = []

    def collect(f):
        if is_const(f):
            if f.decl().kind() == Z3_OP_UNINTERPRETED and not askey(f) in r:
                r.append(askey(f))
        else:
            for c in f.children():
                collect(c)

    collect(f)
    return map(lambda d: d.n, list(r))


def z3_val_to_int(z3_val):
    if z3_val.sexpr() == 'true':
        return 1
    return 0


class Z3Utils(object):
    copies_counter = 0

    def __init__(self):
        super(Z3Utils, self).__init__()

    @classmethod
    def duplicate_vars(cls, var_vector):
        new_var_vector = [Bool(var.decl().name() + '_' + str(cls.copies_counter)) for var in var_vector]
        cls.copies_counter += 1
        return new_var_vector

    @classmethod
    def get_split_formulas(cls, to_split, split_by, transitions):
        formula_to_split = to_split.get_descriptive_formula()
        formula_split_by = split_by.get_descriptive_formula()

        to_split_vars = get_vars(formula_to_split)
        split_by_vars = get_vars(formula_split_by)

        has_son_formula_vars = cls.duplicate_vars(split_by_vars)
        split_by_formula_tag = substitute(formula_split_by, zip(split_by_vars, has_son_formula_vars))  # B(v) [v<-v']

        transitions_has_sons = substitute(transitions, zip(get_vars(transitions), to_split_vars + has_son_formula_vars))
        formula_has_son = And(formula_to_split, Exists(has_son_formula_vars, And(transitions_has_sons,
                                                                                 split_by_formula_tag)))  # A(v) & Ev'[R(v,v')&B(v')]

        no_son_formula_vars = cls.duplicate_vars(split_by_vars)
        split_by_formula_tagtag = substitute(formula_split_by, zip(split_by_vars, no_son_formula_vars))  # B(v) [v<-v'']

        transitions_no_sons = substitute(transitions, zip(get_vars(transitions), to_split_vars + no_son_formula_vars))
        formula_no_son = And(formula_to_split, Exists(no_son_formula_vars, And(transitions_no_sons,
                                                                               split_by_formula_tagtag)))  # A(v) & Ev'[R(v,v')&B(v')]

        return formula_has_son, formula_no_son

    @classmethod
    def get_all_successors(cls, tr, src):
        s = Solver()
        src_values = map(lambda val: int(val), src)
        curr_tr = tr.substitute(src_values, 0)

        next_states = []
        curr_z3 = curr_tr.get_z3_formula()
        next_vector = curr_tr.get_var_vectors()[0]
        while s.check(curr_z3) == sat:
            model = s.model()
            assignment = [(var, model[var]) for var in next_vector]
            cube = [z3_val_to_int(val) for (var, val) in assignment]
            next_states.append(cube)
            # Not(l1 & ... &ln) = Not(l1) | ... | Not(ln)

            blocking_cube = Or(*[Not(var) if val == BoolVal('True') else var for (var, val) in assignment])
            curr_z3 = simplify(And(curr_z3, blocking_cube))
            print curr_z3

        return next_states

    @classmethod
    def parse_assignment(cls, assignment):
        pass


def test():
    vec = [Bool('x' + str(i)) for i in range(5)]
    new_vec = Z3Utils.duplicate_vars(vec)
    print vec
    print new_vec
    new_vec = Z3Utils.duplicate_vars(vec)
    print vec
    print new_vec
    vv = get_vars(And(*vec))
    for v in vv:
        print v
        print type(v)
        print v in vec


if __name__ == '__main__':
    #    test()
    x = [Bool('x' + str(i)) for i in range(5)]

    f = Exists([x[0]], And(x[0], x[1]))
    f2 = And(x[0], x[2], x[3], x[4], Or(x[0], x[2]))
    print get_vars(f)
    print get_vars(f2)

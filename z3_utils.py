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
    def get_exists_successors_in_formula(cls, abstract_targets, transitions):
        abstract_targets_formula = Or(*[abstract_target.get_descriptive_formula().get_z3_formula() for abstract_target in abstract_targets])
        prev_vars = abstract_targets[0].get_descriptive_formula().get_var_vectors()[0]

        new_vars = cls.duplicate_vars(prev_vars)

        split_by_formula_tag = substitute(abstract_targets_formula, zip(prev_vars, new_vars))  # B(v) [v<-v']

        transitions_has_sons = transitions.substitute(new_vars, 1, new_vars)
        exists_formula = Exists(new_vars, And(transitions_has_sons, split_by_formula_tag))  #Ev'[R(v,v')&B(v')]
        return FormulaWrapper(exists_formula, [prev_vars])

    @classmethod
    def get_split_formulas(cls, to_split, split_by, transitions):
        formula_to_split = to_split.get_descriptive_formula().get_z3_formula()

        v_vars = to_split.get_descriptive_formula().get_var_vectors()[0]
        exists_formula = cls.get_exists_successors_in_formula([split_by], transitions).get_z3_formula()
        formula_has_son = And(formula_to_split, exists_formula)  # A(v) & Ev'[R(v,v')&B(v')]

        not_exists_formula = cls.get_exists_successors_in_formula([split_by], transitions).get_z3_formula()
        formula_no_son = And(formula_to_split, not_exists_formula)  # A(v) & Ev'[R(v,v')&B(v')]

        return FormulaWrapper(formula_has_son, [v_vars]), FormulaWrapper(formula_no_son, [v_vars])

    @classmethod
    def int_vec_to_z3_bool_vec(cls, int_vec):
        return [BoolVal(True) if val == 1 else BoolVal(False) for val in int_vec]

    @classmethod
    def get_all_successors(cls, tr, src):
        s = Solver()
        src_values = map(lambda val: int(val), src)
        curr_tr = tr.substitute(Z3Utils.int_vec_to_z3_bool_vec(src_values))

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

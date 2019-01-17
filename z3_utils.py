from z3 import *


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
    r = set()

    def collect(f):
        if is_const(f):
            if f.decl().kind() == Z3_OP_UNINTERPRETED and not askey(f) in r:
                r.add(askey(f))
        else:
            for c in f.children():
                collect(c)

    collect(f)
    return map(lambda d: d.n, list(r))


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


def test():
    vec = [Bool('x' + str(i)) for i in range(5)]
    new_vec = Z3Utils.duplicate_vars(vec)
    print vec
    print new_vec
    new_vec = Z3Utils.duplicate_vars(vec)
    print vec
    print new_vec
    f = And(*vec)
    vv = get_vars(f)
    for v in vv:
        print v
        print type(v)
        print v in vec


if __name__ == '__main__':
    #    test()
    x = [Bool('x' + str(i)) for i in range(5)]

    f = Exists([x[0]], And(x[0], x[1]))
    print get_vars(f)

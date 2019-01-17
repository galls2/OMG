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
    return r


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

        split_by_vars = get_vars(formula_split_by)
        ## TODO finish this..
        has_son_formula_vars = cls.duplicate_vars(split_by_vars)


        formula_has_son = And(formula_to_split)


def test():
    vec = [Bool('x' + str(i)) for i in range(5)]
    new_vec = Z3Utils.duplicate_vars(vec)
    print vec
    print new_vec
    new_vec = Z3Utils.duplicate_vars(vec)
    print vec
    print new_vec
    f = And(*vec)
    vv = map(lambda d: d.n, list(get_vars(f)))
    for v in vv:
        print v
        print type(v)
        print v in vec


if __name__ == '__main__':
    test()

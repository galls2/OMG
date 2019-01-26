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


def get_assignment(model, vars):
    return [z3_val_to_int(model[var]) for var in vars]


class Z3Utils(object):
    copies_counter = 0

    def __init__(self):
        super(Z3Utils, self).__init__()

    @classmethod
    def duplicate_vars(cls, var_vector):
        new_var_vector = [Bool(var.decl().name() + '_' + str(cls.copies_counter)) for var in var_vector]
        cls.copies_counter += 1
        return new_var_vector

    '''
    Given [B1,...,Bn], R
    Returns (B1(v')|....Bn(v'), R(v,v'))
    '''

    @classmethod
    def _get_components_in_quantified(cls, abstract_targets, transitions):
        abstract_targets_formula = simplify(
            Or(*[target.get_descriptive_formula().get_z3_formula() for target in abstract_targets]))
        prev_vars = transitions.get_var_vectors()[0]
        new_vars = cls.duplicate_vars(prev_vars)
        split_by_formula_tag = substitute(abstract_targets_formula, zip(prev_vars, new_vars))  # B(v) [v<-v']
        transitions_has_sons = transitions.substitute(new_vars, 1, new_vars)
        return split_by_formula_tag, transitions_has_sons

    '''
    Returns Ev'[TR(v,v') & OR(targets(v'))]
    '''

    @classmethod
    def get_exists_successors_in_formula(cls, abstract_targets, transitions):
        split_by_formula_tag, transitions_has_sons = cls._get_components_in_quantified(abstract_targets, transitions)
        prev_vars, new_vars = transitions_has_sons.get_var_vectors()

        inner = And(transitions_has_sons.get_z3_formula(), split_by_formula_tag)
        exists_formula = simplify(Exists(new_vars, inner))
        return FormulaWrapper(exists_formula, [prev_vars])

    '''
    Returns Av'[TR(v,v') -> OR(targets(v'))]
    '''

    @classmethod
    def get_forall_successors_in_formula(cls, abstract_targets, transitions):
        split_by_formula_tag, transitions_has_sons = cls._get_components_in_quantified(abstract_targets, transitions)
        prev_vars, new_vars = transitions_has_sons.get_var_vectors()

        inner = Implies(transitions_has_sons.get_z3_formula(), split_by_formula_tag)
        forall_formula = simplify(ForAll(new_vars, inner))
        return FormulaWrapper(forall_formula, [prev_vars])

    @classmethod
    def get_split_formula(cls, to_split, split_by, transitions, quantified_part_getter):
        formula_to_split = to_split.get_descriptive_formula().get_z3_formula()

        v_vars = to_split.get_descriptive_formula().get_var_vectors()[0]
        quantified_formula = quantified_part_getter(split_by, transitions).get_z3_formula()
        pos_quantifier = simplify(And(formula_to_split, quantified_formula))  # A(v) & Qv'[phi(v,v')]

        negated_quantified_formula = Not(quantified_part_getter(split_by, transitions).get_z3_formula())
        neg_quantifier = simplify(And(formula_to_split, negated_quantified_formula))  # A(v) & ~Qv'[phi(v,v')]

        return FormulaWrapper(pos_quantifier, [v_vars]), FormulaWrapper(neg_quantifier, [v_vars])

    @classmethod
    def get_ex_split_formulas(cls, to_split, split_by, transitions):
        return cls.get_split_formula(to_split, split_by, transitions, cls.get_exists_successors_in_formula)

    @classmethod
    def get_ax_split_formulas(cls, to_split, split_by, transitions):
        return cls.get_split_formula(to_split, split_by, transitions, cls.get_forall_successors_in_formula)

    @classmethod
    def int_vec_to_z3(cls, int_vec):
        return [BoolVal(True) if val == 1 else BoolVal(False) for val in int_vec]

    @classmethod
    def get_all_successors(cls, tr, src):
        s = Solver()
        src_values = map(lambda val: int(val), src)
        curr_tr = tr.substitute(Z3Utils.int_vec_to_z3(src_values))

        next_states = []
        curr_z3 = curr_tr.get_z3_formula()
        next_vector = curr_tr.get_var_vectors()[0]
        while s.check(curr_z3) == sat:
            model = s.model()
            cube = get_assignment(model, next_vector)
            next_states.append(cube)
            # Not(l1 & ... &ln) = Not(l1) | ... | Not(ln)

            blocking_cube = Or(*[Not(var) if model[var] == BoolVal('True') else var for var in next_vector])
            curr_z3 = simplify(And(curr_z3, blocking_cube))
        #    print curr_z3

        return next_states

    @classmethod
    def has_successor_in_abstract(cls, concrete_state, abstract_witness):
        kripke = abstract_witness.get_kripke()
        transitions_from_concrete = kripke.get_tr_formula().substitute(Z3Utils.int_vec_to_z3(concrete_state)) \


        variables = transitions_from_concrete.get_var_vectors()[0]
        abs_formula = abstract_witness.get_descriptive_formula().substitute(variables, 0, variables) \
            .get_z3_formula()
        f = And(transitions_from_concrete.get_z3_formula(), abs_formula)

        s = Solver()
        if s.check(f) == unsat:
            return False

        return get_assignment(s.model(), variables)

    @classmethod
    def is_EE_closed(cls, to_close, close_with):
        kripke = to_close.get_kripke()
        transitions = kripke.get_tr_formula()
        src_vars, dst_vars = transitions.get_var_vectors()

        src = to_close.get_descriptive_formula().substitute(src_vars, 0, src_vars).get_z3_formula()
        dst_formulas = [closer.get_descriptive_formula().substitute(dst_vars, 0, dst_vars).get_z3_formula()
                        for closer in close_with]
        dst = Not(Or(*dst_formulas))

        closure_formula = And(src, transitions.get_z3_formula(), dst)
        s = Solver()
        res = s.check(closure_formula)

        if res == unsat:
            return True

        model = s.model()
        return get_assignment(model, src_vars), get_assignment(model, dst_vars)


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

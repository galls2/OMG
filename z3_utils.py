import itertools
import logging

from z3 import *

from common import State, time_me
from formula_wrapper import FormulaWrapper
from var_manager import VarManager

logger = logging.getLogger('OMG')


class EEClosureViolation(object):
    def __init__(self, conc_src, conc_dst):
        self.conc_src = conc_src
        self.conc_dst = conc_dst


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
    return 1 if z3_val.sexpr() == 'true' else 0


def get_assignments(model, variables):
    partial_assignment = [([z3_val_to_int(model[var])] if model[var] is not None else [0, 1]) for var in variables]
    return [list(comb) for comb in itertools.product(*partial_assignment)]


def get_states(model, variables):
    res_list = get_assignments(model, variables)
    return [State.from_int_list(raw_state) for raw_state in res_list]


class Z3Utils(object):
    copies_counter = 0

    def __init__(self):
        super(Z3Utils, self).__init__()

    '''
    Given [B1,...,Bn], R
    Returns (B1(v')|....Bn(v'), R(v,v'))
    '''

    @classmethod
    def _get_components_in_quantified(cls, abstract_targets, transitions):
        abstract_targets_formula = FormulaWrapper.Or([target.get_descriptive_formula() for target in abstract_targets])
        new_vars = VarManager.duplicate_vars(transitions.get_var_vectors()[0])
        split_by_formula_tag = abstract_targets_formula.substitute(new_vars, 0, new_vars)  # B(v) [v<-v']
        transitions_has_sons = transitions.substitute(new_vars, 1, new_vars)  # R(u,v) [v<-v']
        return split_by_formula_tag, transitions_has_sons

    '''
    Returns Ev'[TR(v,v') & OR(targets(v'))]
    '''

    @classmethod
    def get_exists_successors_in_formula(cls, abstract_targets, transitions):
        split_by_formula_tag, transitions_has_sons = cls._get_components_in_quantified(abstract_targets, transitions)
        prev_vars, new_vars = transitions_has_sons.get_var_vectors()
        qe_policy = abstract_targets[0].get_kripke().get_qe_policy()

        inner = And(transitions_has_sons.get_z3_formula(), split_by_formula_tag.get_z3_formula())
        exists_formula = cls.apply_qe(simplify(Exists(new_vars, inner)), qe_policy)

        return FormulaWrapper(exists_formula, [prev_vars])

    '''
    Returns Av'[TR(v,v') -> OR(targets(v'))]
    '''

    @classmethod
    def get_forall_successors_in_formula(cls, abstract_targets, transitions):
        split_by_formula_tag, transitions_has_sons = cls._get_components_in_quantified(abstract_targets, transitions)
        prev_vars, new_vars = transitions_has_sons.get_var_vectors()
        qe_policy = abstract_targets[0].get_kripke().get_qe_policy()

        inner = Implies(transitions_has_sons.get_z3_formula(), split_by_formula_tag.get_z3_formula())
        forall_formula = cls.apply_qe(simplify(ForAll(new_vars, inner)), qe_policy)

        return FormulaWrapper(forall_formula, [prev_vars])

    @classmethod
    def get_split_formula(cls, to_split, split_by, transitions, quantified_part_getter):
        formula_to_split_pos = to_split.get_descriptive_formula()
        quantifier_wrapper_pos = quantified_part_getter(split_by, transitions)
        quantified_formula = quantifier_wrapper_pos.get_z3_formula()
        # pos_quantifier = simplify(And(formula_to_split_pos.get_z3_formula(), quantified_formula))  # A(v) & Qv'[phi(v,v')]

        #    formula_to_split_neg = to_split.get_descriptive_formula()
        #   quantifier_wrapper_neg = quantified_part_getter(split_by, transitions)
        #   negated_quantified_formula = Not(quantifier_wrapper_neg.get_z3_formula())
        #   neg_quantifier = simplify( And(formula_to_split_neg.get_z3_formula(), negated_quantified_formula))  # A(v) & ~Qv'[phi(v,v')]

        v_vars = to_split.get_descriptive_formula().get_var_vectors()[0]
        # return FormulaWrapper(pos_quantifier, [v_vars]), FormulaWrapper(neg_quantifier, [v_vars])
        return formula_to_split_pos.get_z3_formula(), quantified_formula, v_vars

    @classmethod
    def get_ex_split_formulas(cls, to_split, split_by, transitions):
        return cls.get_split_formula(to_split, split_by, transitions, cls.get_exists_successors_in_formula)

    @classmethod
    def int_vec_to_z3(cls, int_vec):
        return [BoolVal(True) if val == 1 else BoolVal(False) for val in int_vec]

    @classmethod
    def get_ax_split_formulas(cls, to_split, split_by, transitions):
        return cls.get_split_formula(to_split, split_by, transitions, cls.get_forall_successors_in_formula)

    @classmethod
    def get_all_next_assignments(cls, tr, src_values):
        s = Solver()
        curr_tr = tr.substitute(Z3Utils.int_vec_to_z3(src_values))

        next_states = []
        curr_z3 = curr_tr.get_z3_formula()
        next_vector = curr_tr.get_var_vectors()[0]
        while s.check(curr_z3) == sat:
            model = s.model()
            cubes = get_assignments(model, next_vector)

            next_states += cubes
            # Not(l1 & ... &ln) = Not(l1) | ... | Not(ln)

            blocking_cube = Or(
                *[Not(var) if z3_val_to_int(model[var]) is 1 else var
                  for var in next_vector if model[var] is not None])
            curr_z3 = simplify(And(curr_z3, blocking_cube))
        #    print curr_z3
        return next_states

    @classmethod
    def get_all_successors(cls, tr, src):
        src_values = src.values()
        next_assignments = cls.get_all_next_assignments(tr, src_values)
        return [State.from_int_list(cube) for cube in next_assignments]

    @classmethod
    def concrete_transition_to_abstract(cls, nodes_from, abstract_witness):
        kripke = abstract_witness.get_kripke()
        tr = kripke.get_tr_formula()

        def sub_src(tr, src_node):
            z3_vec = Z3Utils.int_vec_to_z3(src_node.concrete_label.data)
            return tr.substitute(z3_vec)

        tr_from_concs = [sub_src(tr, node) for node in nodes_from]

        variables = tr_from_concs[0].get_var_vectors()[0]
        abs_formula = abstract_witness.get_descriptive_formula().substitute(variables, 0, variables).get_z3_formula()

        flags = [Bool('f' + str(i)) for i in range(len(tr_from_concs))]

        tr_flagged = [Implies(flags[i], tr_from_concs[i].get_z3_formula()) for i in range(len(tr_from_concs))]
        all_tr_flagged = And(*tr_flagged)

        f = And(all_tr_flagged, abs_formula)

        s = Solver()
        s.add(f)
        s.push()

        for i in range(len(flags)):
            flag = flags[i]
            sat_res = s.check(flag)
            if sat_res == sat:
                model = s.model()
                return nodes_from[i], get_states(model, variables)[0]
        return False

    @classmethod
    def is_AE_closed(cls, to_close, close_with):
        kripke = to_close.get_kripke()
        transitions = kripke.get_tr_formula()
        src_vars, dst_vars = transitions.get_var_vectors()

        src = to_close.get_descriptive_formula().substitute(src_vars, 0, src_vars).get_z3_formula()
        dst_formulas = [closer.get_descriptive_formula().substitute(dst_vars, 0, dst_vars).get_z3_formula()
                        for closer in close_with]
        dst = Not(Or(*dst_formulas))

        closure_formula = And(src, ForAll(dst_vars, Implies(transitions.get_z3_formula(), dst)))

        s = Solver()
        res = s.check(closure_formula)

        if res == unsat:
            return True

        model = s.model()
        ass = get_states(model, src_vars)[0]
        return ass

    @classmethod
    def is_EE_closed(cls, to_close, close_with):
        kripke = to_close.get_kripke()
        transitions = kripke.get_tr_formula()
        src_vars, dst_vars = transitions.get_var_vectors()

        src = to_close.get_descriptive_formula().substitute(src_vars, 0, src_vars).get_z3_formula()
        dst_formulas = [closer.get_descriptive_formula().substitute(dst_vars, 0, dst_vars).get_z3_formula()
                        for closer in close_with]
        dst = Not(Or(*dst_formulas))

        closure_formula = simplify(And(src, transitions.get_z3_formula(), dst))
        #   logger.debug('Check start')
        s = Solver()
        res = s.check(closure_formula)
        #  logger.debug('check end.')
        if res == unsat:
            return True

        model = s.model()
        #  logger.debug(str(model))
        return EEClosureViolation(get_states(model, src_vars)[0], get_states(model, dst_vars)[0])

    @classmethod
    def apply_qe(cls, formula, qe_policy):
        if qe_policy == 'no-qe':
            return formula
        #  formula = Tactic('ctx-solver-simplify')(formula).as_expr()
        return Tactic(qe_policy)(formula).as_expr()

    @classmethod
    def combine_ltr_with_bad_formulas(cls, ltr_formula, output_formulas, max_var_ltr):
        prev_output_vars = [Bool(str(max_var_ltr + i)) for i in range(len(output_formulas))]
        next_output_vars = [Bool(str(max_var_ltr + len(output_formulas) + i)) for i in range(len(output_formulas))]

        prev_latch_vars, next_latch_vars = ltr_formula.get_var_vectors()

        # ltr is over(l,l'). We want our final formula over (v,v') where v=l,o and v'=l',o'

        prev_var_vector = prev_latch_vars + prev_output_vars
        next_var_vector = next_latch_vars + next_output_vars

        var_vectors = [prev_var_vector, next_var_vector]

        substituted_output_z3_formulas = [output_formulas[i]
                                              .substitute([next_output_vars[i]], 1, [next_output_vars[i]])
                                              .substitute(next_latch_vars, 0, next_latch_vars)
                                              .get_z3_formula()
                                          for i in range(len(output_formulas))]

        tr_formula = And(ltr_formula.get_z3_formula(), *substituted_output_z3_formulas)

        return FormulaWrapper(tr_formula, var_vectors)

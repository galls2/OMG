import itertools
import logging

from z3 import *

from common import z3_val_to_int, EEClosureViolation
from qbf_solver import Z3QbfSolver, DepQbfSimpleSolver, QDPLL_QTYPE_EXISTS, QDPLL_QTYPE_FORALL, QbfSolverCtor
from state import State
from formula_wrapper import FormulaWrapper, QBF
from var_manager import VarManager

logger = logging.getLogger('OMG')


def get_assignments(model, variables):
    partial_assignment = (([z3_val_to_int(model[var])] if model[var] is not None else [0, 1]) for var in variables)
    return (list(comb) for comb in itertools.product(*partial_assignment))


def get_states(model, variables, kripke):
    res_list = get_assignments(model, variables)
    return (State.from_int_list(raw_state, kripke.get_var_vector(), kripke) for raw_state in res_list)


class Z3Utils(object):
    QbfSolverCtor = Z3QbfSolver

    def __init__(self):
        super(Z3Utils, self).__init__()

    '''
    Given [B1,...,Bn], R
    Returns (B1(v')|....Bn(v'), R(v,v'))
    '''

    @classmethod
    def _get_components_in_quantified(cls, abs_targets, tr):
        untagged_in_vec, tag_input_vector = tr.get_input_vectors()
        new_state_vars = VarManager.duplicate_vars(tr.get_var_vectors()[0])
        new_tag_in_vec = VarManager.duplicate_vars(tag_input_vector)
        new_untag_in_vec = VarManager.duplicate_vars(untagged_in_vec)

        abs_targets_sub = [target.get_descriptive_formula()
                               .substitute_inputs(new_tag_in_vec, 0)
                               .substitute(new_state_vars, 0)
                               .renew_quantifiers() for target in abs_targets]
        abs_or = Or(*[_t.get_qbf().get_prop() for _t in abs_targets_sub])

        new_q_list = [_v for _t in abs_targets_sub for _v in _t.get_qbf().get_q_list()]

        split_by_formula_tag = FormulaWrapper(QBF(abs_or, new_q_list), [new_state_vars], [new_tag_in_vec])
        ## RENAME QUNATIFIED HERE
        transitions_has_sons = tr.substitute(new_state_vars, 1) \
            .substitute_inputs(new_untag_in_vec, 0) \
            .substitute_inputs(new_tag_in_vec, 1)  # R(u,v) [v<-v']
        return split_by_formula_tag, transitions_has_sons

    '''
    Returns Ev'[TR(v,v') & OR(targets(v'))]
    '''

    @classmethod
    def get_exists_successors_in_formula(cls, abstract_targets, transitions):
        kripke = abstract_targets[0].get_kripke()
        qe_policy = kripke.get_qe_policy()

        split_by, tr = cls._get_components_in_quantified(abstract_targets, transitions)
        prev_vars, new_vars = tr.get_var_vectors()
        in_vec, quantified_input = tr.get_input_vectors()

        inner = And(tr.get_qbf().get_prop(), split_by.get_qbf().get_prop())
        q_list = [(-1, new_vars + in_vec + quantified_input)] + split_by.get_qbf().get_q_list() + tr.get_qbf().get_q_list()
        #   exists_formula = cls.apply_qe(simplify(Exists(new_vars + in_vec, inner)), qe_policy)

        return FormulaWrapper(QBF(inner, q_list), [prev_vars], [in_vec])

    '''
    Returns Av'[TR(v,v') -> OR(targets(v'))]
    '''

    @classmethod
    def get_forall_successors_in_formula(cls, abstract_targets, transitions):
        kripke = abstract_targets[0].get_kripke()
        qe_policy = kripke.get_qe_policy()

        split_by, tr = cls._get_components_in_quantified(abstract_targets, transitions)
        prev_vars, new_vars = tr.get_var_vectors()
        in_vec, quantified_input = tr.get_input_vectors()

        neg_tr = tr.negate()
        inner = Or(neg_tr.get_qbf().get_prop(), split_by.get_qbf().get_prop())
        # forall_formula = cls.apply_qe(simplify(ForAll(new_vars + in_vec, innektr)), qe_policy)
        q_list = [(QDPLL_QTYPE_FORALL, new_vars + in_vec)] + \
                 [(QDPLL_QTYPE_EXISTS, quantified_input)] + \
                 split_by.get_qbf().get_q_list() + neg_tr.get_qbf().get_q_list() # quantification over q_in may be false

        return FormulaWrapper(QBF(inner, q_list), [prev_vars], [in_vec])

    @classmethod
    def get_split_formula(cls, to_split, split_by, transitions, quantified_part_getter):
        input_vars = transitions.get_input_vectors()[0]

        pos_input = VarManager.duplicate_vars(input_vars)
        q_part_pos = quantified_part_getter(split_by, transitions)
        pos_state_vars = q_part_pos.get_var_vectors()[0]
        to_split_pos = to_split.get_descriptive_formula().substitute(pos_state_vars, 0).substitute_inputs(pos_input, 0)
        inner_pos = And(to_split_pos.get_qbf().get_prop(), q_part_pos.get_qbf().get_prop())
        q_list_pos = to_split_pos.get_qbf().get_q_list() + q_part_pos.get_qbf().get_q_list()
        pos_qbf = QBF(inner_pos, q_list_pos)
        pos = FormulaWrapper(pos_qbf, [pos_state_vars], [pos_input])

        neg_input = VarManager.duplicate_vars(input_vars)
        unnegated_q_part = quantified_part_getter(split_by, transitions)
        q_part_neg = unnegated_q_part.negate()
        neg_state_vars = q_part_neg.get_var_vectors()[0]
        to_split_neg = to_split.get_descriptive_formula().substitute(neg_state_vars, 0).substitute_inputs(neg_input, 0)
        inner_neg = And(to_split_neg.get_qbf().get_prop(), q_part_neg.get_qbf().get_prop())
        q_list_neg = to_split_neg.get_qbf().get_q_list() + q_part_neg.get_qbf().get_q_list()
        neg_qbf = QBF(inner_neg, q_list_neg)
        neg = FormulaWrapper(neg_qbf, [neg_state_vars], [neg_input])


        logger.debug("ASSERTING WELL NAMEDNESS")
        assert pos.well_named()
        assert neg.well_named()

        return pos, neg, (to_split_pos, pos)

    @classmethod
    def get_ex_split_formulas(cls, to_split, split_by, transitions):
        return cls.get_split_formula(to_split, split_by, transitions, cls.get_exists_successors_in_formula)

    @classmethod
    def get_ax_split_formulas(cls, to_split, split_by, transitions):
        return cls.get_split_formula(to_split, split_by, transitions, cls.get_forall_successors_in_formula)

    @classmethod
    def all_sat(cls, formula_wrap):
        s = Solver()
        assignments = []
        s.add(formula_wrap.get_qbf().to_z3())

        all_vars = [_v for v_list in formula_wrap.get_var_vectors() for _v in v_list]
        while s.check() == sat:
            model = s.model()
            cubes = list(get_assignments(model, all_vars))

            assignments += cubes
            # Not(l1 & ... &ln) = Not(l1) | ... | Not(ln)

            blocking_cube = Or(
                *[Not(var) if z3_val_to_int(model[var]) is 1 else var
                  for var in all_vars if model[var] is not None])
            s.add(blocking_cube)
        return assignments

    @classmethod
    def get_all_successors(cls, tr, state):
        assigned_tr = tr.assign_state(state)
        next_assignments = cls.all_sat(assigned_tr)
        _vars = state.formula_wrapper.get_var_vectors()[0]
        return [State.from_int_list(cube, _vars, state.kripke) for cube in next_assignments]

    @classmethod
    def concrete_transition_to_abstract(cls, nodes_from, abstract_witness):
        kripke = abstract_witness.get_kripke()
        tr = kripke.get_tr_formula()

        def sub_src(_tr, src_node):
            return _tr.assign_state(src_node.concrete_label)

        tr_from_concs = [sub_src(tr, node) for node in nodes_from]

        dst_vars = tr_from_concs[0].get_var_vectors()[0]
        in_tag = tr.get_input_vectors()[1]
        abs_formula = abstract_witness.get_descriptive_formula().substitute(dst_vars, 0).substitute_inputs(in_tag, 0)

        n_flags = len(tr_from_concs)
        flags = [Bool('f' + str(i)) for i in xrange(n_flags)]

        tr_flagged = [Or(Not(flags[i]), tr_from_concs[i].get_qbf().get_prop()) for i in xrange(n_flags)]
        all_tr_flagged = simplify(And(*tr_flagged))

        f_inner = simplify(And(all_tr_flagged, abs_formula.get_qbf().get_prop()))
        q_list = abs_formula.get_qbf().get_q_list()
        f_qbf = QBF(f_inner, q_list)
        f = FormulaWrapper(f_qbf, [dst_vars], tr.get_input_vectors())

        i, model = QbfSolverCtor().incremental_solve_flags(f, flags, sat)
        if i is False:
            return False
        return nodes_from[i], next(get_states(model, dst_vars, kripke))

    @classmethod
    def is_AE_closed(cls, to_close, close_with):
        kripke = to_close.get_kripke()
        transitions = kripke.get_tr_formula()
        src_vars, dst_vars = transitions.get_var_vectors()
        input_vars, input_tag_vars = transitions.get_input_vectors()

        src_wrapper = to_close.get_descriptive_formula().substitute(src_vars, 0).substitute_inputs(input_vars, 0)
        src_qbf = src_wrapper.get_qbf().renew_quantifiers()

        dst_formulas = [
            closer.get_descriptive_formula()
                .substitute(dst_vars, 0)
                .substitute_inputs(input_tag_vars, 0)
                .get_qbf()
                .negate()
            for closer in close_with]
        dst = QBF(And(*[_d.get_prop() for _d in dst_formulas]), [_v for _t in dst_formulas for _v in _t.get_q_list()])

        tr_qbf = transitions.get_qbf()
        inner_prop = simplify(And(src_qbf.get_prop(), Or(Not(tr_qbf.get_prop()), dst.get_prop())))
        q_list = src_qbf.get_q_list() + [(QDPLL_QTYPE_FORALL, dst_vars)] + tr_qbf.get_q_list() + dst.get_q_list()

        query = FormulaWrapper(QBF(inner_prop, q_list), [src_vars], [input_vars])


        solver = QbfSolverCtor()
        res, model = solver.solve(query)
        #  logger.debug('check end.')
        if res == unsat:
            return True

        ass = next(get_states(model, src_vars, kripke))
        return ass

    @classmethod
    def is_EE_closed(cls, to_close, close_with):
        kripke = to_close.get_kripke()
        transitions = kripke.get_tr_formula()
        src_vars, dst_vars = transitions.get_var_vectors()
        input_vars, input_tag_vars = transitions.get_input_vectors()

        src_wrapper = to_close.get_descriptive_formula().substitute(src_vars, 0).substitute_inputs(input_vars, 0)
        src_qbf_old_q = src_wrapper.get_qbf()
        src_qbf = src_qbf_old_q.renew_quantifiers()

        dst_formulas = [
            closer.get_descriptive_formula()
                .substitute(dst_vars, 0)
                .substitute_inputs(input_tag_vars, 0)
                .get_qbf()
                .negate()
            for closer in close_with]
        dst = QBF(And(*[_d.get_prop() for _d in dst_formulas]), [_v for _t in dst_formulas for _v in _t.get_q_list()])

        tr_qbf = transitions.get_qbf()
        inner_prop = simplify(And(src_qbf.get_prop(), tr_qbf.get_prop(), dst.get_prop()))
        q_list = src_qbf.get_q_list() + dst.get_q_list() + tr_qbf.get_q_list()

        query = FormulaWrapper(QBF(inner_prop, q_list), [src_vars, dst_vars], [input_vars])
        #   logger.debug('Check start')


        solver = QbfSolverCtor()
        res, model = solver.solve(query)
        #  logger.debug('check end.')
        if res == unsat:
            return True

        '''
        for s in get_states(model, src_vars, kripke):
            f = to_close.get_descriptive_formula().assign_state(s).is_sat()
            if not f:
                print 'EE-closure is all messed up!'
                print 'The src is supposed to be in ' + to_close.get_debug_name()
                print 'But is classified to ' + to_close.get_classification_node()._classifier.classify(
                    s).get_debug_name()
                print 'BUG'
                get_states(model, src_vars, kripke)
                solver = DepQbfSimpleSolver()
                res, model = solver.solve(query)
                assert False
        '''
        return EEClosureViolation(next(get_states(model, src_vars, kripke)), next(get_states(model, dst_vars, kripke)))

    @classmethod
    def apply_qe(cls, formula, qe_policy):
        if qe_policy == 'no-qe':
            return formula
        #  formula = Tactic('ctx-solver-simplify')(formula).as_expr()
        return Tactic(qe_policy)(formula).as_expr()

    '''
    @classmethod
    def combine_ltr_with_bad_formulas(cls, ltr_formula, output_formulas, max_var_ltr):
        prev_output_vars = [Bool(str(max_var_ltr + i)) for i in xrange(len(output_formulas))]
        next_output_vars = [Bool(str(max_var_ltr + len(output_formulas) + i)) for i in xrange(len(output_formulas))]

        prev_latch_vars, next_latch_vars = ltr_formula.get_var_vectors()

        # ltr is over(l,l'). We want our final formula over (v,v') where v=l,o and v'=l',o'

        prev_var_vector = prev_latch_vars + prev_output_vars
        next_var_vector = next_latch_vars + next_output_vars

        var_vectors = [prev_var_vector, next_var_vector]

        substituted_output_z3_formulas = [output_formulas[i]
                                              .substitute([next_output_vars[i]], 1, [next_output_vars[i]])
                                              .substitute(next_latch_vars, 0, next_latch_vars)
                                              .get_z3()
                                          for i in xrange(len(output_formulas))]

        tr_formula = And(ltr_formula.get_z3(), *substituted_output_z3_formulas)

        return FormulaWrapper(tr_formula, var_vectors)
    '''

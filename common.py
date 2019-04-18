import cProfile, pstats, StringIO
import functools
import logging
import time

from z3 import BoolVal, Not, And, Z3_OP_UNINTERPRETED, AstRef, Bool, Or

logger = logging.getLogger('OMG')




# -----------------------------------------------------------------------------------------------------
# PROFILING
# -----------------------------------------------------------------------------------------------------
def profiler(func, params):
    pr = cProfile.Profile()
    pr.enable()
    res = func(*params)
    pr.disable()
    s = StringIO.StringIO()
    ps = pstats.Stats(pr, stream=s).sort_stats('cumtime')
    ps.print_stats()
    print s.getvalue()
    ps.print_callers(1.0, '*')
    ps.print_callees()
    return res


def time_me(measuree, args, message):
    start = time.time()
    res = measuree(*args)
    end = time.time()
    logger.info(message + ': ' + str(end - start))
    return res


def time_me_c(measuree, args):
    start = time.time()
    res = measuree(*args)
    end = time.time()
    return end - start, res


# -----------------------------------------------------------------------------------------------------
# ABSTRACT STATES TO INTS
# -----------------------------------------------------------------------------------------------------
def abs_to_int(_abs):
    return 1 << _abs.get_id()


def abstract_states_to_int(abstract_states):
    return sum([abs_to_int(_abs) for _abs in abstract_states])


def subset_abs(small, big):
    return (small & big) == small


def in_abs(_el, abs_set):
    return abs_to_int(_el) & abs_set


def add_elems_to_abs(_elements, abs_set):
    return abstract_states_to_int(_elements) | abs_set


def remove_elems(_elements, remove_from):
    return (~abstract_states_to_int(_elements)) & remove_from


# -----------------------------------------------------------------------------------------------------
# Z3 VALUE CONVERSIONS
# -----------------------------------------------------------------------------------------------------
def z3_val_to_int(z3_val):
    return 1 if z3_val.sexpr() == 'true' else 0


def z3_val_to_bool(z3_val):
    return True if z3_val.sexpr() == 'true' else False


def int_vec_to_z3(int_vec):
    return [BoolVal(True) if val == 1 else BoolVal(False) for val in int_vec]


def int_list_to_cube(int_list, _vars):
    _l = len(int_list)
    return And(*[_vars[i] if int_list[i] == 1 else Not(_vars[i]) for i in xrange(_l)])


# -----------------------------------------------------------------------------------------------------
# AUXILIARY CLASSES
# -----------------------------------------------------------------------------------------------------
class MyModel(object):
    def __init__(self, assignment):
        self.assignment = assignment

    def __getitem__(self, item):
        return self.assignment.get(item)

    def __setitem__(self, key, value):
        self.assignment[key] = value
        return self

    def unassign(self, var):
        del self.assignment[var]
        return self

    def blocking_clause(self):
        return Or(*[Not(var) if self.assignment[var] == BoolVal(True) else var for var in self.assignment.keys()])

class ConcretizationResult(object):
    def __init__(self, src=None, dst=None):
        self.src_node = src
        self.dst_conc = dst

    def exists(self):
        return not (self.src_node is None and self.dst_conc is None)


class EEClosureViolation(object):
    def __init__(self, conc_src, conc_dst):
        self.conc_src = conc_src
        self.conc_dst = conc_dst


# -----------------------------------------------------------------------------------------------------
# FUNCTIONAL PROGRAMMING
# -----------------------------------------------------------------------------------------------------

foldr = lambda func, acc, xs: functools.reduce(lambda x, y: func(y, x), xs[::-1], acc)



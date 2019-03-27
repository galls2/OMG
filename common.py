import cProfile, pstats, StringIO
import logging
import time

from z3 import BoolVal, Not, And

logger = logging.getLogger('OMG')


def profiler(func, params):
    pr = cProfile.Profile()
    pr.enable()
    res = func(*params)
    pr.disable()
    s = StringIO.StringIO()
    ps = pstats.Stats(pr, stream=s).sort_stats('cumtime')
    ps.print_stats()
    print s.getvalue()
    ps.print_callers(1.0, '*' )
    ps.print_callees()
    return res


def z3_val_to_int(z3_val):
    return 1 if z3_val.sexpr() == 'true' else 0


def z3_val_to_bool(z3_val):
    return True if z3_val.sexpr() == 'true' else False


def int_vec_to_z3(int_vec):
    return [BoolVal(True) if val == 1 else BoolVal(False) for val in int_vec]


def int_list_to_cube(int_list, vars):
    return And(*[vars[i] if int_list[i] == 1 else Not(vars[i]) for i in range(len(int_list))])


class ConcretizationResult(object):
    def __init__(self, src=None, dst=None):
        self.src_node = src
        self.dst_conc = dst

    def exists(self):
        return not (self.src_node is None and self.dst_conc is None)


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

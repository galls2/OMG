import logging
import time

logger = logging.getLogger('OMG')


class State(object):
    def __init__(self, data):
        self.data = data

    def __getitem__(self, item):
        return self.data[item]

    def __setitem__(self, key, value):
        self.data[key] = value
        return self

    def values(self):
        return self.data

    def __eq__(self, o):
        return self.data == o.data

    def __ne__(self, o):
        return not self == o

    def __str__(self):
        return str(self.data)
    '''
    @staticmethod
    def from_int_list(int_list):
        return State(BitVector(bitlist=int_list))
    '''

    def __hash__(self):
        return hash(tuple(self.data))

    @staticmethod
    def from_int_list(int_list):
        return State(int_list)


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

def time_me_c(measuree, args, message):
    start = time.time()
    res = measuree(*args)
    end = time.time()
    return end-start, res
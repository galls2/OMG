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

    def __hash__(self):
        return super(State, self).__hash__()

    def __ne__(self, o):
        return not self == o

    def __str__(self):
        return str(self.data)


class ConcretizationResult(object):
    def __init__(self, src=None, dst=None):
        self.src_node = src
        self.dst_conc = dst

    def exists(self):
        return not (self.src_node is None and self.dst_conc is None)

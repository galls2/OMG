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

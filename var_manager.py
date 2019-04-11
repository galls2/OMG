from z3 import Bool


def var_name(full_name):
    return full_name.split('_')[0]


def version(full_name):
    parts = full_name.split('_')
    return 0 if len(parts) == 1 else int(parts[-1])


class VarManager(object):
    copies_counter = 0
    abstract_state_counter = 0

    def __init__(self):
        super(VarManager, self).__init__()

    @classmethod
    def new_var_name(cls, var):
        full_name = var.decl().name()
        return var_name(full_name) + '_' + str(cls.copies_counter)

    @classmethod
    def new_abs_name(cls):
        new_name = int(cls.abstract_state_counter)
        cls.abstract_state_counter += 1
        return new_name

    @classmethod
    def duplicate_vars(cls, var_vector):
        new_var_vector = [Bool(cls.new_var_name(var)) for var in var_vector]
        cls.copies_counter += 1
        return new_var_vector

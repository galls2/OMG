def par(text):
    return '(' + text + ')'


def remove_spaces_from_edges(text):
    text = text[next(i for i in range(len(text)) if text[i] != ' '):]
    text = text[:-1*next(i for i in range(len(text)) if text[len(text)-1-i] != ' ')]
    return text


def remove_spaces(text):
    return ''.join([ch for ch in text if ch != ' '])


def is_balanced_brackets(text):
    values = {"(": 1, ")": -1}
    contribution = [values[c] if c in values else 0 for c in text]
    counts = list(accumulate(contribution))

    return all(c >= 0 for c in counts) and counts[-1] == 0


def accumulate(list_num, addition=0):
    return [] if list_num == [] else \
        [list_num[0] + addition] + accumulate(list_num[1:], addition + list_num[0])


def split_components(f):

    '''
    Written by Tal Shinkar. Many thanks.
    '''
    values = {"(": 1, ")": -1}
    contribution = [values[c] if c in values else 0 for c in f]
    counts = list(accumulate(contribution))
    assert (all(c >= 0 for c in counts) and counts[-1] == 0)  # f is balanced

    lsplits = [i + 1 for i in range(len(counts) - 1) if counts[i] == 0 and counts[i + 1] != 0]
    rsplits = [i + 2 for i in range(len(counts) - 1) if counts[i] != 0 and counts[i + 1] == 0]
    splits = [0] + sorted(lsplits + rsplits) + [len(counts)]

    cuts = [f[splits[i]:splits[i + 1]] for i in range(len(splits) - 1)]
    cuts_no_blanks = [c for c in cuts if c != '' and not all(ch == ' ' for ch in c)]

    for i in range(len(cuts_no_blanks)):
        if cuts_no_blanks[i][0] != '(':
            cuts_no_blanks[i:i + 1] = [c for c in cuts_no_blanks[i].split(' ') if c != '']
    return cuts_no_blanks


class CtlFormula(object):
    """docstring for CtlFormula."""

    def __init__(self, node_data, operands):
        super(CtlFormula, self).__init__()
        self._node_data = node_data
        self._operands = operands
        self.unary_logical_operators = ['!', '~']
        self.unary_temporal_operators = ['EX', 'AX', 'AG', 'EG', 'AF', 'EF']
        self.unary_operators = self.unary_logical_operators + self.unary_temporal_operators
        self.binary_logical_operators = ['->', '&', '|']
        self.binary_temporal_operators = ['AV', 'EV', 'AU', 'EU', 'AR', 'ER']
        self.binary_operators = self.binary_logical_operators + self.binary_temporal_operators
        self.allowed_operators = self.unary_operators + self.binary_operators

    def str_math(self):
        if not self._operands:  # list is empty.
            return str(self._node_data)
        if self._node_data in self.unary_operators:
            first_operand = self._operands[0].str_math()
            return self._node_data + par(first_operand)
        else:
            first_operand = self._operands[0].str_math()
            second_operand = self._operands[1].str_math()
            if self._node_data in self.binary_temporal_operators:
                return self._node_data[0] + par(first_operand) + self._node_data[1] + par(second_operand)
            if self._node_data in self.binary_logical_operators:
                return par(first_operand) + str(self._node_data) + par(second_operand)

    def __str__(self):
        return par(str(self._node_data) + ' '.join([str(op) for op in self._operands]))

    def is_atomic_proposition(self):
        return not self._operands

    def get_arity(self):
        return len(self._operands)

    def get_operands(self):
        return self._operands

    def get_main_connective(self):
        return self._node_data

class CtlParser(object):
    """
    Format:
    CTL -> (AP)
    CTL -> (unary_connective, CTL)
    CTL -> (binary_connective, CTL, CTL)
    """

    def __init__(self):
        super(CtlParser, self).__init__()
        self._unary_logical_operators = ['!', '~']
        self._unary_temporal_operators = ['EX', 'AX', 'AG', 'EG', 'AF', 'EF']
        self._unary_operators = self._unary_logical_operators + self._unary_temporal_operators
        self._binary_logical_operators = ['->', '&', '|']
        self._binary_temporal_operators = ['AV', 'EV', 'AU', 'EU', 'AR', 'ER']
        self._binary_operators = self._binary_logical_operators + self._binary_temporal_operators
        self._allowed_operators = self._unary_operators + self._binary_operators

    def parse_smtlib_format(self, input_formula):
        if input_formula[0] != '(' or input_formula[-1] != ')':
            raise Exception('Error in parsing CTL formula ' + input_formula + ': brackets')
        input_formula = input_formula[1:-1]
        parts = split_components(input_formula)
        if not parts:
            raise Exception('Error in parsing CTL formula ' + input_formula + ': brackets')

        main_operator = parts[0]
        input_operands = parts[1:]
        if not input_operands:
            return CtlFormula(parts[0], [])
        #    print main_operator +str(len(main_operator))
        if main_operator not in self._allowed_operators:
            raise Exception('Error in parsing CTL formula ' + input_formula + ': unrecognized operator')
        if (main_operator in self._unary_operators) and (len(input_operands) != 1):
            raise Exception('Error in parsing CTL formula ' + input_formula + ': unary operator')
        if (main_operator in self._binary_operators) and (len(input_operands) != 2):
            raise Exception('Error in parsing CTL formula ' + input_formula + ': binary operator')
        parsed_operands = [self.parse_smtlib_format(sub_part) for sub_part in input_operands]
        return CtlFormula(main_operator, parsed_operands)

    def parse_math_format(self, input_formula):
        #        print 'ENTERING WITH: '+input_formula

       input_formula = remove_spaces_from_edges(input_formula)

        while input_formula[0] == '(' and input_formula[-1] == ')' and is_balanced_brackets(input_formula[1:-1]):
            #        print 'NOW :'+input_formula
            input_formula = input_formula[1:-1]
            remove_spaces_from_edges(input_formula)

        if input_formula[:2] in self._unary_temporal_operators:
            return CtlFormula(input_formula[:2], [self.parse_math_format(input_formula[2:])])
        parts = split_components(input_formula)
        # AP, binary temporal or binary logical
        if input_formula[0] in ['A', 'E']:
            path_quantifier = input_formula[0]
            temporal_operator = parts[2][0]
            main_connective = path_quantifier + temporal_operator
            first_operand = self.parse_math_format(parts[1])
            second_operand = self.parse_math_format(' '.join(parts[3:]))
            return CtlFormula(main_connective, [first_operand, second_operand])
        #    print parts
        if len(parts) > 1 and parts[1] in self._binary_logical_operators:
            main_connective = parts[1]
            first_operand = self.parse_math_format(parts[0])
            second_operand = self.parse_math_format(' '.join(parts[2:]))
            return CtlFormula(main_connective, [first_operand, second_operand])
        if input_formula[:1] in self._unary_logical_operators:
            return CtlFormula(input_formula[:1], [self.parse_math_format(input_formula[1:])])
        else:  # this is ap
            return CtlFormula(input_formula, [])


def test_formula(formula, parse_method):
    print 'INPUT: ' + formula
    parsed = parse_method(formula)
    print 'RESULT: '
    print 'SMTLIB FORMAT: ' + str(parsed)
    print 'REGULAR FORMAT: ' + parsed.str_math()
    print '\n\n'


def test_ctl_parser():
    ctlParser = CtlParser()

    f1 = '(AU (& (p) (q)) (EX (q)))'
    test_formula(f1, lambda x: ctlParser.parse_smtlib_format(x))
    f2 = 'AG((dataOut3<2> & ~dataOut3<1> & dataOut3<0>) -> AX AF(dataOut3<2> & ~dataOut3<1> & dataOut3<0>))'
    test_formula(f2, lambda x: ctlParser.parse_math_format(x))

    f3 = 'AG(full<0> -> AF(dataOut1<1> | dataOut1<0>))'
    test_formula(f3, lambda x: ctlParser.parse_math_format(x))

    f4 = '~E safe U final'
    test_formula(f4, lambda x: ctlParser.parse_math_format(x))

    f5 = 'AG(~u_ack<1> -> (A u_req<1> R ~u_ack<1>))'
    test_formula(f5, lambda x: ctlParser.parse_math_format(x))


if __name__ == '__main__':
    test_ctl_parser()
    print is_balanced_brackets('dataOut3<2> & ~dataOut3<1> & dataOut3<0>')

def par(text):
    return '(' + text + ')'


def remove_spaces_from_edges(text):
    text = text[next(i for i in range(len(text)) if text[i] != ' '):]
    last_space = next(i for i in range(len(text)) if text[len(text) - 1 - i] != ' ')
    text = text if text[-1] != ' ' else text[:-1 * last_space]
    return text


def remove_characters(text, characters_to_remove):
    return ''.join([ch for ch in text if ch not in characters_to_remove]).replace('R','V')


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
    unary_logical_operators = ['!', '~']
    unary_temporal_operators = ['EX', 'AX', 'AG', 'EG', 'AF', 'EF']
    unary_operators = unary_logical_operators + unary_temporal_operators
    binary_logical_operators = ['->', '&', '|']
    binary_temporal_operators = ['AV', 'EV', 'AU', 'EU', 'AR', 'ER']
    binary_operators = binary_logical_operators + binary_temporal_operators
    allowed_operators = unary_operators + binary_operators

    def __init__(self, node_data, operands):
        super(CtlFormula, self).__init__()
        self._node_data = node_data
        self._operands = operands

    def str_math(self):
        if not self._operands:  # list is empty.
            return str(self._node_data)
        if self._node_data in CtlFormula.unary_operators:
            first_operand = self._operands[0].str_math()
            return self._node_data + par(first_operand)
        else:
            first_operand = self._operands[0].str_math()
            second_operand = self._operands[1].str_math()
            if self._node_data in CtlFormula.binary_temporal_operators:
                return self._node_data[0] + par(first_operand) + self._node_data[1] + par(second_operand)
            if self._node_data in CtlFormula.binary_logical_operators:
                return par(first_operand) + str(self._node_data) + par(second_operand)

    def __str__(self):
        return par(str(self._node_data) + ' '.join([str(op) for op in self._operands]))

    def is_atomic_proposition(self):
        return self.is_leaf() and self._node_data not in [True, False]

    def is_leaf(self):
        return not self._operands

    def get_arity(self):
        return len(self._operands)

    def get_operands(self):
        return self._operands

    def get_main_connective(self):
        return self._node_data

    def get_ap_text(self):
        assert self.is_atomic_proposition()
        return self._node_data

    def get_atomic_propositions(self):
        if self.is_atomic_proposition():
            return [self._node_data]
        return list(set([ap for operand in self._operands for ap in operand.get_atomic_propositions()]))

    def convert_to_omg(self):
        # base
        if self.is_leaf():
            return self

        # step

        main_connective = self.get_main_connective()
        if main_connective in CtlFormula.unary_operators:
            operand = self.get_operands()[0].convert_to_omg()

            if main_connective in ['EX', '~', '!']:
                return CtlFormula(main_connective, [operand])

            if main_connective == 'AX':
                return CtlFormula('~', [CtlFormula('EX', [CtlFormula('~', [operand])])])

            if main_connective in ['AG', 'EG']:
                new_main_connective = main_connective[0] + 'V'
                return CtlFormula(new_main_connective, [CtlFormula(False, []), operand])

            if main_connective in ['AF', 'EF']:
                negated_main_connective = ('E' if main_connective[0] == 'A' else 'A') + 'V'
                return CtlFormula('~', [
                    CtlFormula(negated_main_connective, [CtlFormula(False, []), CtlFormula('~', [operand])])])
        else:
            left_operand = self.get_operands()[0].convert_to_omg()
            right_operand = self.get_operands()[1].convert_to_omg()
            if main_connective in ['AV', 'EV', '&', '->', '|']:
                return CtlFormula(main_connective, [left_operand, right_operand])

            if main_connective in ['AU', 'EU']:

                negated_main_connective = ('E' if main_connective[0] == 'A' else 'A') + 'V'
                return CtlFormula('~', [CtlFormula(negated_main_connective, [CtlFormula('~', [left_operand]),
                                                                             CtlFormula('~', [right_operand])])])

    def remove_double_negations(self):
        if self.is_leaf():
            return self
        reduced_operands = [op.remove_double_negations() for op in self._operands]

        if self._node_data not in CtlFormula.unary_logical_operators:
            return CtlFormula(self._node_data, reduced_operands)

        operand = reduced_operands[0]
        if operand.get_main_connective() in CtlFormula.unary_logical_operators:
            return operand.get_operands()[0]
        else:
            return CtlFormula(self._node_data, reduced_operands)


class CtlParser(object):
    """
    Format:
    CTL -> (AP)
    CTL -> (unary_connective, CTL)
    CTL -> (binary_connective, CTL, CTL)
    """
    unary_logical_operators = ['!', '~']
    unary_temporal_operators = ['EX', 'AX', 'AG', 'EG', 'AF', 'EF']
    unary_operators = unary_logical_operators + unary_temporal_operators
    binary_logical_operators = ['->', '&', '|']
    binary_temporal_operators = ['AV', 'EV', 'AU', 'EU', 'AR', 'ER']
    binary_operators = binary_logical_operators + binary_temporal_operators
    allowed_operators = unary_operators + binary_operators

    def __init__(self):
        super(CtlParser, self).__init__()

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
        if main_operator not in CtlParser.allowed_operators:
            raise Exception('Error in parsing CTL formula ' + input_formula + ': unrecognized operator')
        if (main_operator in CtlParser.unary_operators) and (len(input_operands) != 1):
            raise Exception('Error in parsing CTL formula ' + input_formula + ': unary operator')
        if (main_operator in CtlParser.binary_operators) and (len(input_operands) != 2):
            raise Exception('Error in parsing CTL formula ' + input_formula + ': binary operator')
        parsed_operands = [self.parse_smtlib_format(sub_part) for sub_part in input_operands]

        return CtlFormula(main_operator, parsed_operands)

    def parse_math_format(self, input_formula):
        # print 'ENTERING WITH: '+input_formula

        input_formula = remove_spaces_from_edges(input_formula)

        while input_formula[0] == '(' and input_formula[-1] == ')' and is_balanced_brackets(input_formula[1:-1]):
            #    print 'NOW :'+input_formula
            input_formula = input_formula[1:-1]
            remove_spaces_from_edges(input_formula)

        if input_formula[:2] in CtlParser.unary_temporal_operators:
            return CtlFormula(input_formula[:2], [self.parse_math_format(input_formula[2:])])
        parts = split_components(input_formula)
        # AP, binary temporal or binary logical
        if input_formula[0] in ['A', 'E']:
            path_quantifier = input_formula[0]
            temporal_operator = parts[2][0]
            if temporal_operator == 'R':
                temporal_operator = 'V'
            main_connective = path_quantifier + temporal_operator
            first_operand = self.parse_math_format(parts[1])
            second_operand = self.parse_math_format(' '.join(parts[3:]))
            return CtlFormula(main_connective, [first_operand, second_operand])
        #    print parts
        if len(parts) > 1 and parts[1] in CtlParser.binary_logical_operators:
            main_connective = parts[1]
            first_operand = self.parse_math_format(parts[0])
            second_operand = self.parse_math_format(' '.join(parts[2:]))
            return CtlFormula(main_connective, [first_operand, second_operand])
        if input_formula[:1] in CtlParser.unary_logical_operators:
            return CtlFormula(input_formula[:1], [self.parse_math_format(input_formula[1:])])
        else:  # this is ap
            return CtlFormula(input_formula, [])


def test_formula(formula, parse_method):
    print 'Testing: ' + formula,
    parsed = parse_method(formula)
    #  print 'RESULT: '
    #  print 'SMTLIB FORMAT: ' + str(parsed)
    #  print 'REGULAR FORMAT: ' + parsed.str_math()
    #  print '\n\n'
    to_remove = [' ', '(', ')']
    if remove_characters(formula, to_remove) == remove_characters(parsed.str_math(), to_remove):
        print ' PASSED!'
        print parsed.str_math()
        omg = parsed.convert_to_omg()
        print omg.str_math()
        no_double_negs = omg.remove_double_negations()
        print no_double_negs.str_math()
    else:
        print ' FAILED!!!!!!!!!!!!!!!!!!!'
        print remove_characters(formula, to_remove)
        print remove_characters(parsed.str_math(), to_remove)
        print '*******************************************************************'
    print 'AP: ' + str(parsed.get_atomic_propositions())


def test_ctl_parser():
    ctl_parser = CtlParser()

    f1 = '(AU (& (p) (q)) (EX (q)))'
  #  test_formula(f1, lambda x: ctl_parser.parse_smtlib_format(x))

    f2 = 'AG((dataOut3<2> & ~dataOut3<1> & dataOut3<0>) -> AX AF(dataOut3<2> & ~dataOut3<1> & dataOut3<0>))'
    test_formula(f2, lambda x: ctl_parser.parse_math_format(x))


    f3 = 'AG(full<0> -> AF(dataOut1<1> | dataOut1<0>))'
    test_formula(f3, lambda x: ctl_parser.parse_math_format(x))

    f4 = '~E safe U final'
    test_formula(f4, lambda x: ctl_parser.parse_math_format(x))

    f5 = 'AG(~u_ack<1> -> (A u_req<1> R ~u_ack<1>))'
    test_formula(f5, lambda x: ctl_parser.parse_math_format(x))


if __name__ == '__main__':
    test_ctl_parser()

DEBUG = False


def _par(text):
    return '(' + text + ')'


def _remove_spaces_from_edges(text):
    text = text.replace('\n', '').replace(';', '')
    try:
        text = text[next(i for i in range(len(text)) if text[i] != ' '):]
        last_space = next(i for i in range(len(text)) if text[len(text) - 1 - i] != ' ')
        text = text if text[-1] != ' ' else text[:-1 * last_space]
    except Exception as e:
        print e
        raise Exception('Problem in '+text)

    return text


def _remove_characters(text):
    characters_to_remove = [' ', '(', ')']
    characters_removed = ''.join([ch for ch in text if ch not in characters_to_remove])
    return characters_removed.replace('R', 'V').replace('!', '~')


def is_balanced_brackets(text):
    values = {"(": 1, ")": -1}
    contribution = [values[c] if c in values else 0 for c in text]
    counts = list(_accumulate(contribution))

    return all(c >= 0 for c in counts) and counts[-1] == 0


def _accumulate(list_num):
    res = []
    addition = 0
    for i in range(len(list_num)):
        addition += list_num[i]
        res.append(addition)
    return res


def _split_components(f):
    """
    Written by Tal Shinkar. Many thanks.
    """
    values = {"(": 1, ")": -1}
    contribution = [values[c] if c in values else 0 for c in f]
    counts = list(_accumulate(contribution))
    is_balanced = (all(c >= 0 for c in counts) and counts[-1] == 0)  # f is balanced
    if not is_balanced:
        assert is_balanced

    lsplits = [i + 1 for i in range(len(counts) - 1) if counts[i] == 0 and counts[i + 1] != 0]
    rsplits = [i + 2 for i in range(len(counts) - 1) if counts[i] != 0 and counts[i + 1] == 0]
    splits = [0] + sorted(lsplits + rsplits) + [len(counts)]

    cuts = [f[splits[i]:splits[i + 1]] for i in range(len(splits) - 1)]
    cuts_no_blanks = [c for c in cuts if c != '' and not all(ch == ' ' for ch in c)]

    cuts_split = []
    for i in range(len(cuts_no_blanks)):
        if cuts_no_blanks[i][0] != '(':
            cuts_split += [c for c in cuts_no_blanks[i].split(' ') if c != '']
        else:
            cuts_split += [cuts_no_blanks[i]]
    return cuts_split


def _flip_ae(ch):
    return 'A' if ch == 'E' else 'E'


class CtlFormula(object):
    """docstring for CtlFormula."""
    unary_logical_operators = ['!', '~']
    unary_temporal_operators = ['EX', 'AX', 'AG', 'EG', 'AF', 'EF']
    unary_operators = unary_logical_operators + unary_temporal_operators
    binary_logical_operators = ['->', '&', '|', '^', '==']  ## ORDER OF PRECEDENCE
    binary_temporal_operators = ['AV', 'EV', 'AU', 'EU', 'AR', 'ER', 'AW', 'EW']
    binary_operators = binary_logical_operators + binary_temporal_operators
    allowed_operators = unary_operators + binary_operators

    def __init__(self, node_data, operands=None):
        super(CtlFormula, self).__init__()
        if operands is None:
            operands = []
        self._node_data = node_data
        self._operands = operands

    def str_math(self):
        if not self._operands:
            return str(self._node_data)
        if self._node_data in CtlFormula.unary_operators:
            first_operand = self._operands[0].str_math()
            return self._node_data + _par(first_operand)
        else:
            first_operand = self._operands[0].str_math()
            second_operand = self._operands[1].str_math()
            if self._node_data in CtlFormula.binary_temporal_operators:
                return self._node_data[0] + _par(first_operand) + self._node_data[1] + _par(second_operand)
            if self._node_data in CtlFormula.binary_logical_operators:
                return _par(first_operand) + str(self._node_data) + _par(second_operand)

    def __str__(self):
        return _par(str(self._node_data) + ' '.join([str(op) for op in self._operands]))

    def is_atomic_proposition(self):
        return self.is_leaf() and self._node_data not in [True, False]

    def __eq__(self, o):
        if not isinstance(o, CtlFormula):
            return False

        if self.is_leaf():
            if not o.is_leaf():
                return False
            return self.get_ap_text() == o.get_ap_text()

        if o.is_leaf() or self.get_main_connective() != o.get_main_connective() or len(self.get_operands()) != len(
                o.get_operands()):
            return False

        for i in range(len(self.get_operands())):
            if self.get_operands()[i] != o.get_operands()[i]:
                return False

        return True

    def __ne__(self, o):
        return not self == o

    def __hash__(self):
        return self.str_math().__hash__()

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
            return [self]
        return list(set([ap for operand in self._operands for ap in operand.get_atomic_propositions()]))

    def negate(self):
        if self._node_data in CtlFormula.unary_logical_operators:
            return self._operands[0]
        else:
            return CtlFormula('~', [self])

    def convert_to_omg_format(self):
        # base case
        if self.is_leaf():
            return self

        # induction step
        main_connective = self.get_main_connective()
        if main_connective in CtlFormula.unary_operators:
            operand = self.get_operands()[0].convert_to_omg_format()

            if main_connective in ['EX']:
                return CtlFormula(main_connective, [operand])

            if main_connective in CtlFormula.unary_logical_operators:
                return operand.negate()

            if main_connective == 'AX':
                return CtlFormula('EX', [operand.negate()]).negate()

            if main_connective in ['AG', 'EG']:
                new_main_connective = main_connective[0] + 'V'
                return CtlFormula(new_main_connective, [CtlFormula(False), operand])

            if main_connective in ['AF', 'EF']:
                new_main_connective = _flip_ae(main_connective[0]) + 'V'
                return CtlFormula(new_main_connective, [CtlFormula(False), operand.negate()]).negate()
        else:
            left_operand = self.get_operands()[0].convert_to_omg_format()
            right_operand = self.get_operands()[1].convert_to_omg_format()
            if main_connective in ['AV', 'EV', '&', '->', '|']:
                return CtlFormula(main_connective, [left_operand, right_operand])

            if main_connective in ['AU', 'EU']:
                negated_main_connective = _flip_ae(main_connective[0]) + 'V'
                return CtlFormula(negated_main_connective, [left_operand.negate(), right_operand.negate()]).negate()

            if main_connective in ['^']:
                left_or = CtlFormula('&', [left_operand.negate(), right_operand])
                right_or = CtlFormula('&', [left_operand, right_operand.negate()])
                return CtlFormula('|', [left_or, right_or])

            if main_connective in ['==']:
                left_implication = CtlFormula('->', [left_operand, right_operand])
                right_implication = CtlFormula('->', [right_operand, left_operand])
                return CtlFormula('&', [left_implication, right_implication])

            if main_connective in ['AW', 'EW']:
                new_main_connective = main_connective[0] + 'V'

                return CtlFormula(new_main_connective, [right_operand, CtlFormula('|', [left_operand, right_operand])])

            raise Exception('Unsupported operator '+main_connective)

class CtlParser(object):
    """
    Format:
    CTL -> (AP)
    CTL -> (unary_connective, CTL)
    CTL -> (binary_connective, CTL, CTL)
    """

    def __init__(self):
        super(CtlParser, self).__init__()

    def parse_smtlib_format(self, input_formula):
        if input_formula[0] != '(' or input_formula[-1] != ')':
            raise Exception('Error in parsing CTL formula ' + input_formula + ': brackets')
        input_formula = input_formula[1:-1]
        parts = _split_components(input_formula)
        if not parts:
            raise Exception('Error in parsing CTL formula ' + input_formula + ': brackets')

        main_operator = parts[0]
        input_operands = parts[1:]
        if not input_operands:
            return CtlFormula(parts[0], [])
        #    print main_operator +str(len(main_operator))
        if main_operator not in CtlFormula.allowed_operators:
            raise Exception('Error in parsing CTL formula ' + input_formula + ': unrecognized operator')
        if (main_operator in CtlFormula.unary_operators) and (len(input_operands) != 1):
            raise Exception('Error in parsing CTL formula ' + input_formula + ': unary operator')
        if (main_operator in CtlFormula.binary_operators) and (len(input_operands) != 2):
            raise Exception('Error in parsing CTL formula ' + input_formula + ': binary operator')
        parsed_operands = [self.parse_smtlib_format(sub_part) for sub_part in input_operands]

        return CtlFormula(main_operator, parsed_operands)

    def split_by_operator(self, parts, operator):
        operator_locations = [i for i in range(len(parts)) if parts[i] == operator]
        if operator_locations:
            and_location = operator_locations[0]
            first_operand = self.parse_math_format(' '.join(parts[:and_location]))
            second_operand = self.parse_math_format(' '.join(parts[and_location + 1:]))
            return CtlFormula(operator, [first_operand, second_operand])
        return None

    def parse_math_format(self, input_formula):
        # print 'ENTERING WITH: '+input_formula
        """
        Precedence order:
        %left '^' "==" "->";
        %left '|';
        %left '&';
        %nonassoc '~' '!';
        %left EX EF EG AX AF AG EQUANT AQUANT UNTIL RELEASES WEAK_UNTIL;  // We do not support weak until.

        I don't think so. Negations are reduced last for me.
        """

        input_formula = _remove_spaces_from_edges(input_formula)
        if DEBUG:
            print 'NOW :' + input_formula

        while input_formula[0] == '(' and input_formula[-1] == ')' and is_balanced_brackets(input_formula[1:-1]):
            if DEBUG:
                print 'R_NOW :' + input_formula
            input_formula = input_formula[1:-1]
            _remove_spaces_from_edges(input_formula)

        if input_formula[:2] in CtlFormula.unary_temporal_operators:
            return CtlFormula(input_formula[:2], [self.parse_math_format(input_formula[2:])])

        parts = _split_components(input_formula)
        if DEBUG:
            print parts

        # First checking if this is a binary temporal operator.
        if input_formula[0] in ['A', 'E'] and len(parts[0]) == 1 and len(parts) > 1:
            path_quantifier = input_formula[0]
            try:
                temp_op_index = next(i for i in range(len(parts)) if (path_quantifier+parts[i]) in CtlFormula.binary_temporal_operators)
                temporal_operator = parts[temp_op_index].replace('R', 'V')
            except Exception as e:
                print 'upupu'
                print e
                raise Exception('Parsing Failed dur to '+input_formula)
            main_connective = path_quantifier + temporal_operator

            first_operand = self.parse_math_format(' '.join(parts[1:temp_op_index]))
            second_operand = self.parse_math_format(' '.join(parts[temp_op_index+1:]))

            return CtlFormula(main_connective, [first_operand, second_operand])

        # Handle negations
        if input_formula[:1] in CtlFormula.unary_logical_operators:
            return CtlFormula(input_formula[:1], [self.parse_math_format(input_formula[1:])])

        # Handle &, |, -> (in that order)
        if len(parts) > 2:
            for operator in CtlFormula.binary_logical_operators:
                split_result = self.split_by_operator(parts, operator)
                if split_result is not None:
                    return split_result



        else:  # Otherwise, it is an atomic proposition or true/false
            return self._parse_ap_bool(input_formula)

    def _parse_ap_bool(self, input_formula):
        if input_formula.lower() == 'true':
            return CtlFormula(True)
        elif input_formula.lower() == 'false':
            return CtlFormula(False)
        else:
            return CtlFormula(input_formula)

    def parse_omg(self, raw_specification):
        return self.parse_math_format(raw_specification).convert_to_omg_format()


def test_formula(formula, parse_method, verbose=False):
    print 'Testing: ' + formula,
    parsed = parse_method(formula)
    if verbose:
        print 'RESULT: '
        print 'SMTLIB FORMAT: ' + str(parsed)
        print 'REGULAR FORMAT: ' + parsed.str_math()
        print '\n\n'

    if _remove_characters(formula) == _remove_characters(parsed.str_math()):
        print ' PASSED!'
        if verbose:
            print parsed.str_math()
            omg = parsed.convert_to_omg_format()

            print 'OMGing: ' + omg.str_math()

    else:
        print ' FAILED!!!!!!!!!!!!!!!!!!!'
        if verbose:
            print _remove_characters(formula)
            print _remove_characters(parsed.str_math())
            print '*******************************************************************'
    if verbose:
        print 'AP: ' + str(parsed.get_atomic_propositions())


def test_ctl_parser():
    ctl_parser = CtlParser()

    f2 = 'AG((dataOut3<2> & ~dataOut3<1> & dataOut3<0>) -> AX AF(dataOut3<2> & ~dataOut3<1> & dataOut3<0>))'
    test_formula(f2, lambda x: ctl_parser.parse_math_format(x), True)

    f3 = 'AG(full<0> -> AF(dataOut1<1> | dataOut1<0>))'
    test_formula(f3, lambda x: ctl_parser.parse_math_format(x), True)

    f4 = '~E safe U final'
    test_formula(f4, lambda x: ctl_parser.parse_math_format(x), True)

    f5 = 'AG(~u_ack<1> -> (A u_req<1> R ~u_ack<1>))'
    test_formula(f5, lambda x: ctl_parser.parse_math_format(x), True)


if __name__ == '__main__':
    test_ctl_parser()

    # current problem: ~ is parsed before &. What is the truth?

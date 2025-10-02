# This file is an addition to the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/operators.py

"""Syntactic conversion of predicate formulas to use only specific sets of
operators."""
from syntax import *
from proofs import Schema

def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> Formula:
    """Substitutes in the current formula, each constant or operator `op`
    that is a key in `substitution_map` with the formula
    `substitution_map[op]` applied to its (zero or one or two) operands,
    where the first operand is used for every occurrence of ``'p'`` in the
    formula and the second for every occurrence of ``'q'``.

    Parameters:
        substitution_map: mapping defining the substitutions to be
            performed.

    Returns:
        The formula resulting from performing all substitutions. Only
        operator occurrences originating in the current formula are
        substituted (i.e., operator occurrences originating in one of the
        specified substitutions are not subjected to additional
        substitutions).

    Examples:
        >>> substitute_operators(Formula.parse('((R(a,b)&S(f(a)))->a=b)'),
        ...     {'&': Schema(Formula.parse('~(~P()|~Q())'), {'P','Q'})})
        (~(~R(a,b)|~S(f(a)))->a=b)
    """
    for operator in substitution_map:
        assert is_unary(operator) or is_binary(operator)
        assert substitution_map[operator].templates.issubset({'P', 'Q'})
    root = self.root

    substitution_map = {operator:substitution_map[operator] for operator in substitution_map if operator in Formula.operators(self)}
    if substitution_map:
        if is_quantifier(root):
            result = Formula(root, self.variable, substitute_operators(self.statement, substitution_map))

        if is_unary(root):
            if root in substitution_map:
                first = substitute_operators(self.first, substitution_map)
                inst_map = {'P': first}
                result = substitution_map[root].instantiate(inst_map)
            else:
                result = Formula(root, substitute_operators(self.first, substitution_map))

        elif is_binary(root):
            if root in substitution_map:
                first = substitute_operators(self.first, substitution_map)
                second = substitute_operators(self.second, substitution_map)
                inst_map = {'P': first, 'Q': second}
                result = substitution_map[root].instantiate(inst_map)
            else:
                result = Formula(root, substitute_operators(self.first, substitution_map), substitute_operators(self.second, substitution_map))
    else:
        result = self

    return result
    # Harris J. Bolus - Personal Task

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '~', '&', and '|'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '~', '&', and
        '|'.
    """
    sub_map = {'->': Schema(Formula.parse('(~P()|Q())'), {'P', 'Q'}),
               '+': Schema(Formula.parse('((P()|Q())&~(P()&Q()))'), {'P', 'Q'}),
               '-&': Schema(Formula.parse('~(P()&Q())'), {'P', 'Q'}),
               '-|': Schema(Formula.parse('~(P()|Q())'), {'P', 'Q'}),
               '<->': Schema(Formula.parse('((~P()|Q())&(~Q()|P()))'), {'P', 'Q'})}
    return substitute_operators(formula, sub_map)
    # Harris J. Bolus - Personal Task

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '~' and '&'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '~' and '&'.
    """
    sub_map = {'|': Schema(Formula.parse('~(~P()&~Q())'), {'P', 'Q'}),
               '->': Schema(Formula.parse('~(P()&~Q())'), {'P', 'Q'}),
               '+': Schema(Formula.parse('(~(P()&Q())&~(~P()&~Q()))'), {'P', 'Q'}),
               '-&': Schema(Formula.parse('~(P()&Q())'), {'P', 'Q'}),
               '-|': Schema(Formula.parse('(~P()&~Q())'), {'P', 'Q'}),
               '<->': Schema(Formula.parse('(~(P()&~Q())&~(Q()&~P()))'), {'P', 'Q'})}
    return substitute_operators(formula, sub_map)
    # Harris J. Bolus - Personal Task

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '-&'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '-&'.
    """
    sub_map = {'~': Schema(Formula.parse('(P()-&P())'), {'P'}),
               '&': Schema(Formula.parse('((P()-&Q())-&(P()-&Q()))'), {'P', 'Q'}),
               '|': Schema(Formula.parse('((P()-&P())-&(Q()-&Q()))'), {'P', 'Q'}),
               '->': Schema(Formula.parse('(P()-&(Q()-&Q()))'), {'P', 'Q'}),
               '+': Schema(Formula.parse('((P()-&(P()-&Q()))-&(Q()-&(P()-&Q())))'), {'P', 'Q'}),
               '-|': Schema(Formula.parse('(((P()-&Q())-&(Q()-&Q()))-&((P()-&P())-&(Q()-&Q())))'), {'P', 'Q'}),
               '<->': Schema(Formula.parse('(((P()-&P())-&(Q()-&Q()))-&(P()-&Q()))'), {'P', 'Q'})}
    return substitute_operators(formula, sub_map)
    # Harris J. Bolus - Personal Task

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '->' and '~'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '->' and '~'.
    """
    sub_map = {'&': Schema(Formula.parse('~(P()->~Q())'), {'P', 'Q'}),
               '|': Schema(Formula.parse('(~P()->Q())'), {'P', 'Q'}),
               '+': Schema(Formula.parse('((P()->Q())->~(Q()->P()))'), {'P', 'Q'}),
               '-|': Schema(Formula.parse('~(~P()->Q())'), {'P', 'Q'}),
               '-&': Schema(Formula.parse('(P()->~Q())'), {'P', 'Q'}),
               '<->': Schema(Formula.parse('~((P()->Q())->~(Q()->P()))'), {'P', 'Q'})}
    return substitute_operators(formula, sub_map)
    # Harris J. Bolus - Personal Task

def to_not_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '~' and '|'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '~' and '|'.
    """
    sub_map = {'&': Schema(Formula.parse('~(~P()|~Q())'), {'P', 'Q'}),
               '->': Schema(Formula.parse('~(~P()|Q())'), {'P', 'Q'}),
               '+': Schema(Formula.parse('(~(~P()|Q())|~(~Q()|P()))'), {'P', 'Q'}),
               '-&': Schema(Formula.parse('(~P()|~Q())'), {'P', 'Q'}),
               '-|': Schema(Formula.parse('~(P()|Q())'), {'P', 'Q'}),
               '<->': Schema(Formula.parse('~(~(~P()|Q())|~(~Q()|P()))'), {'P', 'Q'})}
    return substitute_operators(formula, sub_map)
    # Harris J. Bolus - Personal Task

def to_nor(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '-|'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '-|'.
    """
    sub_map = {'~': Schema(Formula.parse('(P()-|P())'), {'P'}),
               '&': Schema(Formula.parse('((P()-|P())-|(Q()-|Q()))'), {'P', 'Q'}),
               '|': Schema(Formula.parse('((P()-|Q())-|(P()-|Q()))'), {'P', 'Q'}),
               '->': Schema(Formula.parse('(((P()-|P())-|Q())-|((P()-|P())-|Q()))'), {'P', 'Q'}),
               '+': Schema(Formula.parse('((P()-|Q())-|((P()-|P())-|(Q()-|Q())))'), {'P', 'Q'}),
               '-&': Schema(Formula.parse('(((P()-|P())-|(Q()-|Q()))-|((P()-|P())-|(Q()-|Q())))'), {'P', 'Q'}),
               '<->': Schema(Formula.parse('((P()-|(P()-|Q()))-|(Q()-|(P()-|Q())))'), {'P', 'Q'})}
    return substitute_operators(formula, sub_map)
    # Harris J. Bolus - Personal Task

def frege(formula: Formula) -> None:
    """Computes a representation of the current formula in Frege's notation.

    Returns:
        A Fregean notation representation of the current formula.
    """

    def _frege_helper(self: Formula) -> str:
        """Computes a representation of the current formula, which contains only
       the operators `~` and `->`, in Frege's notation, lacking a judgement stroke.

        Returns:
            The Fregean notation representation of the current formula, lacking
            a judgement stroke.
        """

        root = self.root
        if is_relation(root) or is_equality(root):
            return ['─ '+str(self)]

        elif is_unary(root):
            first = _frege_helper(self.first)
            if len(first) > 1:
                for i in range(1, len(first)):
                    first[i] = '  '+first[i]
            first[0] = '─┬'+first[0]
            return first

        elif is_binary(root):
            first = _frege_helper(self.first)
            second = _frege_helper(self.second)
            diff = len(first[0].split(' ')[0])-len(second[0].split(' ')[0])
            if diff > 0:
                second[0] = '─'*diff+second[0]
            second[0] = '─┬'+second[0]
            if len(second) > 1:
                for i in range(1, len(second)):
                    if diff > 0:
                        second[i] = ' '*diff+second[i]
                    second[i] = ' │'+second[i]

            if diff < 0:
                first[0] = '─'*(diff*-1)+first[0]
            first[0] = ' └'+first[0]
            if len(first) > 1:
                for i in range(1, len(first)):
                    if diff < 0:
                        first[i] = ' '*(diff*-1)+first[i]
                    first[i] = '  '+first[i]
            return [*second, *first]

        else:
            assert is_quantifier(root)
            variable = self.variable
            statement = _frege_helper(self.statement)

            if root == 'A':
                statement[0] = f'─{variable}─{statement[0]}'
            elif root == 'E':
                statement[0] = f'┬{variable}┬{statement[0]}'

            for i in range(1, len(statement)):
                statement[i] = (len(variable)+2)*' '+statement[i]
            return statement
    string = _frege_helper(to_implies_not(formula))
    print('├─'+'\n  '.join(string))
    # Harris J. Bolus - Personal Task


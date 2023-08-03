# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union
from itertools import takewhile
from logic_utils import frozen, memoized_parameterless_method

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and (len(string) == 1 or string[1:].isdecimal())

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'

@lru_cache(maxsize=100) # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'

@lru_cache(maxsize=100) # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    #return string == '&' or string == '|' or string == '->'
    # For Chapter 3:
    return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}

@lru_cache(maxsize=100) # Cache the return value of split_str
def split_str(string): #returns any operator, constant, (, ), or variable if it's the first character.
    if string and string[0] == '-':
        prefix, suffix = string[:2], string[2:]
    elif string and string[0] == '<':
        prefix, suffix = string[:3], string[3:]
    else:
        prefix, suffix = string[:1], string[1:]

    if prefix and is_variable(prefix):
        while suffix and suffix[0].isnumeric():
            prefix += suffix[0]
            suffix = suffix.replace(suffix[0], '', 1)
    return prefix, suffix

@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    variable names, and operators applied to them.

    Attributes:
        root (`str`): the constant, variable name, or operator at the root of
            the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None, second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand for the root, if the root is a unary or
                binary operator.
            second: the second operand for the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        attributes = dir(self)
        if 'root' in attributes:
            if isinstance(self.root, Formula):
                root = self.root.__repr__()
            else:
                root = self.root
            if 'first' in attributes:
                if isinstance(self.first, Formula):
                    first = self.first.__repr__()
                else:
                    first = self.first

                if is_unary(self.root):
                    string = root + first

                else:
                    assert is_binary(self.root) and 'second' in attributes
                    if isinstance(self.second, Formula):
                        second = self.second.__repr__()
                    else:
                        second = self.second
                    string = '(' + first + root + second + ')'
            else: string = root
        return string
        # Task 1.1

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        if is_variable(str(self.root)):
            root = {str(self.root)}
            return root
        elif isinstance(self.root, Formula):
            root = self.root.variables()
            return root

        if 'first' in dir(self):
            if is_variable(str(self.first)):
                first = {str(self.first)}
            elif isinstance(self.first, Formula):
                first = self.first.variables()

            if 'second' in dir(self):
                if is_variable(str(self.second)):
                    second = {str(self.second)}
                    return first | second
                elif isinstance(self.second,Formula):
                    second = self.second.variables()
                    return first | second
            else:
                return first
        else:
            return set()
        # Task 1.2

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        if is_constant(self.root) or is_unary(self.root) or is_binary(self.root):
            root = {self.root}
        else:
            root = set()

        if 'first' in dir(self):
            if isinstance(self.first, Formula):
                first = self.first.operators()
            if 'second' in dir(self):
                if isinstance(self.second, Formula):
                    second = self.second.operators()
            else:
                second = set()
        else:
            first, second = set(), set()
        return root | first | second
        # Task 1.3

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        prefix, suffix = split_str(string)
        if prefix and (is_constant(prefix) or is_variable(prefix)):
            return Formula(prefix), suffix

        elif is_unary(prefix):
            root = prefix
            first, suffix = Formula._parse_prefix(suffix)
            if first is None:
                return first, suffix
            else:
                return Formula(root, first), suffix

        elif prefix == '(':
            first, suffix = Formula._parse_prefix(suffix)
            if first is None:
                return first, suffix

            root, suffix = split_str(suffix)
            if not is_binary(root):
                return None, 'Unexpected symbol {} in {}'

            second, tail = Formula._parse_prefix(suffix)
            if second is None:
                return second, tail

            if not tail.startswith(')'):
                return None, 'Unexpected symbol {} in {}'.format(tail[:1], tail)

            return Formula(root, first, second), tail[1:]

        else:
            return None, "Unexpected input {}".format(string)
        # Task 1.4


    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        prefix, suffix = Formula._parse_prefix(string)
        while suffix:
            try:
                prefix, suffix = Formula._parse_prefix(suffix)
            except:
                return False
            if suffix.split(' ')[0] == 'Unexpected':
                return False
        return True
        # Task 1.5

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        return Formula._parse_prefix(string)[0]
        # Task 1.6

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        root = str(self.root)
        if 'first' in dir(self):
            first = self.first
            if 'first' in dir(first):
                first = Formula.polish(first)
            if 'second' in dir(self):
                second = self.second
                if 'first' in dir(second):
                    second = Formula.polish(second)
                return str(root) + str(first) + str(second)
            else:
                return str(root) + str(first)
        else:
            return str(root)

        # Optional Task 1.7

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        prefix, suffix = split_str(string)

        if is_variable(prefix):
            return (Formula(prefix))
        elif is_unary(prefix):
            return Formula(prefix, (Formula.parse_polish(suffix)))
        elif is_binary(prefix):                                         # & pq
            root = prefix
            first, second = split_str(suffix)
            return Formula(root, first, second)

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable name `v` that is a
        key in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variable name occurrences originating in the current formula are
            substituted (i.e., variable name occurrences originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
            if self == Formula(variable):
                return substitution_map[variable]
            elif 'first' in dir(self):
                if is_unary(self.root):
                    return Formula(self.root, Formula.substitute_variables(self.first, substitution_map))
                elif 'second' in dir(self):
                    return Formula(self.root, Formula.substitute_variables(self.first, substitution_map), Formula.substitute_variables(self.second, substitution_map))
        return self
        # Task 3.3

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
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_constant(operator) or is_unary(operator) or is_binary(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})

        substitution_map = {operator:substitution_map[operator] for operator in substitution_map if operator in Formula.operators(self)}
        if substitution_map:
            if is_constant(str(self)):
                return substitution_map[str(self)]

            else:
                if is_unary(self.root):
                    if self.root in substitution_map:
                        schema = substitution_map[self.root]
                        first = Formula.substitute_operators(self.first, substitution_map)
                        self = Formula.substitute_variables(schema, {'p':first})
                    else:
                        self = Formula(self.root, Formula.substitute_operators(self.first, substitution_map))

                elif is_binary(self.root):
                    if self.root in substitution_map:
                        schema = substitution_map[self.root]
                        first = Formula.substitute_operators(self.first, substitution_map)
                        second = Formula.substitute_operators(self.second, substitution_map)
                        self = Formula.substitute_variables(schema, {'p':first, 'q':second})
                    else:
                        self = Formula(self.root, Formula.substitute_operators(self.first, substitution_map), Formula.substitute_operators(self.second, substitution_map))

        return self
        # Task 3.4

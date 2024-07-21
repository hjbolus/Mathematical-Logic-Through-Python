# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations
from functools import lru_cache, reduce
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union
from logic_utils import fresh_variable_name_generator, frozen, memoized_parameterless_method

import sys
sys.path.append('/Users/harrisbolus/Desktop/Fun/Mathematical logic thru python')
from propositions.syntax import Formula as PropositionalFormula, is_variable as is_propositional_variable

class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """
    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((string[0] >= '0' and string[0] <= '9') or \
              (string[0] >= 'a' and string[0] <= 'e')) and \
               string.isalnum()) or string == '_'

def make_constant(string:str, universe:set) -> str:
    """converts a string to a valid constant name.

    Parameters:
        string: string to convert.

    Returns:
        a string for which is_constant(string) will evaluate to True.
    """
    if not (string[0] >= '0' and string[0] <= '9') or \
              (string[0] >= 'a' and string[0] <= 'e') or \
               string[0] == '_':
        string = '0' + string
    if not string.isalnum():
        string = ''.join([i if i.isalnum() else '' for i in string])
    if string in universe:
        i=1
        new_string = string
        while new_string in universe:
            new_string = string+str(i)
            i+=1
        string = new_string
    return string
    # Personal task

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'u' and string[0] <= 'z' and string.isalnum()

@lru_cache(maxsize=100) # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= 'f' and string[0] <= 't' and string.isalnum()

def separate_relation_name(string: str) -> Tuple:
    assert string and is_relation(string[0]), print(f'{string} does not start with a relation name')
    counter = 0
    while string[counter].isalnum():
        counter += 1
    return string[:counter], string[counter:]

def separate_bracketed_formula(string: str) -> Tuple:
    if (open_bracket := string[0]) not in {'[','('}:
        print(f"{string} doesn't start with a bracket")
        return string
    if open_bracket == '[':
        close_bracket =']'
    else:
        close_bracket = ')'
    counter = 0
    for i,j in enumerate(string):
        if j == open_bracket:
            counter +=1
        elif j == close_bracket:
            counter -=1
        if counter == 0:
            return string[:i+1], string[i+1:]

def separate_operator(string: str) -> list:
    if string[0] in {'&', '|', '+'}:
        return string[0], string[1:]
    elif string[0] == '-':
        assert string[1] in {'>','&','|'}
        return string[0:2], string[2:]
    else:
        assert string[0:3] == '<->'
        return string[0:3], string[3:]

def separate_term(string: str) -> Tuple:
    assert string
    sample = string[0]
    if sample == '_':
        return ('_', string[1:])
    counter = 0
    while counter < len(string) and string[counter].isalnum():
        counter += 1
    if is_constant(sample) or is_variable(sample):
        return string[:counter], string[counter:]

    elif is_function(sample):
        arguments, suffix = separate_bracketed_formula(string[counter:])
        return string[:counter]+arguments, suffix

def separate_function_or_relation_name(string: str) -> Tuple:
    assert string
    counter = 0
    while string[counter].isalnum():
        counter += 1
    return string[:counter], *separate_bracketed_formula(string[counter:])

@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments for the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None and len(arguments) > 0
            self.root = root
            self.arguments = tuple(arguments)

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        root = self.root
        if is_variable(root) or is_constant(root):
            return root
        else:
            assert type(self) == Term or type(self) == Formula
            return f'{root}({",".join([argument.__repr__() for argument in self.arguments])})'
        # Harris J. Bolus - Task 7.1

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        if string:
            sample = string[0]
            if is_constant(sample) or is_variable(sample):
                prefix, suffix = separate_term(string)
                return Term(prefix), suffix
            else:
                assert is_function(sample)
                function_name, args, suffix = separate_function_or_relation_name(string)
                arg_suffix = args[1:-1]
                arg_list = []

                while arg_suffix:
                    arg_prefix, arg_suffix = separate_term(arg_suffix)
                    arg_list.append(arg_prefix)
                    if arg_suffix and arg_suffix[0] == ',':
                        arg_suffix = arg_suffix[1:]
                return Term(function_name, [Term._parse_prefix(arg)[0] for arg in arg_list]), suffix
        # Harris J. Bolus - Task 7.3a

    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        return Term._parse_prefix(string)[0]
        # Harris J. Bolus - Task 7.3b

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        root = self.root
        if is_constant(root):
            return {root}

        elif is_variable(root):
            return set()

        elif is_function(root):
            constants = set()
            for argument in self.arguments:
                constants = constants | Term.constants(argument)
            return constants
        # Harris J. Bolus - Task 7.5a

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        root = self.root
        if is_variable(root):
            return {root}

        elif is_constant(root):
            return set()

        elif is_function(root):
            variables = set()
            for argument in self.arguments:
                variables = variables | Term.variables(argument)
            return variables
        # Harris J. Bolus - Task 7.5b

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        root = self.root
        functions = set()
        if is_function(root):
            functions = functions | {(root, len(self.arguments))}
            for argument in self.arguments:
                functions = functions | Term.functions(argument)
        return functions
        # Harris J. Bolus - Task 7.5c

    def __len__(self) -> int:
        return len(self.variables()) + len(self.constants()) + len(self.functions())
        # personal task

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `construct` or
        variable name `construct` that is a key in `substitution_map` with the
        term `substitution_map[`construct`]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current term are substituted (i.e., those originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from
                `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)

        if not substitution_map:
            return self

        if sinners:= set.union(*[value.variables() for value in substitution_map.values()]) & forbidden_variables:
            raise ForbiddenVariableError(sinners.pop())

        string = str(self)
        if string in substitution_map:
            term = substitution_map[str(self)]
        elif is_variable(string) or is_constant(string):
            term = self
        else:
            term = Term(self.root, [argument.substitute(substitution_map, forbidden_variables) for argument in self.arguments])
        return term
        # Harris J. Bolus - Task 9.1

@lru_cache(maxsize=100) # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == '='

@lru_cache(maxsize=100) # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= 'F' and string[0] <= 'T' and string.isalnum()

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
    return string in {'&', '|', '->', '<->', '+', '-|', '-&'}

@lru_cache(maxsize=100) # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == 'A' or string == 'E'

@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        statement (`~typing.Optional`\\[`Formula`]): the statement quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    statement: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_statement: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable name and statement.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments for the root, if the
                root is a relation name or the equality relation; the first
                operand for the root, if the root is a unary or binary operator;
                the variable name to be quantified by the root, if the root is a
                quantification.
            second_or_statement: the second operand for the root, if the root is
                a binary operator; the statement to be quantified by the root,
                if the root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert isinstance(arguments_or_first_or_variable, Sequence) and not isinstance(arguments_or_first_or_variable, str)
            if is_equality(root):
                assert len(arguments_or_first_or_variable) == 2
            assert second_or_statement is None
            self.root, self.arguments = root, tuple(argument if isinstance(argument, Term) else Term(argument) for argument in arguments_or_first_or_variable)

        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula), print(f'{arguments_or_first_or_variable} is {type(arguments_or_first_or_variable)}, should be Formula')
            assert second_or_statement is None
            self.root, self.first = root, arguments_or_first_or_variable

        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula), print(f'{arguments_or_first_or_variable} is {type(arguments_or_first_or_variable)}')
            assert second_or_statement is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_statement

        else:
            assert is_quantifier(root)
            # Populate self.variable and self.statement
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable)
            assert second_or_statement is not None
            self.root, self.variable, self.statement = root, arguments_or_first_or_variable, second_or_statement

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        root = self.root
        if is_equality(root):
            return f'{self.arguments[0].__repr__()}{root}{self.arguments[1].__repr__()}'

        elif is_relation(root):
            return f'{root}({",".join([argument.__repr__() for argument in self.arguments])})'

        elif is_unary(root):
            return f'{root}{self.first.__repr__()}'

        elif is_binary(root):
            return f'({self.first.__repr__()}{root}{self.second.__repr__()})'

        else:
            assert is_quantifier(root)
            return f'{root}{self.variable}[{self.statement.__repr__()}]'

        # Harris J. Bolus - Task 7.2

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

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'f(y)=c12'``) or by a variable
            name (e.g., ``'f(y)=x12'``), then the parsed prefix will include
            that entire name (and not just a part of it, such as ``'f(y)=x1'``).
        """
        sample = string[0]
        if is_constant(sample) or is_variable(sample) or is_function(sample):
            first, suffix = separate_term(string)
            assert suffix[0] == '='
            second, suffix = separate_term(suffix[1:])
            formula = Formula('=', [Term.parse(first), Term.parse(second)])

        elif is_relation(sample):
            relation_name, args, suffix = separate_function_or_relation_name(string)
            arg_suffix = args[1:-1]
            arg_list = []

            while arg_suffix:
                arg_prefix, arg_suffix = separate_term(arg_suffix)
                arg_list.append(arg_prefix)
                if arg_suffix and arg_suffix[0] == ',':
                    arg_suffix = arg_suffix[1:]
            formula = Formula(relation_name, [Term._parse_prefix(arg)[0] for arg in arg_list])

        elif is_unary(sample):
            prefix, suffix = Formula._parse_prefix(string[1:])
            formula = Formula('~', prefix)

        elif is_quantifier(sample):
            quantifier = sample
            variable, suffix = separate_term(string[1:])
            statement, suffix = separate_bracketed_formula(suffix)
            formula = Formula(quantifier, variable, Formula._parse_prefix(statement[1:-1])[0])

        else:
            assert sample == '('
            binary_formula, suffix = separate_bracketed_formula(string)
            first, remaining = Formula._parse_prefix(binary_formula[1:])
            operator, second = separate_operator(remaining)
            formula = Formula(operator, first, Formula._parse_prefix(second)[0])
        return formula, suffix
        # Harris J. Bolus - Task 7.4a

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        return Formula._parse_prefix(string)[0]
        # Harris J. Bolus - Task 7.4b

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.
        Returns:
            A set of all constant names used in the current formula.
        """
        root = self.root
        if is_quantifier(root):
            return Formula.constants(self.statement)

        elif is_unary(root):
            return Formula.constants(self.first)

        elif is_binary(root):
            return Formula.constants(self.first) | Formula.constants(self.second)

        elif is_equality(root) or is_relation(root):
            constants = set()
            for argument in self.arguments:
                constants = constants | Term.constants(argument)
            return constants
        # Harris J. Bolus - Task 7.6a

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        root = self.root
        if is_quantifier(root):
            return Formula.variables(self.statement) | {self.variable}

        elif is_unary(root):
            return Formula.variables(self.first)

        elif is_binary(root):
            return Formula.variables(self.first) | Formula.variables(self.second)

        elif is_equality(root) or is_relation(root):
            variables = set()
            for argument in self.arguments:
                variables = variables | Term.variables(argument)
            return variables
        # Harris J. Bolus - Task 7.6b

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """
        root = self.root
        if is_quantifier(root):
            free_variables = Formula.free_variables(self.statement) - {self.variable}
            return free_variables

        elif is_unary(root):
            return Formula.free_variables(self.first)

        elif is_binary(root):
            return Formula.free_variables(self.first) | Formula.free_variables(self.second)

        elif is_equality(root) or is_relation(root):
            free_variables = set()
            for argument in self.arguments:
                free_variables = free_variables | Term.variables(argument)
            return free_variables
        # Harris J. Bolus - Task 7.6c

    def bound_variables(self) -> Set[str]:
        """Finds all variable names that are quantified in the current formula.

        Returns:
            A set of every variable name that is used in the current formula
            within a scope of a quantification on that variable name.
        """
        root = self.root
        if is_quantifier(root):
            return {self.variable} | self.statement.bound_variables()

        elif is_unary(root):
            return Formula.bound_variables(self.first)

        elif is_binary(root):
            return Formula.bound_variables(self.first) | Formula.bound_variables(self.second)

        elif is_equality(root) or is_relation(root):
            return set()

        # Personal task

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        root = self.root
        if is_quantifier(root):
            return Formula.functions(self.statement)

        elif is_unary(root):
            return Formula.functions(self.first)

        elif is_binary(root):
            return Formula.functions(self.first) | Formula.functions(self.second)

        elif is_equality(root) or is_relation(root):
            functions = set()
            for argument in self.arguments:
                functions = functions | Term.functions(argument)
            return functions
        # Harris J. Bolus - Task 7.6d

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        root = self.root
        if is_relation(root):
            return {(root, len(self.arguments))}

        elif is_quantifier(root):
            return Formula.relations(self.statement)

        elif is_unary(root):
            return Formula.relations(self.first)

        elif is_binary(root):
            return Formula.relations(self.first) | Formula.relations(self.second)

        return set()
        # Harris J. Bolus - Task 7.6e

    def quantifiers(self) -> Set[Tuple[str, str]]:
        """Finds all quantifiers in the current formula.

        Returns:
            A set of tuples of every quantifier with its associated variable name that is used in the current formula.
        """
        root = self.root
        if is_quantifier(root):
            return {(root, self.variable)} | self.statement.quantifiers()

        elif is_unary(root):
            return Formula.quantifiers(self.first)

        elif is_binary(root):
            return Formula.quantifiers(self.first) | Formula.quantifiers(self.second)

        elif is_equality(root) or is_relation(root):
            return set()
        # personal task

    def __len__(self) -> int:
        return len(self.constants()) + len(self.variables()) + len(self.quantifiers()) + len(self.functions()) + len(self.relations())
        # personal task

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
            Formula:
        """Substitutes in the current formula, each constant name `construct` or
        free occurrence of variable name `construct` that is a key in
        `substitution_map` with the term `substitution_map[construct]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current formula are substituted (i.e., those originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from `forbidden_variables`
                or a variable name occurrence that becomes bound when that term
                is substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)

        if not substitution_map:
            return self
        
        if not set(substitution_map.keys()) & (self.variables() | self.constants()):
            return self
        
        if sinners:= set.union(*[value.variables() for value in substitution_map.values()]) & forbidden_variables:
            raise ForbiddenVariableError(sinners.pop())

        if str(self) in substitution_map:
            formula = substitution_map[str(self)]
        else:
            root = self.root
            if is_unary(root):
               formula = Formula(root,
                        self.first.substitute(substitution_map, forbidden_variables))

            elif is_binary(root):
                formula = Formula(root,
                        self.first.substitute(substitution_map, forbidden_variables),
                        self.second.substitute(substitution_map, forbidden_variables))

            elif is_relation(root) or is_equality(root):
                formula = Formula(root,
                        [argument.substitute(substitution_map, forbidden_variables) for argument in self.arguments])

            else:
                forbidden_variables = set(forbidden_variables) | {self.variable}
                new_substitution_map = {key:substitution_map[key] for key in substitution_map if not key == self.variable}
                if new_substitution_map:
                    formula = Formula(root,
                            self.variable,
                            self.statement.substitute(new_substitution_map, forbidden_variables))
                else:
                    formula = self
        return formula
        # Harris J. Bolus - Task 9.2

    def propositional_skeleton(self, substitution_map=None) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation name, equality, or quantifier at its
            root with a propositional variable name, consistently such that
            multiple identical such (outermost) subformulas are substituted with
            the same propositional variable name. The propositional variable
            names used for substitution are obtained, from left to right
            (considering their first occurrence), by calling
            `next(~logic_utils.fresh_variable_name_generator)`.
            The second element of the pair is a mapping from each propositional
            variable name to the subformula for which it was substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(~Q(y)->x=7))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(~z3->z2)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(~z6->z5)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        if not substitution_map:
            substitution_map = dict()
        root = self.root
        if is_unary(root):
            first, substitution_map = self.first.propositional_skeleton(substitution_map)
            formula = PropositionalFormula(root, first)

        elif is_binary(root):
            first, substitution_map = self.first.propositional_skeleton(substitution_map)
            if self.second in substitution_map.values():
                for _tuple in substitution_map.items():
                    if self.second in _tuple:
                        second = PropositionalFormula.parse(_tuple[0])
                        break
            else:
                second, substitution_map2 = self.second.propositional_skeleton(substitution_map)
                substitution_map.update(substitution_map2)
            formula = PropositionalFormula(root, first, second)

        elif is_relation(root) or is_equality(root) or is_quantifier(root):
            if self in substitution_map.values():
                for _tuple in substitution_map.items():
                    if self in _tuple:
                        formula = PropositionalFormula(_tuple[0])
                        break
            else:
                variable = next(fresh_variable_name_generator)
                substitution_map[variable] = self
                formula = PropositionalFormula.parse(variable)
        return formula, substitution_map
        # Harris J. Bolus - Task 9.8

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) \
            -> Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond '~', '->',
                '|', '&', '+', '<->', '-|', and '-&'.
            substitution_map: mapping from each propositional variable name of
                the given propositional skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each propositional variable name with the
            formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(~z3->z2))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))

            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z9&z2)|(~z3->z2))'),
            ...     {'z2': Formula.parse('x=7'), 'z3': Formula.parse('Q(y)'),
            ...      'z9': Formula.parse('Ax[x=7]')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map

        root = skeleton.root
        if is_propositional_variable(root) and root in substitution_map:
            return substitution_map[root]
        else:
            if is_unary(root):
               return Formula(root, Formula.from_propositional_skeleton(skeleton.first, substitution_map))
            elif is_binary(root):
                return Formula(root,
                    Formula.from_propositional_skeleton(skeleton.first, substitution_map),
                    Formula.from_propositional_skeleton(skeleton.second, substitution_map))

        # Harris J. Bolus - Task 9.10

def make_formula_of_size(size: int) -> Formula:
    """Accepts an integer `size`, returns a formula of the form Exi[...Ex0[(...(L(x0,x1)&...)&L(xi,xi+1))]]] up to i = `size`. 248 is the max size I can request before an error.
    If L is defined as the less-than relation, the formula is true for statements like (0<1&(1<2&(2<3))))"""
    assert size > 0
    formula = Formula('L', [Term('x0'), Term('x1')])
    for i in range(1,size):
        formula = Formula('&', formula, Formula('L', [Term('x'+str(i)), Term('x'+str(i+1))]))
    for i in range(size+1):
        formula = Formula('E', 'x' + str(i), formula)
    return formula

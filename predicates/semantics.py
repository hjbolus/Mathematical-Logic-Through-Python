# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/semantics.py

"""Semantic analysis of predicate-logic expressions."""

from typing import AbstractSet, FrozenSet, Generic, Mapping, Tuple, TypeVar
from ..logic_utils import frozen, frozendict
from .syntax import *

#: A generic type for a universe element in a model.
T = TypeVar('T')

@frozen
class Model(Generic[T]):
    """An immutable model for predicate-logic constructs.

    Attributes:
        universe (`~typing.FrozenSet`\\[`T`]): the set of elements to which
            terms can be evaluated and over which quantifications are defined.
        constant_interpretations (`~typing.Mapping`\\[`str`, `T`]): mapping from
            each constant name to the universe element to which it evaluates.
        relation_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each relation name to its arity, or to ``-1`` if the relation is the
            empty relation.
        relation_interpretations (`~typing.Mapping`\\[`str`, `~typing.AbstractSet`\\[`~typing.Tuple`\\[`T`, ...]]]):
            mapping from each n-ary relation name to argument n-tuples (of
            universe elements) for which the relation is true.
        function_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each function name to its arity.
        function_interpretations (`~typing.Mapping`\\[`str`, `~typing.Mapping`\\[`~typing.Tuple`\\[`T`, ...], `T`]]):
            mapping from each n-ary function name to the mapping from each
            argument n-tuple (of universe elements) to the universe element that
            the function outputs given these arguments.
    """
    universe: FrozenSet[T]
    constant_interpretations: Mapping[str, T]
    relation_arities: Mapping[str, int]
    relation_interpretations: Mapping[str, AbstractSet[Tuple[T, ...]]]
    function_arities: Mapping[str, int]
    function_interpretations: Mapping[str, Mapping[Tuple[T, ...], T]]

    def __init__(self, universe: AbstractSet[T],
                 constant_interpretations: Mapping[str, T],
                 relation_interpretations:
                 Mapping[str, AbstractSet[Tuple[T, ...]]],
                 function_interpretations:
                 Mapping[str, Mapping[Tuple[T, ...], T]] = frozendict()):
        """Initializes a `Model` from its universe and constant, relation, and
        function name interpretations.

        Parameters:
            universe: the set of elements to which terms are to be evaluated
                and over which quantifications are to be defined.
            constant_interpretations: mapping from each constant name to a
                universe element to which it is to be evaluated.
            relation_interpretations: mapping from each relation name that is to
                be the name of an n-ary relation, to the argument n-tuples (of
                universe elements) for which the relation is to be true.
            function_interpretations: mapping from each function name that is to
                be the name of an n-ary function, to a mapping from each
                argument n-tuple (of universe elements) to a universe element
                that the function is to output given these arguments.
        """
        for constant in constant_interpretations:
            assert is_constant(constant), print(f'{constant} is not a valid constant name')
            assert constant_interpretations[constant] in universe, print(f'the constant {constant_interpretations[constant]} is not in the domain')
        relation_arities = {}
        for relation in relation_interpretations:
            assert is_relation(relation), print(f'{relation} is not a valid relation')
            relation_interpretation = relation_interpretations[relation]
            if len(relation_interpretation) == 0:
                arity = -1 # any
            else:
                some_arguments = next(iter(relation_interpretation))
                arity = len(some_arguments)
                for arguments in relation_interpretation:
                    assert len(arguments) == arity
                    for argument in arguments:
                        assert argument in universe
            relation_arities[relation] = arity
        function_arities = {}
        for function in function_interpretations:
            assert is_function(function), print(f'{function} is not a valid function. Function names must begin with a lowercase letter f-t and must be alphanumeric.')
            function_interpretation = function_interpretations[function]
            assert len(function_interpretation) > 0
            some_argument = next(iter(function_interpretation))
            arity = len(some_argument)
            assert arity > 0
            assert len(function_interpretation) == len(universe)**arity
            for arguments in function_interpretation:
                assert len(arguments) == arity
                for argument in arguments:
                    assert argument in universe
                assert function_interpretation[arguments] in universe
            function_arities[function] = arity

        self.universe = frozenset(universe)
        self.constant_interpretations = frozendict(constant_interpretations)
        self.relation_arities = frozendict(relation_arities)
        self.relation_interpretations = \
            frozendict({relation: frozenset(relation_interpretations[relation])
                        for relation in relation_interpretations})
        self.function_arities = frozendict(function_arities)
        self.function_interpretations = \
            frozendict({function: frozendict(function_interpretations[function])
                        for function in function_interpretations})
        self.max_cache_size = 100
        self.formula_cache = {}


    def __repr__(self) -> str:
        """Computes a string representation of the current model.

        Returns:
            A string representation of the current model.
        """
        return 'Universe=' + str(self.universe) + \
               '; Constant Interpretations=' + \
               str(self.constant_interpretations) + \
               '; Relation Interpretations=' + \
               str(self.relation_interpretations) + \
               ('; Function Interpretations=' + \
                str(self.function_interpretations)
                if len(self.function_interpretations) > 0 else '')

    def evaluate_term(self, term: Term,
                      assignment: Mapping[str, T] = frozendict()) -> T:
        """Calculates the value of the given term in the current model under the
        given assignment of values to variable names.

        Parameters:
            term: term to calculate the value of, for the constant and function
                names of which the current model has interpretations.
            assignment: mapping from each variable name in the given term to a
                universe element to which it is to be evaluated.

        Returns:
            The value (in the universe of the current model) of the given
            term in the current model under the given assignment of values to
            variable names.
        """
        assert term.constants().issubset(self.constant_interpretations.keys())
        assert term.variables().issubset(assignment.keys()), print(f'variables in term are {term.variables()}, assignment includes {assignment.keys()}')
        for function,arity in term.functions():
            assert function in self.function_interpretations and self.function_arities[function] == arity
        
        root = term.root
        if is_constant(root):
            result = self.constant_interpretations[root]
        elif is_variable(root):
            result = assignment[root]
        elif is_function(root):
            result = self.function_interpretations[root][tuple(self.evaluate_term(argument, assignment) for argument in term.arguments)]
        
        return result
        # Harris J. Bolus - Task 7.7
        
    def evaluate_formula(self, formula: Formula,
                         assignment: Mapping[str, T] = frozendict()) -> bool:
        assert formula.constants().issubset(self.constant_interpretations.keys())
        assert formula.free_variables().issubset(assignment.keys()), \
            f'in the formula {formula}, formula.free_variables() is {formula.free_variables()}, assignment.keys() is {assignment.keys()}'
        for function, arity in formula.functions():
            assert function in self.function_interpretations and \
                   self.function_arities[function] == arity
        for relation, arity in formula.relations():
            assert relation in self.relation_interpretations and \
                   self.relation_arities[relation] in {-1, arity}
        
        key = (formula, frozenset(assignment.items()))
        cache = self.formula_cache
        if key in cache:
            return cache[key]
        if len(cache) > self.max_cache_size:
            cache.pop(next(iter(cache)))
            
        root = formula.root
        if is_equality(root):
            result = self.evaluate_term(formula.arguments[0], assignment) is self.evaluate_term(formula.arguments[1], assignment)
        elif is_relation(root):
            result = tuple(self.evaluate_term(argument, assignment) for argument in formula.arguments) in self.relation_interpretations[root]
        elif is_unary(root):
            result = not self.evaluate_formula(formula.first, assignment)
        elif is_binary(root):
            if root == '&':
                result = self.evaluate_formula(formula.first, assignment) and self.evaluate_formula(formula.second, assignment)
            elif root == '|':
                result = self.evaluate_formula(formula.first, assignment) or self.evaluate_formula(formula.second, assignment)
            elif root == '->':
                result = not self.evaluate_formula(formula.first, assignment) or self.evaluate_formula(formula.second, assignment)
            elif root == '-&':
                result = not (self.evaluate_formula(formula.first, assignment) and self.evaluate_formula(formula.second, assignment))
            elif root == '-|':
                result = not (self.evaluate_formula(formula.first, assignment) or self.evaluate_formula(formula.second, assignment))
            elif root == '+':
                result = self.evaluate_formula(formula.first, assignment) != self.evaluate_formula(formula.second, assignment)
            elif root == '<->':
                result = self.evaluate_formula(formula.first, assignment) == self.evaluate_formula(formula.second, assignment)
        
        elif is_quantifier(root):
            variable = formula.variable
            new_assignments = ({variable: value} for value in self.universe)
            truth_values = (self.evaluate_formula(formula.statement, {**assignment, **new_assignment}) for new_assignment in new_assignments)
            if root == 'A':
                result = all(truth_values)
            else:
                result = any(truth_values)
                
        cache[key] = result
        return result
        # Harris J. Bolus - Task 7.8

    def find_assignments(self, formula: Formula, assignment: Mapping[str, T] = frozendict(), value: bool = True) -> Set[Formula]:
        """Returns a generator object of assignments for which the formula is true in the model"""
        
        assert is_quantifier(formula.root), print(f'{formula} is not quantified')
        variable = formula.variable
        new_assignments = ({variable:value} for value in self.universe)
        truth_values = (({**assignment, **new_assignment}, self.evaluate_formula(formula.statement, {**assignment, **new_assignment})) for new_assignment in new_assignments)
        if value:
            return [i[0] for i in truth_values if i[1]]
        else:
            return [i[0] for i in truth_values if not i[1]] #only gets the first assignment
        # Personal task

    def is_model_of(self, formulas: AbstractSet[Formula]) -> bool:
        """Checks if the current model is a model of the given formulas.

        Parameters:
            formulas: formulas to check, for the constant, function, and
                relation names of which the current model has interpretations.

        Returns:
            ``True`` if each of the given formulas evaluates to true in the
            current model under any assignment of elements from the universe of
            the current model to the free occurrences of variable names in that
            formula, ``False`` otherwise.
        """
        for formula in formulas:
            assert formula.constants().issubset(
                self.constant_interpretations.keys())
            for function,arity in formula.functions():
                assert function in self.function_interpretations and \
                       self.function_arities[function] == arity
            for relation,arity in formula.relations():
                assert relation in self.relation_interpretations and \
                       self.relation_arities[relation] in {-1, arity}
        new_formulas = set()
        for formula in formulas:
            for free_variable in formula.free_variables():
                formula = Formula('A', free_variable, formula)
            new_formulas.add(formula)
        return all(self.evaluate_formula(formula) for formula in new_formulas)
        # Harris J. Bolus - Task 7.9

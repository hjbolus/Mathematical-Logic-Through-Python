# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set
from collections import Counter
from logic_utils import fresh_variable_name_generator, is_z_and_number

from syntax import *
from semantics import *

def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function interpretations, replacing each function interpretation with a
    canonically corresponding relation interpretation.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            interpretations in this model.

    Returns:
        A model obtained from the given model by replacing every function
        interpretation of a function name with a relation interpretation of the
        canonically corresponding relation name, such that the relation
        interpretation contains any tuple
        ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1` is the
        output of the function interpretation for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_interpretations:
        assert function_name_to_relation_name(function) not in \
               model.relation_interpretations

    new_relation_interpretations = dict(model.relation_interpretations)

    for function_name in model.function_interpretations:
        new_relation_interpretations[function_name_to_relation_name(function_name)] = {(model.function_interpretations[function_name][arguments],*arguments) for arguments in model.function_interpretations[function_name]}

    return Model(model.universe, model.constant_interpretations, new_relation_interpretations, dict())
    # Task 8.1

def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function interpretations to a
    canonically corresponding model with interpretations for the given function
    names, having each new function interpretation replace a canonically
    corresponding relation interpretation.

    Parameters:
        model: model to convert, which contains no function interpretations.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has an interpretation in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    assert len(model.function_interpretations) == 0
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_interpretations
        assert function_name_to_relation_name(function) in \
               model.relation_interpretations

    new_function_interpretations = dict()
    relation_interpretations = dict(model.relation_interpretations)

    for function_name, relation_name in zip(original_functions, map(function_name_to_relation_name, original_functions)):
        relata = relation_interpretations.pop(relation_name)
        function_dict = {ntuple[1:]:ntuple[0] for ntuple in relata}

        if len(function_dict) != len(relata) or len(function_dict) != len(model.universe)**len(list(function_dict)[0]):
            return None
        else:
            new_function_interpretations[function_name] = function_dict
    return Model(model.universe, model.constant_interpretations, relation_interpretations, new_function_interpretations)
    # Task 8.2

def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names that are ``z`` followed by a number.

    Returns:
        A list of steps, each of which is a formula of the form 'y = f(x1,...,xn)',
        where `y` is a new variable name obtained by calling
        `next(logic_utils.fresh_variable_name_generator)`, `f` is a function name,
        and each of the `xi` is either a constant name or a variable name. If `xi`
        is a new variable name, then it is also the left-hand side of a previous
        step, where all of the steps "leading up to" `x1` precede those "leading
        up" to `x2`, etc. If all the returned steps hold in any model, then the
        left-hand-side variable name of the last returned step evaluates in that
        model to the value of the given term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert not is_z_and_number(variable)

    pile = []
    new_arguments = []
    for argument in term.arguments:
        if is_function(argument.root):
            for i in _compile_term(argument):
                pile.append(i)
            new_arguments.append(pile[-1].arguments[0])
        else:
            new_arguments.append(argument)
    pile.append(Formula('=',[Term.parse(next(fresh_variable_name_generator)),Term(term.root, new_arguments)]))
    return pile
    # Task 8.3

def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function interpretations.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            ``z`` followed by a number, and such that there exist no canonically
            corresponding function name and relation name that are both invoked
            in this formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    
    root = formula.root
    
    if is_relation(root) or is_equality(root):
        pile = []
        new_arguments = []
        for argument in formula.arguments:
            if is_function(argument.root):
                pile.append(_compile_term(argument))
                new_arguments.append(pile[-1][-1].arguments[0])
            else:
                new_arguments.append(argument)
        new_formula = Formula(formula.root, new_arguments)
        
        for compiled_formula in pile[::-1]:
            for step in compiled_formula[::-1]:
                new_relation = Formula(function_name_to_relation_name(step.arguments[1].root), 
                                        [step.arguments[0], *step.arguments[1].arguments])
                new_formula = Formula('E', str(step.arguments[0]), 
                                        Formula('&', new_relation, new_formula))

    elif is_binary(root):
        new_formula = Formula(formula.root,
                                replace_functions_with_relations_in_formula(formula.first),
                                replace_functions_with_relations_in_formula(formula.second))
    elif is_unary(root):
        new_formula = Formula(formula.root,
                                replace_functions_with_relations_in_formula(formula.first))
    else:
        new_formula = Formula(formula.root,
                                formula.variable,
                                replace_functions_with_relations_in_formula(formula.statement))
    return new_formula
    # Task 8.4

def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function interpretations.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with interpretations for the functions
       names of the former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names that are
            ``z`` followed by a number, and such that there exist no canonically
            corresponding function name and relation name that are both invoked
            in these formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function,arity in formula.functions()}
                           for formula in formulas]).intersection(
                               set.union(*[{relation for relation,arity in
                                            formula.relations()} for
                                           formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert not is_z_and_number(variable)
    
    new_formulas = {replace_functions_with_relations_in_formula(formula) for formula in formulas}
    
    new_relations = set.union(*[i.relations() for i in new_formulas]) - set.union(*[i.relations() for i in formulas])
    for relation in new_relations:
        arguments = [Term.parse(next(fresh_variable_name_generator)) for _ in range(relation[1]+2)]
        
        existence_formula = Formula('E', str(arguments[0]), 
                                Formula(relation[0], [arguments[0], *arguments[3:]]))
        uniqueness_formula = Formula('->',
                                Formula('&',
                                    Formula(relation[0], [arguments[1], *arguments[3:]]),
                                    Formula(relation[0], [arguments[2], *arguments[3:]])),
                                Formula('=',
                                    [arguments[1],
                                    arguments[2]]))
            
        for argument in arguments[1:]:
            existence_formula = Formula('A', str(argument), existence_formula)
            uniqueness_formula = Formula('A', str(argument), uniqueness_formula)
            
        new_formulas.add(Formula('&', existence_formula, uniqueness_formula))
    return new_formulas
    # Task 8.5

def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model of the returned formulas, the
       interpretation of the relation name ``'SAME'`` is reflexive,
       symmetric, and transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model of the returned formulas, the interpretation of this
       relation name respects the interpretation of the relation name
       ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}
    # Task 8.6

def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds an interpretation of the relation name ``'SAME'`` in the given
    model, that canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no interpretation of the relation name
            ``'SAME'``, to add the interpretation to.

    Returns:
        A model obtained from the given model by adding an interpretation of the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_interpretations
    # Task 8.7

def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    interpretation of ``'SAME'`` in the given model, in the sense that any set
    of formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function interpretations, and
            contains an interpretation of the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the
            interpretations of all other relation names.

    Returns:
        A model that is a model of any set `formulas` if and only if the given
        model is a model of
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        interpretation of ``'SAME'`` in the given model.
    """
    assert 'SAME' in model.relation_interpretations and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_interpretations) == 0
    # Task 8.8

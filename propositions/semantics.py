# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple
from syntax import *
from proofs import *
from itertools import *

#: A model for propositional-logic formulas, a mapping from variable names to truth values.
Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    if is_constant(formula.root):
        if formula.root == 'T':
            return True
        elif formula.root == 'F':
            return False
    elif is_variable(formula.root):
        return model[formula.root]
    elif is_unary(formula.root):
        return not evaluate(formula.first, model)
    elif is_binary(formula.root):
        if formula.root == '&':
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif formula.root == '|':
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == '->':
            if not evaluate(formula.first, model):
                return True
            else:
                return evaluate(formula.second, model)
        elif formula.root == '-&':
            return not (evaluate(formula.first, model) and evaluate(formula.second, model))
        elif formula.root == '-|':
            return (not evaluate(formula.first, model)) and (not evaluate(formula.second, model))
        elif formula.root == '+':
            return evaluate(formula.first, model) != evaluate(formula.second, model)
        elif formula.root == '<->':
            return evaluate(formula.first, model) == evaluate(formula.second, model)
    # Harris J. Bolus - Task 2.1

def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Parameters:
        variables: variable names over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variable names. The
        order of the models is lexicographic according to the order of the given
        variable names, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    return (({tuple(variables)[j]:i[j] for j in range(len(i))}) for i in product({False, True}, repeat=len(variables)))
    # Harris J. Bolus - Task 2.2

def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    return (evaluate(formula, model) for model in models)
    # Harris J. Bolus - Task 2.3

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    def bool_to_str(value):
        assert type(value) == bool
        return 'T' if value else 'F'
    variables = sorted(formula.variables())
    print('| ' + ' | '.join([i for i in variables]) + ' | ' + str(formula) + ' |')
    print('|-' + '-|-'.join(['-'*len(i) for i in variables]) + '-|-' + '-'*len(str(formula)) + '-|')
    for i in all_models(variables):
        print('| ' + ' | '.join([bool_to_str(i[j])+' '*(len(j)-1) for j in variables]) + ' | ' + bool_to_str(evaluate(formula,i)) + ' ' * len(str(formula)) + '|')
    # Harris J. Bolus - Task 2.4

def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    return all(truth_values(formula,all_models(Formula.variables(formula))))
    # Harris J. Bolus - Task 2.5a

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    return not any(truth_values(formula,all_models(Formula.variables(formula))))
    # Harris J. Bolus - Task 2.5b

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    return any(truth_values(formula,all_models(Formula.variables(formula))))
    # Harris J. Bolus - Task 2.5c

def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    variables = list(model.keys())
    if not model[variables[0]]:
        formula = Formula('~', Formula(variables.pop(0)))
    else:
        formula = Formula(variables.pop(0))
    while variables:
        if not model[variables[0]]:
            second = Formula('~', Formula(variables.pop(0)))
        else:
            second = Formula(variables.pop(0))
        formula = Formula('&', formula, second)
    return formula

    # Harris J. Bolus - Task 2.6

def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    variables = list(variables)
    rows = zip(all_models(variables),values)
    disjuncts = [_synthesize_for_model(i[0]) for i in rows if i[1]]
    if disjuncts:
        formula = disjuncts.pop(0)
        while disjuncts:
            formula = Formula('|',formula,disjuncts.pop(0))
    else:
        var = Formula(variables.pop(0))
        formula = Formula('&',var, Formula('~',var))
        while variables:
            second = Formula(variables.pop(0))
            second = Formula('&',second, Formula('~',second))
            formula = Formula('|',formula, second)
    return formula
    # Harris J. Bolus - Task 2.7

def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    variables = list(model.keys())
    init = True
    for i in variables:
        if init:
            if model[i]:
                formula = Formula('~',Formula(i))
                init = False
            else:
                formula = Formula(i)
                init = False
        else:
            if model[i]:
                first = Formula('~',Formula(i))
            else:
                first = Formula(i)
            formula = Formula('|', first, formula)
    return formula
    # Harris J. Bolus - Optional Task 2.8

def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    variables = list(variables)
    rows = zip(all_models(variables),values)
    conjuncts = [_synthesize_for_all_except_model(i[0]) for i in rows if not i[1]]
    if conjuncts:
        formula = conjuncts.pop(0)
        while conjuncts:
            formula = Formula('&',formula,conjuncts.pop(0))
    else:
        var = Formula(variables.pop(0))
        formula = Formula('|',var, Formula('~',var))
        while variables:
            second = Formula(variables.pop(0))
            second = Formula('|',second, Formula('~',second))
            formula = Formula('&',formula, second)
    return formula
    # Harris J. Bolus - Optional Task 2.9

def combine_formulae(formulae: Iterable[Formula], operator: str) -> Formula:
    if len(formulae) == 0:
        return formulae
    elif len(formulae) == 1:
        return formulae[0]
    else:
        return Formula(operator, formulae[0], combine_formulae(formulae[1:], operator))
    # Personal task

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    if rule.assumptions:
        formula = Formula('->', combine_formulae(rule.assumptions, '&'), rule.conclusion)
    else:
        formula = rule.conclusion
    return evaluate(formula, model)
    # Harris J. Bolus - Task 4.2

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    return all((evaluate_inference(rule, model) for model in all_models(InferenceRule.variables(rule))))
    # Harris J. Bolus - Task 4.3

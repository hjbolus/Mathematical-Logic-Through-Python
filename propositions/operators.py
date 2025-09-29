# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from .syntax import *
from .semantics import *

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
    sub_map = { 'T': Formula.parse('(p|~p)'),
                'F': Formula.parse('(p&~p)'),
                '->': Formula.parse('(~p|q)'),
                '+': Formula.parse('((p|q)&~(p&q))'),
                '-&': Formula.parse('~(p&q)'),
                '-|': Formula.parse('~(p|q)'),
                '<->': Formula.parse('((~p|q)&(~q|p))')}
    return Formula.substitute_operators(formula, sub_map)
    # Harris J. Bolus - Task 3.5

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '~' and '&'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '~' and '&'.
    """
    sub_map = { 'T': Formula.parse('~(p&~p)'),
                'F': Formula.parse('(p&~p)'),
                '|': Formula.parse('~(~p&~q)'),
                '->': Formula.parse('~(p&~q)'),
                '+': Formula.parse('(~(p&q)&~(~p&~q))'),
                '-&': Formula.parse('~(p&q)'),
                '-|': Formula.parse('(~p&~q)'),
                '<->': Formula.parse('(~(p&~q)&~(q&~p))')}
    return Formula.substitute_operators(formula, sub_map)
    # Harris J. Bolus - Task 3.6a

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '-&'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '-&'.
    """
    sub_map = { 'T': Formula.parse('(p-&(p-&p))'),
                'F': Formula.parse('((p-&(p-&p))-&(p-&(p-&p)))'),
                '~': Formula.parse('(p-&p)'),
                '&': Formula.parse('((p-&q)-&(p-&q))'),
                '|': Formula.parse('((p-&p)-&(q-&q))'),
                '->': Formula.parse('(p-&(q-&q))'),
                '+': Formula.parse('((p-&(p-&q))-&(q-&(p-&q)))'),
                '-|': Formula.parse('(((p-&p)-&(q-&q))-&((p-&p)-&(q-&q)))'),
                '<->': Formula.parse('(((p-&p)-&(q-&q))-&(p-&q))')}
    return Formula.substitute_operators(formula, sub_map)
    # Harris J. Bolus - Task 3.6b

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '->' and '~'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '->' and '~'.
    """
    sub_map = { 'T': Formula.parse('(p->p)'),
                'F': Formula.parse('~(p->p)'),
                '&': Formula.parse('~(p->~q)'),
                '|': Formula.parse('(~p->q)'),
                '+': Formula.parse('((p->q)->~(q->p))'),
                '-|': Formula.parse('~(~p->q)'),
                '-&': Formula.parse('(p->~q)'),
                '<->': Formula.parse('~((p->q)->~(q->p))')}
    return Formula.substitute_operators(formula, sub_map)
    # Harris J. Bolus - Task 3.6c

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '->' and 'F'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '->' and 'F'.
    """
    sub_map = { 'T': Formula.parse('(F->p)'),
                '~': Formula.parse('(p->F)'),
                '&': Formula.parse('((p->(q->F))->F)'),
                '|': Formula.parse('((p->q)->q)'),
                '+': Formula.parse('((p->q)->((q->p)->F))'),
                '-|': Formula.parse('(((p->q)->q)->F)'),
                '-&': Formula.parse('((p->q)->(p->F))'),
                '<->': Formula.parse('(((p->q)->((q->p)->F))->F)')}
    return Formula.substitute_operators(formula, sub_map)
    # Harris J. Bolus - Task 3.6d

def to_not_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '~' and '|'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '~' and '|'.
    """
    sub_map = { 'T': Formula.parse('(p|~p)'),
                'F': Formula.parse('~(p|~p)'),
                '&': Formula.parse('~(~p|~q)'),
                '->': Formula.parse('~(~p|q)'),
                '+': Formula.parse('(~(~p|q)|~(~q|p))'),
                '-&': Formula.parse('(~p|~q)'),
                '-|': Formula.parse('~(p|q)'),
                '<->': Formula.parse('~(~(~p|q)|~(~q|p))')}
    return Formula.substitute_operators(formula, sub_map)
    # Personal task

def to_nor(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond '-|'.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond '-|'.
    """
    sub_map = { 'T': Formula.parse('((p-|(p-|p))-|(p-|(p-|p)))'),
                'F': Formula.parse('(p-|(p-|p))'),
                '~': Formula.parse('(p-|p)'),
                '&': Formula.parse('((p-|p)-|(q-|q))'),
                '|': Formula.parse('((p-|q)-|(p-|q))'),
                '->': Formula.parse('(((p-|p)-|q)-|((p-|p)-|q))'),
                '+': Formula.parse('((p-|q)-|((p-|p)-|(q-|q)))'),
                '-&': Formula.parse('(((p-|p)-|(q-|q))-|((p-|p)-|(q-|q)))'),
                '<->': Formula.parse('((p-|(p-|q))-|(q-|(p-|q)))')}
    return Formula.substitute_operators(formula, sub_map)
    # Personal task


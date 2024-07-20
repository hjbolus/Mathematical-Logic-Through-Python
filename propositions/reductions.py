# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/reductions.py

"""Reduction between computational search problems."""

from __future__ import annotations
from typing import AbstractSet, Mapping, Tuple, Union

from syntax import *
from semantics import *
from operators import *

#: A graph on a vertex set of the form `(1, ..., n_vertices)`,
#: represented by the number of vertices `n_vertices` and a set of edges over
#: the vertices.
Graph = Tuple[int, AbstractSet[Tuple[int, int]]]

def is_graph(graph: Graph) -> bool:
    """Checks if the given data structure is a valid representation of a graph.

    Parameters:
        graph: data structure to check.

    Returns:
        ``True`` if the given data structure is a valid representation of a
        graph, ``False`` otherwise.
    """
    (n_vertices, edges) = graph
    for edge in edges:
        for vertex in edge:
            if not 1 <= vertex <= n_vertices:
                return False
        if edge[0] == edge[1]:
            return False
    return True

def is_valid_3coloring(graph: Graph, coloring: Mapping[int, int]) -> bool:
    """Checks whether the given coloring is a valid coloring of the given graph
    by the colors 1, 2, and 3.

    Parameters:
        graph: graph to check.
        coloring: mapping from the vertices of the given graph to colors,
            to check.

    Returns:
        ``True`` if the given coloring is a valid coloring of the given graph by
        the colors 1, 2, and 3; ``False`` otherwise.
    """
    assert is_graph(graph)
    (n_vertices, edges) = graph
    for vertex in range(1, n_vertices + 1):
        if vertex not in coloring.keys() or coloring[vertex] not in {1, 2, 3}:
            return False
    for edge in edges:
        if coloring[edge[0]] == coloring[edge[1]]:
            return False
    return True

def graph3coloring_to_formula(graph: Graph) -> Formula:
    """Efficiently reduces the 3-coloring problem of the given graph into a
    satisfiability problem.

    Parameters:
        graph: graph whose 3-coloring problem to reduce.

    Returns:
        A propositional formula that is satisfiable if and only if the given
        graph is 3-colorable.
    """
    assert is_graph(graph)
    (n_vertices, edges) = graph
    colors = ('1','2','3')
    formula = None

    for node in range(1,n_vertices+1):
        variables = ['x'+str(node)+color for color in colors]
        nodeformula = Formula(variables[0])

        for variable in variables[1:]:
            nodeformula = Formula('|',nodeformula,Formula(variable))

        for i,j in combinations(variables,2):
            tempformula = Formula('|',Formula('~',Formula(i)),Formula('~',Formula(j)))
            nodeformula = Formula('&',nodeformula,tempformula)

        if not formula:
            formula = nodeformula
        else:
            formula = Formula('&',formula,nodeformula)

    for node_0,node_1 in edges:
        variables = zip(('x'+str(node_0)+color for color in colors),('x'+str(node_1)+color for color in colors))
        for source,target in variables:
            formula = Formula('&', formula, Formula('|', Formula('~', Formula(source)), Formula('~', Formula(target))))

    return formula

    # Harris J. Bolus - Optional Task 2.10a

def assignment_to_3coloring(graph: Graph, assignment: Model) -> \
        Mapping[int, int]:
    """Efficiently transforms an assignment to the formula corresponding to the
    3-coloring problem of the given graph, to a 3-coloring of the given graph so
    that the 3-coloring is valid if and only if the given assignment is
    satisfying.

    Parameters:
        graph: graph to produce a 3-coloring for.
        assignment: assignment to the variable names of the formula returned by
            `graph3coloring_to_formula(graph)`.

    Returns:
        A 3-coloring of the given graph by the colors 1, 2, and 3 that is valid
        if and only if the given assignment satisfies the formula
        `graph3coloring_to_formula(graph)`.
    """
    assert is_graph(graph)
    formula = graph3coloring_to_formula(graph)
    assert evaluate(formula, assignment)

    mapping = dict()
    for i in formula.variables():
        if assignment[i]:
            mapping[int(i[1:-1])] = int(i[-1])
    return mapping
    # Harris J. Bolus - Optional Task 2.10b

def tricolor_graph(graph: Graph) -> Union[Mapping[int, int], None]:
    """Computes a 3-coloring of the given graph.

    Parameters:
        graph: graph to 3-color.

    Returns:
        An arbitrary 3-coloring of the given graph if it is 3-colorable,
        ``None`` otherwise.
    """
    assert is_graph(graph)
    formula = graph3coloring_to_formula(graph)
    for assignment in all_models(list(formula.variables())):
        if evaluate(formula, assignment):
            return assignment_to_3coloring(graph, assignment)
    return None

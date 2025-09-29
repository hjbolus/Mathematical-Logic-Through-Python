# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Sequence, Union
from ..logic_utils import frozendict
from .syntax import *
from .semantics import *
from .proofs import *
from .axiomatic_systems import *
from .deduction import *
from .operators import *
from functools import reduce

def formulas_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulas that capture the given model: ``'``\ `x`\ ``'``
    for each variable name `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable name `x` that is assigned
    the value ``False``.

    Parameters:
        model: model to construct the formulas for.

    Returns:
        A list of the constructed formulas, ordered alphabetically by variable
        name.

    Examples:
        >>> formulas_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    list1 = []
    variables = sorted(model.keys())
    for i in variables:
        if model[i]:
            list1.append(Formula.parse(i))
        else:
            list1.append(Formula('~',Formula.parse(i)))
    return list1
    # Harris J. Bolus - Task 6.1a

def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p->q7)
        >>> proof.statement.assumptions
        (~p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p->q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)

    assumptions = formulas_capturing_model(model)
    rules = AXIOMATIC_SYSTEM
    root = formula.root
    
    if is_variable(root):
        if evaluate(formula, model):
            conclusion = formula
        else:
            conclusion = Formula('~', formula)

        line = [Proof.Line(conclusion)]
        statement = InferenceRule(assumptions, conclusion)
        proof = Proof(statement, rules, line)
        return proof

    elif root == '~':
        if evaluate(formula, model):
            return prove_in_model(formula.first, model)
        else:
            proof = prove_in_model(formula.first, model)
            consequent = Formula('~', formula)
            conditional = NN
            return prove_corollary(proof, consequent, conditional)

    elif root == '->':
        if evaluate(formula, model):
            if not evaluate(formula.first, model):
                proof = prove_in_model(Formula('~', formula.first), model)
                consequent = I2.specialize({'p': formula.first, 'q': formula.second}).conclusion.second
                conditional = I2
                return prove_corollary(proof, consequent, conditional)

            else:
                proof = prove_in_model(formula.second, model)
                consequent = I1.specialize({'p': formula.first, 'q': formula.second}).conclusion.second
                conditional = I1
                return prove_corollary(proof, consequent, conditional)

        else:
            proof1 = prove_in_model(formula.first, model)
            proof2 = prove_in_model(Formula('~', formula.second), model)
            consequent = Formula('~', formula)
            return combine_proofs(proof1, proof2, consequent, NI)
    # Harris J. Bolus - Task 6.1b

def reduce_assumption(proof_from_affirmation: Proof, proof_from_negation: Proof) -> Proof:
    """Combines the two given proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_from_negation: valid proof of `conclusion` from the same
            assumptions and inference rules of `proof_from_affirmation`, but
            with the last assumption being ``'~``\ `assumption`\ ``'`` instead
            of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If `proof_from_affirmation` is of
                       ``['p', '~q', 'r'] ==> '(p&(r|~r))'``, then `proof_from_negation` must be of
                       ``['p', '~q', '~r'] ==> '(p&(r|~r))'`` and the returned proof is of
                       ``['p', '~q'] ==> '(p&(r|~r))'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules

    return combine_proofs(remove_assumption(proof_from_affirmation),
                          remove_assumption(proof_from_negation),
                          proof_from_affirmation.statement.conclusion,
                          R)

    # Harris J. Bolus - Task 6.2

def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulas that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variable names of `tautology`, from whose
            formulas to prove.

    Returns:
        A valid proof of the given tautology from the formulas that capture the
        given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'),
        ...                         {'p': True, 'q': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        (p, ~q)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'))
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        ()
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())

    if sorted(tautology.variables()) == sorted(model.keys()):
        return prove_in_model(tautology, model)
    else:
        model = dict(model)
        model_copy = {i: model[i] for i in model.keys()}
        next_variable = sorted(tautology.variables())[len(model)]

        model.update({next_variable: True})
        model_copy.update({next_variable: False})

        return reduce_assumption(prove_tautology(tautology, model),
                                 prove_tautology(tautology, model_copy))
    # Harris J. Bolus - Task 6.3a

def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    if is_tautology(formula):
        return prove_tautology(formula)
    else:
        for i in all_models(formula.variables()):
            if not evaluate(formula, i):
                return i
    # Harris J. Bolus - Task 6.3b

def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))

        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """

    if rule.assumptions:
        new_assumptions = rule.assumptions[:-1]
        new_conclusion = Formula('->', rule.assumptions[-1], rule.conclusion)
        return encode_as_formula(InferenceRule(new_assumptions, new_conclusion))
    else:
        return rule.conclusion
    # Harris J. Bolus - Task 6.4a

def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in {rule.conclusion}.union(rule.assumptions):
        assert formula.operators().issubset({'->', '~'})

    encoding = encode_as_formula(rule)

    rules = AXIOMATIC_SYSTEM
    lines = list(prove_tautology(encoding).lines)

    n = len(lines)
    for assumption in rule.assumptions:
        encoding = encoding.second
        lines.append(Proof.Line(assumption))
        lines.append(Proof.Line(encoding, MP, (n, n-1)))
        n += 2

    return Proof(rule, rules, lines)
    # Harris J. Bolus - Task 6.4b

def model_or_inconsistency(formulae: Sequence[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulas hold, or proves
    ``'~(p->p)'`` from these formulas.

    Parameters:
        formulas: formulas that use only the operators ``'->'`` and ``'~'``, to
            either find a model of, or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulas hold if such exists,
        otherwise a valid proof of ``'~(p->p)'`` from the given formulas via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})

    variables = reduce(lambda x, y: x | y, (set(formula.variables()) for formula in formulae))
    models = all_models(variables)

    for formula in formulae:
        models = [model for model in models if evaluate(formula, model)]

    if models:
        return models[0]
    else:
        return prove_sound_inference(InferenceRule(formulae, Formula.parse('~(p->p)')))
    # Harris J. Bolus - Task 6.5

def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'`` (and may contain constants), whose affirmation
            or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If `formula` evaluates to ``True`` in the given model, then a valid
        proof of `formula`; otherwise a valid proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulas that capture the given model, in
        the order returned by `formulas_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.

    Examples:
        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': True, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p&q7)
        >>> proof.statement.assumptions
        (p, q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True

        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p&q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    
    assumptions = formulas_capturing_model(model)
    rules = AXIOMATIC_SYSTEM_FULL
    root = formula.root
    
    if is_variable(root):
        if evaluate(formula, model):
            conclusion = formula
        else:
            conclusion = Formula('~', formula)

        line = [Proof.Line(conclusion)]
        statement = InferenceRule(assumptions, conclusion)
        proof = Proof(statement, rules, line)
        return proof

    elif root == '~':
        if evaluate(formula, model):
            return prove_in_model_full(formula.first, model)
        else:
            proof = prove_in_model_full(formula.first, model)
            consequent = Formula('~', formula)
            conditional = NN
            return prove_corollary(proof, consequent, conditional)

    elif root == '->':
        if evaluate(formula, model):
            if not evaluate(formula.first, model):
                proof = prove_in_model_full(Formula('~', formula.first), model)
                consequent = I2.specialize({'p': formula.first, 'q': formula.second}).conclusion.second
                conditional = I2
                return prove_corollary(proof, consequent, conditional)

            else:
                proof = prove_in_model_full(formula.second, model)
                consequent = I1.specialize({'p': formula.first, 'q': formula.second}).conclusion.second
                conditional = I1
                return prove_corollary(proof, consequent, conditional)

        else:
            proof1 = prove_in_model_full(formula.first, model)
            proof2 = prove_in_model_full(Formula('~', formula.second), model)
            consequent = Formula('~', formula)
            return combine_proofs(proof1, proof2, consequent, NI)
    
    elif root == '&':
        if evaluate(formula, model):
            proof1 = prove_in_model_full(formula.first, model)
            proof2 = prove_in_model_full(formula.second, model)
            consequent = formula
            double_conditional = A
            return combine_proofs(proof1, proof2, consequent, double_conditional)
            
        else:
            if evaluate(formula.first, model):
                proof = prove_in_model_full(Formula('~', formula.second), model)
                consequent = Formula('~', formula)
                conditional = NA1
                return prove_corollary(proof, consequent, conditional)
                
            else:
                proof = prove_in_model_full(Formula('~', formula.first), model)
                consequent = Formula('~', formula)
                conditional = NA2
                return prove_corollary(proof, consequent, conditional)
    
    elif root == '|':
        if evaluate(formula, model):
            if evaluate(formula.first, model):
                proof = prove_in_model_full(formula.first, model)
                consequent = formula
                conditional = O2
                return prove_corollary(proof, consequent, conditional)
                
            else:
                proof = prove_in_model_full(formula.second, model)
                consequent = formula
                conditional = O1
                return prove_corollary(proof, consequent, conditional)
        else:
            proof1 = prove_in_model_full(Formula('~', formula.first), model)
            proof2 = prove_in_model_full(Formula('~', formula.second), model)
            consequent = Formula('~', formula)
            double_conditional = NO
            return combine_proofs(proof1, proof2, consequent, double_conditional)
            
    elif root == 'T':
        line = [Proof.Line(formula, T, ())]
        statement = T
        return Proof(statement, rules, line)
    
    else:
        assert root == 'F'
        line = [Proof.Line(Formula('~', formula), NF, ())]
        statement = NF
        return Proof(statement, rules, line)
    # Harris J. Bolus - Optional Task 6.6

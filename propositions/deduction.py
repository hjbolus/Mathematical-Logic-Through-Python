# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from syntax import *
from proofs import *
from axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)

    new_statement = InferenceRule(list(antecedent_proof.statement.assumptions), consequent)

    new_rules = antecedent_proof.rules | set((MP, conditional))

    specialized_conditional = Formula('->', antecedent_proof.statement.conclusion, consequent)

    n = len(antecedent_proof.lines)

    new_lines = list(antecedent_proof.lines)
    new_lines.append(Proof.Line(specialized_conditional, conditional, []))
    new_lines.append(Proof.Line(consequent, MP, [n-1,n]))

    return Proof(new_statement, new_rules, new_lines)
    # Task 5.3a

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)

    new_statement = InferenceRule((antecedent1_proof.statement.assumptions + tuple(set(antecedent2_proof.statement.assumptions)-set(antecedent1_proof.statement.assumptions))),consequent)

    new_rules = antecedent1_proof.rules | antecedent2_proof.rules | set((MP, double_conditional))

    n = len(antecedent1_proof.lines)
    m = len(antecedent2_proof.lines)

    specialized_double_conditional = Formula('->', antecedent1_proof.statement.conclusion, Formula('->', antecedent2_proof.statement.conclusion, consequent))
    specialized_single_conditional = specialized_double_conditional.second

    new_lines1 = list(antecedent1_proof.lines)
    new_lines2 = [line if line.is_assumption() else Proof.Line(line.formula, line.rule, [assumption+n for assumption in line.assumptions]) for line in antecedent2_proof.lines]
    new_lines = new_lines1 + new_lines2

    new_lines.append(Proof.Line(specialized_double_conditional, double_conditional, []))
    new_lines.append(Proof.Line(specialized_single_conditional, MP, [n-1,n+m]))
    new_lines.append(Proof.Line(consequent, MP, [n+m-1, n+m+1]))

    return Proof(new_statement, new_rules, new_lines)
    # Task 5.3b

def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0

    phi = proof.statement.assumptions[-1]
    phi_I0 = Formula('->', phi, phi)

    new_lines = []
    line_index = []

    for i in range(len(proof.lines)):
        line = proof.lines[i]

        if line.formula == phi:
            line_index.append(i)
            new_lines.append(Proof.Line(phi_I0, I0, []))

        elif line.is_assumption() or len(line.rule.assumptions) == 0:
            [line_index.append(i) for j in range(3)]
            q = line.formula

            new_lines.append(line)
            new_lines.append(Proof.Line(I1.specialize({'p': phi, 'q': q}).conclusion, I1, []))
            new_lines.append(Proof.Line(Formula('->', phi, q), MP, [len(new_lines)-2, len(new_lines)-1]))

        else:
            [line_index.append(i) for j in range(3)]
            n = len(new_lines)
            q = proof.lines[line.assumptions[1]].formula.first

            new_lines.append(Proof.Line(D.specialize({'p': phi, 'q': q, 'r': line.formula}).conclusion, D, []))

            antecedent_1 = new_lines[-1].formula.first
            for line_number in range(len(new_lines)):
                if new_lines[line_number].formula == antecedent_1:
                    p1_1 = line_number
                    break
            new_lines.append(Proof.Line(new_lines[-1].formula.second, MP, [p1_1, n]))

            antecedent_2 = new_lines[-1].formula.first
            for line_number in range(len(new_lines)):
                if new_lines[line_number].formula == antecedent_2:
                    p1_2 = line_number
                    break
            new_lines.append(Proof.Line(new_lines[-1].formula.second, MP, [p1_2, n+1]))

    new_statement = InferenceRule((proof.statement.assumptions[:-1]), Formula('->',proof.statement.assumptions[-1],proof.statement.conclusion))
    new_rules = proof.rules | set((I0, D, I1, MP))

    return Proof(new_statement, new_rules, new_lines)
    # Task 5.4

def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules

    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)
    # Task 5.6

def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0

    r = proof.statement.assumptions[-1].first

    proof = remove_assumption(proof)
    proof = prove_corollary(proof, Formula('->',Formula.parse('(p->p)'), r), N)
    new_statement = InferenceRule(proof.statement.assumptions, r)

    n = len(proof.lines)
    new_lines = list(proof.lines)
    new_lines.append(Proof.Line(Formula.parse('(p->p)'), I0, []))
    new_lines.append(proof.Line(r, MP, [n, n-1]))

    return Proof(new_statement, proof.rules, new_lines)
    # Task 5.7

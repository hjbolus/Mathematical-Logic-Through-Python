# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""
import sys
sys.path.append('/Users/harrisbolus/Desktop/Fun/Mathematical logic thru python')
from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of '(assumption->conclusion)' from the
    same assumptions except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.
        print_as_proof_forms: flag specifying whether the proof of
            '(assumption`->conclusion)' is to be printed in real time as it is
            being created.

    Returns:
        A valid proof of '(assumption->conclusion)'
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()

    prover = Prover(proof.assumptions-{Schema(assumption)},print_as_proof_forms)
    
    for number, line in enumerate(proof.lines):
        if isinstance(line, Proof.AssumptionLine):
            if line.formula == assumption:
                step = prover.add_tautology(Formula('->', assumption, assumption))
            else:
                step = prover.add_instantiated_assumption(line.formula, line.assumption, line.instantiation_map)
                step = prover.add_tautological_implication(Formula('->', assumption, line.formula), [step])

        elif isinstance(line, Proof.TautologyLine):
            step = prover.add_tautology(line.formula)
            step = prover.add_tautology(Formula('->', assumption, line.formula))

        elif isinstance(line, Proof.MPLine):
            antecedent = Formula('->', assumption, proof.lines[line.antecedent_line_number].formula)
            conditional = Formula('->', assumption, proof.lines[line.conditional_line_number].formula)
            consequent = Formula('->', assumption, line.formula)
            antecedent_line_number = None
            conditional_line_number = None
            for line_number, temp_line in enumerate(prover._lines):
                if not antecedent_line_number:
                    if temp_line.formula == antecedent:
                        antecedent_line_number = line_number
                if not conditional_line_number:
                    if temp_line.formula == conditional:
                        conditional_line_number = line_number
                if antecedent_line_number and conditional_line_number:
                    break
            assert isinstance(antecedent_line_number, int) and isinstance(conditional_line_number, int), print('Missing antecedent or conditional. Antecedent_line_number: ', antecedent_line_number, 'conditional_line_number: ', conditional_line_number)
            step = prover.add_tautological_implication(consequent, {antecedent_line_number, conditional_line_number})
            
        else:
            assert isinstance(line, Proof.UGLine)
            nonquantified_line_number = None
            nonquantified_formula = proof.lines[line.nonquantified_line_number].formula
            new_nonquantified_line_number = None
            new_nonquantified_formula = Formula('->', assumption, nonquantified_formula)
            
            for line_number, temp_line in enumerate(prover._lines):
                if temp_line.formula == nonquantified_formula:
                    nonquantified_line_number = line_number
                    break
                
            if nonquantified_line_number == None:
                for line_number, temp_line in enumerate(prover._lines):
                    if temp_line.formula == new_nonquantified_formula:
                        new_nonquantified_line_number = line_number
                        break
                step1 = prover.add_ug(Formula('A', line.formula.variable, new_nonquantified_formula), new_nonquantified_line_number)
                inst_map = {'Q': assumption, 'R': nonquantified_formula.substitute({line.formula.variable:Term('_')}), 'x': line.formula.variable}
                step2 = prover.add_instantiated_assumption(Prover.US.instantiate(inst_map), Prover.US, inst_map)
                step = prover.add_mp(prover._lines[step2].formula.second, step1, step2)
            else:
                step = prover.add_ug(line.formula, nonquantified_line_number)
                step = prover.add_tautological_implication(Formula('->', assumption, line.formula), {step})
    return prover.qed().clean()
    # Harris J. Bolus - Task 11.1

def prove_by_way_of_contradiction(proof: Proof, assumption: Formula) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    conditional_proof = remove_assumption(proof, assumption)
    prover = Prover(conditional_proof.assumptions)
    conditional = prover.add_proof(conditional_proof.conclusion, conditional_proof)
    prover.add_tautological_implication(Formula('~', assumption), {conditional})
    return prover.qed()
    # Harris J. Bolus - Task 11.2

# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, List, Mapping, Optional, Sequence, Set, Tuple, Union
from syntax import *

import sys
sys.path.append('/Users/harrisbolus/Desktop/Fun/Mathematical logic thru python')
from logic_utils import frozen, memoized_parameterless_method

#: A mapping from variable names to formulas.
SpecializationMap = Mapping[str, Formula]

@frozen
class InferenceRule:
    """An immutable inference rule in Propositional Logic, comprised of zero
    or more assumed propositional formulas, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Sequence[Formula], conclusion: Formula):
        """Initializes an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + ' ==> ' + "'" + str(self.conclusion) + "'"

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return isinstance(other, InferenceRule) and \
               self.assumptions == other.assumptions and \
               self.conclusion == other.conclusion

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def variables(self) -> Set[str]:
        """Finds all variable names in the current inference rule.

        Returns:
            A set of all variable names used in the assumptions and in the
            conclusion of the current inference rule.
        """
        variable_list = set()
        for assumption in self.assumptions:
            variable_list = variable_list | Formula.variables(assumption)
        return variable_list | Formula.variables(self.conclusion)
        # Task 4.1

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable name `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """
        for variable in specialization_map:
            assert is_variable(variable)

        specialized_assumptions = (Formula.substitute_variables(assumption, specialization_map) for assumption in self.assumptions)
        specialized_conclusion = Formula.substitute_variables(self.conclusion, specialization_map)
        return InferenceRule(specialized_assumptions, specialized_conclusion)
        # Task 4.4

    @staticmethod
    def _merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps while checking their
        consistency.

        Parameters:
            specialization_map1: first mapping to merge, or ``None``.
            specialization_map2: second mapping to merge, or ``None``.

        Returns:
            A single mapping containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        else:
            return None
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        else:
            return None

        map1 = dict(specialization_map1)

        intersection = set(specialization_map1.keys()) & set(specialization_map2.keys())
        for key in intersection:
            if specialization_map1[key] != specialization_map2[key]:
                return None

        difference = set(specialization_map2.keys()) - set(specialization_map1.keys())
        for key in difference:
            map1[key] = specialization_map2[key]

        return map1
        # Task 4.5a

    @staticmethod
    def _formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        #1. Break them down by tree structure until one operand is a variable, then close that branch.
        map1 = dict()
        if is_variable(general.root):
            map1 = {general.root: specialization}
            return map1

        elif is_constant(general.root):
            if general.root == specialization.root:
                return {}
            else:
                return None

        if general.root == specialization.root:
            if is_unary(general.root):
                map2 = InferenceRule._formula_specialization_map(general.first, specialization.first)
                if map2 != None:
                    map1 = InferenceRule._merge_specialization_maps(map1, map2)
                    return map1
                else:
                    return None

            elif is_binary(general.root):
                map2 = InferenceRule._formula_specialization_map(general.first, specialization.first)
                map3 = InferenceRule._formula_specialization_map(general.second, specialization.second)

                if map2 != None and map3 != None:
                    map1 = InferenceRule._merge_specialization_maps(map1, map2)
                    map1 = InferenceRule._merge_specialization_maps(map1, map3)
                    return map1

                else:
                    return None
        else:
            return None
        # Task 4.5b

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        map1 = dict()
        if len(self.assumptions) == len(specialization.assumptions):
            for i,j in zip(self.assumptions, specialization.assumptions):
                map1 = InferenceRule._merge_specialization_maps(map1, InferenceRule._formula_specialization_map(i,j))
        else:
            return None
        map1 = InferenceRule._merge_specialization_maps(map1, InferenceRule._formula_specialization_map(self.conclusion,specialization.conclusion))
        return map1 if map1 else None
        # Task 4.5c

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None

@frozen
class Proof:
    """An immutable deductive proof in Propositional Logic, comprised of a
    statement in the form of an inference rule, a set of inference rules that
    may be used in the proof, and a list of lines that prove the statement via
    these inference rules.

    Attributes:
        statement (`InferenceRule`): the statement proven by the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement to be proven by the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula that
        is justified either as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule,
                out of those allowed in the proof, that has a specialization
                that concludes the formula; or ``None`` if the formula is
                justified as an assumption of the proof.
            assumptions (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): tuple
                of zero or more numbers of previous lines in the proof whose
                formulas are the respective assumptions of the specialization of
                the rule that concludes the formula, if the formula is not
                justified as an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Sequence[int]] = None):
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and numbers of justifying previous lines.

            Parameters:
                formula: the formula to be justified by the line.
                rule: the inference rule, out of those allowed in the proof,
                    that has a specialization that concludes the formula; or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
                assumptions: numbers of previous lines in the proof whose
                    formulas are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                r = str(self.formula) + '    (Inference Rule ' + str(self.rule)
                if len(self.assumptions) == 1:
                    r += ' on line ' + str(self.assumptions[0])
                elif len(self.assumptions) > 1:
                    r += ' on lines ' + ','.join(map(str, self.assumptions))
                r += ')'
                return r

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += "QED\n"
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulas justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: number of the line according to which to compute the
                inference rule.

        Returns:
            The computed inference rule, with assumptions ordered in the order
            of their numbers in the specified line, or ``None`` if the specified
            line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        if Proof.Line.is_assumption(self.lines[line_number]):
            return None
        else:
            assumptions = list()
            for assumption in self.lines[line_number].assumptions:
                assumptions.append(self.lines[assumption].formula)
            conclusion = self.lines[line_number].formula
            return InferenceRule(assumptions, conclusion)
        # Task 4.6a

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: number of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            ``True`` if the rule specified for that line is one of the allowed
            inference rules in the current proof, and it has a specialization
            that satisfies all of the following:

            1. The conclusion of that specialization is the formula justified by
               that line.
            2. The assumptions of this specialization are the formulas justified
               by the lines that are specified as the assumptions of that line
               (in the order of their numbers in that line), all of which must
               be previous lines.
        """
        assert line_number < len(self.lines)
        line = self.lines[line_number]
        if Proof.Line.is_assumption(line):
            return any(str(line) == str(assumption) for assumption in self.statement.assumptions)

        else:
            rule_was_given = any(line.rule == rule for rule in self.rules)
            rule_matches_line = Proof.rule_for_line(self, line_number).is_specialization_of(line.rule)
            assumptions_are_prior = all(assumption < line_number for assumption in line.assumptions)
            assumptions_match_line = all(i == j for i,j in zip([self.lines[k].formula for k in line.assumptions], Proof.rule_for_line(self, line_number).assumptions))
            return rule_was_given and rule_matches_line and assumptions_are_prior and assumptions_match_line
        # Task 4.6b

    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        if self.lines:
            each_line_is_valid = all(self.is_line_valid(line) for line in range(len(self.lines)))
            if not each_line_is_valid:
                print([self.is_line_valid(line) for line in range(len(self.lines))])
            conclusion_matches = self.statement.conclusion == self.lines[-1].formula
            if not conclusion_matches:
                print(self.statement.conclusion, ' != ', self.lines[-1].formula)
            return each_line_is_valid and conclusion_matches
        return False
        # Task 4.6c

def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule to a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the rule proven by the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)

    sub_map = proof.statement.specialization_map(specialization)
    specialized_statement = proof.statement.specialize(sub_map)
    specialized_lines = [Proof.Line(line.formula.substitute_variables(sub_map), line.rule, line.assumptions) if not Proof.Line.is_assumption(line) else Proof.Line(line.formula.substitute_variables(sub_map)) for line in proof.lines ]

    proof1 = Proof(specialized_statement, proof.rules, specialized_lines)

    return proof1
    # Task 5.1

def _inline_proof_once(main_proof: Proof, line_number: int,
                       lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: number of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating justification line numbers specified throughout the proof
        to maintain the validity of the proof. The set of allowed inference
        rules in the returned proof is the union of the rules allowed in the two
        given proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.is_valid()
    assert line_number < len(main_proof.lines)
    assert str(main_proof.lines[line_number].rule) == str(lemma_proof.statement)
    assert lemma_proof.is_valid()

    s_lemma_proof = prove_specialization(lemma_proof, Proof.rule_for_line(main_proof, line_number))
    adjustment = len(lemma_proof.lines)-1

    new_lines = []
    for i in range(line_number):
        new_lines.append(main_proof.lines[i])

    for line in s_lemma_proof.lines:
        if not Proof.Line.is_assumption(line):
            rule = line.rule
            assumptions = [assumption+line_number for assumption in line.assumptions]
            new_lines.append(Proof.Line(line.formula, rule, assumptions))
        else:
            if not line.formula in main_proof.statement.assumptions:
                for earlier_line in main_proof.lines:
                    if line.formula == earlier_line.formula:
                        rule, assumptions = earlier_line.rule, earlier_line.assumptions
                        break
                new_lines.append(Proof.Line(line.formula, rule, assumptions))
            else:
                new_lines.append(line)

    for i in range(line_number+1, len(main_proof.lines)):
        if not Proof.Line.is_assumption(main_proof.lines[i]):
            formula = main_proof.lines[i].formula
            rule = main_proof.lines[i].rule
            assumptions = [assumption+adjustment if assumption >= line_number else assumption for assumption in main_proof.lines[i].assumptions]
            new_lines.append(Proof.Line(formula, rule, assumptions))
        else:
            new_lines.append(main_proof.lines[i])
    new_rules = set(lemma_proof.rules).union(set(main_proof.rules))
    proof1 = Proof(main_proof.statement, new_rules, new_lines)
    return proof1

    # Task 5.2a

def uses_rule(proof: Proof, rule: InferenceRule) -> bool:
    """Returns True if the given proof uses the given rule.
    """
    return any((line.rule == rule for line in proof.lines))

def find_first_use_of_rule(proof: Proof, rule: InferenceRule) -> int:
    """Returns the number of the first line that uses the given inference rule.
    """
    for i in range(len(proof.lines)):
        if proof.lines[i].rule == rule:
            return i
    else:
        return false

def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specializations
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    assert main_proof.is_valid()
    assert lemma_proof.is_valid()

    new_rules = set(rule for rule in main_proof.rules if rule != lemma_proof.statement).union(lemma_proof.rules)

    new_proof = _inline_proof_once(main_proof, find_first_use_of_rule(main_proof, lemma_proof.statement), lemma_proof)
    while uses_rule(new_proof, lemma_proof.statement):
        new_proof = _inline_proof_once(new_proof, find_first_use_of_rule(new_proof, lemma_proof.statement), lemma_proof)
    proof1 = Proof(main_proof.statement, new_rules, new_proof.lines)
    return proof1
    # Task 5.2b

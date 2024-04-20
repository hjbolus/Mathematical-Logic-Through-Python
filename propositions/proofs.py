# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""
from __future__ import annotations
from typing import AbstractSet, FrozenSet, List, Mapping, Optional, Sequence, Set, Tuple, Union
from logic_utils import frozen, memoized_parameterless_method
from syntax import *

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
            rule_matches_line = Proof.rule_for_line(self, line_number).is_specialization_of(line.rule) or Proof.rule_for_line(self, line_number) == line.rule
            assumptions_are_prior = all(assumption < line_number for assumption in line.assumptions)
            assumptions_match_line = all(i == j for i,j in zip([self.lines[k].formula for k in line.assumptions], Proof.rule_for_line(self, line_number).assumptions))
            if not rule_was_given:
                print(f'rule was not given: {line}')
            if not rule_matches_line:
                print(f'rule does not match formula: {line}')
            if not assumptions_are_prior:
                print(f'assumptions are not found on prior lines: {line}')
            if not assumptions_match_line:
                print(f'assumptions do not match formula: {line}')
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
                print([(str(line)+': '+str(self.is_line_valid(line))) for line in range(len(self.lines)) if not self.is_line_valid(line)])
            conclusion_matches = self.statement.conclusion == self.lines[-1].formula
            if not conclusion_matches:
                print('statement ' + str(self.statement.conclusion) + ' != conclusion ' + str(self.lines[-1].formula))
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
    return Proof(main_proof.statement, new_rules, new_lines)

    # Task 5.2a

def uses_rule(proof: Proof, rule: InferenceRule) -> bool:
    """Returns True if the given proof uses the given rule.
    """
    return any((line.rule == rule for line in proof.lines))
    # Personal task

def find_first_use_of_rule(proof: Proof, rule: InferenceRule) -> int:
    """Returns the number of the first line that uses the given inference rule.
    """
    for i in range(len(proof.lines)):
        if proof.lines[i].rule == rule:
            return i
    else:
        return False
    # Personal task

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
    assert main_proof.is_valid(), print('\n******************** invalid proof ********************\n', main_proof, '\n***************************************************\n')
    assert lemma_proof.is_valid()

    new_rules = set(rule for rule in main_proof.rules if rule != lemma_proof.statement).union(lemma_proof.rules)

    new_proof = _inline_proof_once(main_proof, find_first_use_of_rule(main_proof, lemma_proof.statement), lemma_proof)
    while uses_rule(new_proof, lemma_proof.statement):
        new_proof = _inline_proof_once(new_proof, find_first_use_of_rule(new_proof, lemma_proof.statement), lemma_proof)
    proof1 = Proof(main_proof.statement, new_rules, new_proof.lines)
    return proof1
    # Task 5.2b

def parse_inference_rule(text:str) -> InferenceRule:
    """Converts a copied-and-pasted string from an inference rule object into an InferenceRule object"""

    assumption_str = text.split("[")[1].replace("'","").split("]")[0].split(",")
    if assumption_str == ['']:
        st_assumptions = []
    else:
        st_assumptions = [Formula.parse(i.replace("'",'').replace(" ",'')) for i in assumption_str]
    st_conclusion = Formula.parse(text.split("==> '")[1].split("'")[0])
    return InferenceRule(st_assumptions, st_conclusion)
    # Personal task

def parse_proof(text: list[str]) -> Proof:
    """Converts a copied-and-pasted string from a proof object, with triple quotes added to the start and end , into a Proof object"""

    text = text.split('\n')

    statement = parse_inference_rule(text[0])

    rules = []
    lines = []
    on_rules = True
    for i in text[1:]:
        if on_rules:
            if 'Lines' in i:
                on_rules = False
                continue
            rules.append(parse_inference_rule(i))
        elif 'QED' in i:
            break
        else:
            afternumber = ')'.join(i.split(')')[1:])
            formula = afternumber.split(' ')[1]
            try:
                formula = Formula.parse(formula)
            except AssertionError:
                print('error parsing the formula in the following line: \n', i, '\n')
            if 'Inference Rule ' in i:
                i = i.split('Inference Rule ')[1]
                if ' on lines ' in i:
                    inferencerule, assumptions = i.split(' on lines ')
                    inferencerule = parse_inference_rule(inferencerule)
                    assumptions = [int(j) for j in assumptions[:-1].split(',')]

                elif ' on line ' in i:
                    inferencerule, assumptions = i.split(' on line ')
                    inferencerule = parse_inference_rule(inferencerule)
                    assumptions = [int(j) for j in assumptions[:-1].split(',')]

                else:
                    inferencerule = parse_inference_rule(i)
                    assumptions = []
                lines.append(Proof.Line(formula, inferencerule, assumptions))

            else:
                lines.append(Proof.Line(formula))
    return Proof(statement, rules, lines)
    # Personal task

def inference_rule_to_code(rule: InferenceRule) -> str:
    """Converts an InferenceRule object into the constituent Python code, represented as a string"""

    return 'InferenceRule([' + ', '.join([f"Formula.parse('{str(i)}')" for i in rule.assumptions]) + f"], Formula.parse('{str(rule.conclusion)}'))"
    # Personal task

def proof_to_code(proof: Proof) -> str:
    """Converts a Proof object into the constituent Python code, represented as a string"""

    text = 'Proof(\n'
    statement = '\t' + inference_rule_to_code(proof.statement) + ',\n'
    rules = '\t[' + ',\n\t\t'.join([inference_rule_to_code(i) for i in proof.rules]) + '],\n'
    lines = '\t[Proof.Line(' + "),\n\t\tProof.Line(".join([f"Formula.parse('{i.formula}'), {inference_rule_to_code(i.rule)}, {list(i.assumptions)}"\
        if not i.is_assumption() else f"Formula.parse('{i.formula}')" for i in proof.lines]) + ")])"

    return text + statement + rules + lines
    # Personal task

def find_first_instance_of_formula(proof: Proof, formula: Formula) -> int:
    """Returns the line number of the first line containing the given formula"""

    for i in range(len(proof.lines)):
        if proof.lines[i].formula == formula:
            return i
    # Personal task

def remove_line(proof: Proof, line_number: int) -> Proof:
    """Removes the specified line and updates assumption citations to match new line numbers"""

    citations = find_citation_tree(proof, line_number)
    first_use = find_first_instance_of_formula(proof, proof.lines[line_number].formula)

    new_lines = []
    for i in range(len(proof.lines)):
        if i != line_number:
            line = proof.lines[i]
            if not line.is_assumption():
                new_assumptions = []
                for j in line.assumptions:
                    if j == line_number:
                        j = first_use
                    elif j > line_number:
                        j -= 1
                    new_assumptions.append(j)
                line = Proof.Line(line.formula, line.rule, new_assumptions)
            new_lines.append(line)
    new_proof = Proof(proof.statement, proof.rules, new_lines)
    assert new_proof.is_valid(), print(new_proof)
    return new_proof
    # Personal task

# def find_citation_tree(proof: Proof, line_number: int) -> list:
#     """Returns a list of numbers representing lines that cite the given line"""

#     line_list = []
#     for i in range(len(proof.lines)):
#         line = proof.lines[i]
#         if not line.is_assumption():
#             if line_number in line.assumptions:
#                 line_list.append(i)
#     return line_list
    # Personal task
    
def find_citation_tree(proof: Proof, line_number: int) -> set:
    """Traces citations back from the conclusion, finding all lines which are actually used to prove the conclusion.
    Returns them as a set."""

    set1 = set()

    if proof.lines[line_number].is_assumption():
        return set()
    else:
        new_citations = proof.lines[line_number].assumptions

    for i in new_citations:
        set1.add(i)
        if not proof.lines[i].is_assumption() and proof.lines[i].assumptions:
            set1 = set1 | find_citation_tree(proof, i)
    return set1
    # Personal task

def find_uncited_lines(proof: Proof) -> list:
    """Takes the difference between the set of line numbers in the proof and the set of line numbers in its citation tree.
    Returns them as a reversed list."""

    length = len(proof.lines)-1
    return sorted(set(range(length)) - find_citation_tree(proof, length))[::-1]
    # Personal task

def find_duplicate_lines(proof: Proof) -> list:
    """Returns a list of lists of line numbers with matching formulae"""

    list1 = []
    list2 = []
    for i in range(len(proof.lines)-1):
        if not i in list1:
            list2 = []
            formula = proof.lines[i].formula
            for j in range(len(proof.lines)-1):
                if i != j:
                    if formula == proof.lines[j].formula:
                        list2.append(j)
            if list2:
                [list1.append(i) for i in list2]
    return sorted(list1)[::-1]
    # Personal task

def clean_proof(proof: Proof) -> Proof:
    """Removes duplicate lines and unused lines, adjusting citations to match new line numbers"""

    if u:= find_duplicate_lines(proof):
        for i in u:
            proof = remove_line(proof, i)

    if d := find_uncited_lines(proof):
        for i in d:
            proof = remove_line(proof, i)

    assert proof.is_valid()
    return proof
    # Personal task

def convert_inference_rule_operators(inferencerule: InferenceRule, operator_function) -> InferenceRule:
    return InferenceRule([operator_function(i) for i in inferencerule.assumptions], operator_function(inferencerule.conclusion))
    # Personal task

def convert_proof_operators(proof: Proof, operator_function) -> Proof:
    statement = convert_inference_rule_operators(proof.statement, operator_function)
    rules = [convert_inference_rule_operators(i, operator_function) for i in proof.rules]

    lines = []
    for line in proof.lines:
        if line.is_assumption():
            lines.append(Proof.Line(operator_function(line.formula)))
        else:
            lines.append(Proof.Line(operator_function(line.formula), convert_inference_rule_operators(line.rule, operator_function), line.assumptions))
    return Proof(statement, rules, lines)
    # Personal task

# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/prover.py

"""Axiomatic schemas of Predicate Logic, and useful proof creation maneuvers
using them."""

from typing import AbstractSet, Collection, FrozenSet, List, Mapping, \
                   Sequence, Tuple, Union
from logic_utils import fresh_variable_name_generator, is_z_and_number
from syntax import *
from proofs import *

class Prover:
    """A class for gradually creating a predicate-logic proof from given
    assumptions as well as from the six axioms (`AXIOMS`) Universal
    Instantiation (`UI`), Existential Introduction (`EI`), Universal
    Simplification (`US`), Existential Simplification (`ES`), Reflexivity
    (`RX`), and Meaning of Equality (`ME`).

    Attributes:
        _assumptions (`~typing.FrozenSet`\\[`~predicates.proofs.Schema`]): the
            assumptions/axioms of the proof being created, which include
            `AXIOMS`.
        _lines (`~typing.List`\\[`~predicates.proofs.Proof.Line`]): the lines so
            far of the proof being created.
        _print_as_proof_forms (`bool`): flag specifying whether the proof being
            created is being printed in real time as it forms.
    """
    _assumptions: FrozenSet[Schema]
    _lines: List[Proof.Line]
    _print_as_proof_forms: bool

    #: Axiom schema of universal instantiation
    UI = Schema(Formula.parse('(Ax[R(x)]->R(c))'), {'R', 'x', 'c'})
    #: Axiom schema of existential introduction
    EI = Schema(Formula.parse('(R(c)->Ex[R(x)])'), {'R', 'x', 'c'})
    #: Axiom schema of universal simplification
    US = Schema(Formula.parse('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))'),
                {'Q', 'R', 'x'})
    #: Axiom schema of existential simplification
    ES = Schema(Formula.parse('((Ax[(R(x)->Q())]&Ex[R(x)])->Q())'),
                {'Q', 'R', 'x'})
    #: Axiom schema of reflexivity
    RX = Schema(Formula.parse('c=c'), {'c'})
    #: Axiom schema of meaning of equality
    ME = Schema(Formula.parse('(c=d->(R(c)->R(d)))'), {'R', 'c', 'd'})
    #: Axiomatic system for Predicate Logic, consisting of `UI`, `EI`, `US`,
    #: `ES`, `RX`, and `ME`.
    AXIOMS = frozenset({UI, EI, US, ES, RX, ME})

    def __init__(self, assumptions: Collection[Union[Schema, Formula, str]],
                 print_as_proof_forms: bool=False):
        """Initializes a `Prover` from its assumptions/additional axioms. The
        proof created by the prover initially has no lines.

        Parameters:
            assumptions: the assumptions/axioms beyond `AXIOMS` for the proof
                to be created, each specified as either a schema, a formula that
                constitutes the unique instance of the assumption, or the string
                representation of the unique instance of the assumption.
            print_as_proof_forms: flag specifying whether the proof to be
                created is to be printed in real time as it forms.
        """
        self._assumptions = \
            Prover.AXIOMS.union(
                {assumption if isinstance(assumption, Schema)
                 else Schema(assumption) if isinstance(assumption, Formula)
                 else Schema(Formula.parse(assumption))
                 for assumption in assumptions})
        self._lines = []
        self._print_as_proof_forms = print_as_proof_forms
        if self._print_as_proof_forms:
            print('Proving from assumptions/axioms:\n'
                  '  AXIOMS')
            for assumption in self._assumptions - Prover.AXIOMS:
                  print('  ' + str(assumption))
            print('Lines:')

    def qed(self) -> Proof:
        """Concludes the proof created by the current prover.

        Returns:
            A valid proof, from the assumptions of the current prover as well as
            `AXIOMS`', of the formula justified by the last line appended to the
            current prover.
        """
        conclusion = self._lines[-1].formula
        if self._print_as_proof_forms:
            print('Conclusion:', str(conclusion) + '. QED\n')
        return Proof(self._assumptions, conclusion, self._lines)

    def _add_line(self, line: Proof.Line) -> int:
        """Appends to the proof being created by the current prover the given
        validly justified line.

        Parameters:
            line: proof line that is validly justified when appended to the
                lines of the proof being created by the current prover.

        Returns:
            The line number of the appended line in the proof being created by
            the current prover.
        """
        line_number = len(self._lines)
        self._lines.append(line)
        assert line.is_valid(self._assumptions, self._lines, line_number)
        if self._print_as_proof_forms:
            print(('%3d) ' % line_number) + str(line.formula))
        return line_number

    def add_instantiated_assumption(self, instance: Union[Formula, str],
                                    assumption: Schema,
                                    instantiation_map: InstantiationMap) -> \
            int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given instance of the given assumptions/axioms of
        the current prover.

        Parameters:
            instance: instance to be appended, specified as either a formula or
                its string representation.
            assumption: assumption/axiom of the current prover that instantiates
                the given instance.
            instantiation_map: mapping instantiating the given instance from the
                given assumption/axiom. Each value of this map may also be given
                as a string representation (instead of a term or a formula).

        Returns:
            The line number of the newly appended line that justifies the given
            instance in the proof being created by the current prover.
        """
        if isinstance(instance, str):
            instance = Formula.parse(instance)
        instantiation_map = dict(instantiation_map)
        for key in instantiation_map:
            value = instantiation_map[key]
            if is_variable(key):
                assert is_variable(value)
            elif is_constant(key):
                if isinstance(value, str):
                    instantiation_map[key] = Term.parse(value)
                else:
                    assert isinstance(value, Term)
            else:
                assert is_relation(key)
                if isinstance(value, str):
                    instantiation_map[key] = Formula.parse(value)
                else:
                    assert isinstance(value, Formula)

#         print('\n',instance, assumption, instantiation_map,'\n')
        return self._add_line(Proof.AssumptionLine(instance, assumption,
                                                   instantiation_map))

    def add_assumption(self, unique_instance: Union[Formula, str]) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the unique instance of one of the assumptions/axioms
        of the current prover.

        Parameters:
            unique_instance: unique instance of one of the assumptions/axioms
                of the current prover, to be appended, specified as either a
                formula or its string representation.

        Returns:
            The line number of the newly appended line that justifies the given
            instance in the proof being created by the current prover.
        """
        if isinstance(unique_instance, str):
            unique_instance = Formula.parse(unique_instance)
        return self.add_instantiated_assumption(unique_instance,
                                                Schema(unique_instance), {})

    def add_tautology(self, tautology: Union[Formula, str]) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given tautology.

        Parameters:
            tautology: tautology to be appended, specified as either a formula
                or its string representation.

        Returns:
            The line number of the newly appended line that justifies the given
            tautology in the proof being created by the current prover.
        """
        if isinstance(tautology, str):
            tautology = Formula.parse(tautology)
        return self._add_line(Proof.TautologyLine(tautology))

    def add_mp(self, consequent: Union[Formula, str],
               antecedent_line_number: int, conditional_line_number: int) -> \
            int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given consequent of an MP inference from the
        specified already existing lines of the proof.

        Parameters:
            consequent: consequent of MP inference to be appended, specified as
                either a formula or its string representation.
            antecedent_line_number: line number in the proof of the antecedent
                of the MP inference that derives the given formula.
            conditional_line_number: line number in the proof of the conditional
                of the MP inference that derives the given formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(consequent, str):
            consequent = Formula.parse(consequent)
        return self._add_line(Proof.MPLine(consequent, antecedent_line_number,
                                           conditional_line_number))

    def add_ug(self, quantified: Union[Formula, str],
               nonquantified_line_number: int) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given universally quantified formula, the
        statement quantified by which is the specified already existing line of
        the proof.

        Parameters:
            quantified: universally quantified formula to be appended, specified
                as either a formula or its string representation.
            nonquantified_line_number: line number in the proof of the statement
                quantified by the given formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(quantified, str):
            quantified = Formula.parse(quantified)
        return self._add_line(Proof.UGLine(quantified,
                                           nonquantified_line_number))

    def add_and_introduction(self, firstline, secondline):
        first = self._lines[firstline].formula
        second = self._lines[secondline].formula
        tautology = Formula('->',first,
                        Formula('->',second,
                            Formula('&', first, second)))
        step1 = self.add_tautology(tautology)
        step2 = self.add_mp(tautology.second, firstline, step1)
        return self.add_mp(tautology.second.second, secondline, step2)
        # personal task

    def add_and_elimination(self, conjunction_line, desired_operand):
        conjunction = self._lines[conjunction_line].formula
        assert conjunction.root == '&'
        assert conjunction.first == desired_operand or conjunction.second == desired_operand
        tautology = Formula('->', conjunction, desired_operand)
        step1 = self.add_tautology(tautology)
        return self.add_mp(desired_operand, conjunction_line, step1)
        # personal task

    def add_or_introduction(self, conjunct1, conjunct1line, conjunct2, conjunct2line):
        pass

    def add_or_elimination(self, ):
        pass

    def add_proof(self, conclusion: Union[Formula, str], proof: Proof) -> int:
        """Appends to the proof being created by the current prover a validly
        justified inlined version of the given proof of the given conclusion,
        the last line of which validly justifies the given formula.

        Parameters:
            conclusion: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            proof: valid proof of the given formula from a subset of the
                assumptions/axioms of the current prover.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(conclusion, str):
            conclusion = Formula.parse(conclusion)
        assert proof.conclusion == conclusion
        assert proof.assumptions.issubset(self._assumptions)
        line_shift = len(self._lines)
        for line in proof.lines:
            if type(line) in {Proof.AssumptionLine, Proof.TautologyLine}:
                self._add_line(line)
            elif isinstance(line, Proof.MPLine):
                self.add_mp(line.formula,
                            line.antecedent_line_number + line_shift,
                            line.conditional_line_number + line_shift)
            else:
                assert isinstance(line, Proof.UGLine)
                self.add_ug(line.formula,
                            line.nonquantified_line_number + line_shift)
        line_number = len(self._lines) - 1
        assert self._lines[line_number].formula == conclusion
        return line_number

    def add_universal_instantiation(self, instantiation: Union[Formula, str],
                                    line_number: int, term: Union[Term, str]) \
            -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the result of substituting a term for the
        outermost universally quantified variable name in the formula in the
        specified already existing line of the proof.

        Parameters:
            instantiation: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of a universally quantified
                formula of the form `Ax[statement]`.
            term: term, specified as either a term or its string representation,
                that when substituted into the free occurrences of `x` in
                `statement` yields the given formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.

        Examples:
            If Line `line_number` contains the formula
            ``'Ay[Az[f(x,y)=g(z,y)]]'`` and `term` is ``'h(w)'``, then
            `instantiation` should be ``'Az[f(x,h(w))=g(z,h(w))]'``.
        """
        if isinstance(instantiation, str):
            instantiation = Formula.parse(instantiation)
        assert line_number < len(self._lines)
        quantified = self._lines[line_number].formula
        assert quantified.root == 'A'
        if isinstance(term, str):
            term = Term.parse(term)
        assert instantiation == \
               quantified.statement.substitute({quantified.variable: term})

        instantiation_map = {'R': quantified.statement.substitute({quantified.variable: Term('_')}),
                             'c': term,
                             'x': quantified.variable}

        step1 = self.add_instantiated_assumption(Formula('->', quantified, instantiation), Prover.UI, instantiation_map)
        return self.add_mp(instantiation, line_number, step1)
        # Harris J. Bolus - Task 10.1

    def add_tautological_implication(self, implication: Union[Formula, str],
                                     line_numbers: AbstractSet[int]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is a tautological implication of the formulas in
        the specified already existing lines of the proof.

        Parameters:
            implication: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_numbers: line numbers in the proof of formulas of which
                `implication` is a tautological implication.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(implication, str):
            implication = Formula.parse(implication)
        for line_number in line_numbers:
            assert line_number < len(self._lines)

        line_numbers = sorted(line_numbers)
        tautology = implication
        for line in line_numbers[::-1]:
            tautology = Formula('->', self._lines[line].formula, tautology)
        step = self.add_tautology(tautology)
        if len(line_numbers) > 1:
            for line in line_numbers[:-1]:
                tautology = tautology.second
                step = self.add_mp(tautology, line, step)
        return self.add_mp(implication, line_numbers[-1], step)
        # Harris J. Bolus - Task 10.2

    def add_existential_derivation(self, consequent: Union[Formula, str],
                                   line_number1: int, line_number2: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the consequent of the formula in the second
        specified already existing line of the proof, whose antecedent is
        existentially quantified by the formula in the first specified already
        existing line of the proof.

        Parameters:
            consequent: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number1: line number in the proof of an existentially
                quantified formula of the form
                `Ex[antecedent(x)]`, where `x`
                is a variable name that may have free occurrences in
                `antecedent(x)` but has no free occurrences in `consequent`.
            line_number2: line number in the proof of the formula
                `(antecedent(x)->consequent)`.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(consequent, str):
            consequent = Formula.parse(consequent)
        assert line_number1 < len(self._lines)
        quantified = self._lines[line_number1].formula
        assert quantified.root == 'E'
        assert quantified.variable not in consequent.free_variables()
        assert line_number2 < len(self._lines)
        conditional = self._lines[line_number2].formula
        assert conditional == Formula('->', quantified.statement, consequent)

        variable = quantified.variable
        step1 = self.add_ug(Formula('A', variable, self._lines[line_number2].formula), line_number2)
        instantiation_map = {'Q': consequent,
                        'R': quantified.statement.substitute({variable:Term('_')}),
                        'x': variable}
        step2 = self.add_instantiated_assumption(Prover.ES.instantiate(instantiation_map), Prover.ES, instantiation_map)
        return self.add_tautological_implication(consequent, {line_number1, step1, step2})
        # Harris J. Bolus - Task 10.3

    def add_flipped_equality(self, flipped: Union[Formula, str],
                             line_number: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, which is the result of exchanging the two sides of the
        equality in the specified already existing line of the proof.

        Parameters:
            flipped: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of an equality that is the
                same as the given equality, except that the two sides of the
                equality are exchanged.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.
        """
        if isinstance(flipped, str):
            flipped = Formula.parse(flipped)
        assert is_equality(flipped.root)
        assert line_number < len(self._lines)
        equality = self._lines[line_number].formula
        assert equality == Formula('=', [flipped.arguments[1],
                                         flipped.arguments[0]])
        x, y = equality.arguments
        instantiation_map = {'R': Formula('=', [Term('_'), x]), 'c': x, 'd': y}
        step1 = self.add_instantiated_assumption(Prover.ME.instantiate(instantiation_map), Prover.ME, instantiation_map)
        step2 = self.add_mp(self._lines[step1].formula.second, line_number, step1)
        step3 = self.add_instantiated_assumption(Prover.RX.instantiate({'c':x}), Prover.RX, {'c':x})
        return self.add_mp(self._lines[step2].formula.second, step3, step2)

        # Harris J. Bolus - Task 10.6

    def add_free_instantiation(self, instantiation: Union[Formula, str],
                               line_number: int,
                               substitution_map:
                               Mapping[str, Union[Term, str]]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the result of substituting terms for free
        variable names in the formula in the specified already existing line of
        the proof.

        Parameters:
            instantiation: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of a formula with free
                variable names, which contains no variable names that are ``z``
                followed by a number.
            substitution_map: mapping from free variable names of the formula
                with the given line number to terms that contain no variable
                names that are ``z`` followed by a number, to be substituted for
                them to obtain the given formula. Each value of this map may
                also be given as a string representation (instead of a term).
                Only variable name occurrences originating in the formula with
                the given line number are substituted (i.e., variable names
                originating in one of the specified substitutions are not
                subjected to additional substitutions).

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.

        Examples:
            If Line `line_number` contains the formula
            ``'(z=5&Az[f(x,y)=g(z,y)])'`` and `substitution_map` is
            ``{'y': 'h(w)', 'z': 'y'}``, then `instantiation` should be
            ``'(y=5&Az[f(x,h(w))=g(z,h(w))])'``.
        """
        if isinstance(instantiation, str):
            instantiation = Formula.parse(instantiation)
        substitution_map = dict(substitution_map)
        for variable in substitution_map:
            assert is_variable(variable)
            term = substitution_map[variable]
            if isinstance(term, str):
                substitution_map[variable] = term = Term.parse(term)
            for variable in term.variables():
                assert not is_z_and_number(variable)
        assert line_number < len(self._lines)
        original = self._lines[line_number].formula
        for variable in original.variables():
            assert not is_z_and_number(variable)
        assert original.free_variables().issuperset(substitution_map.keys())
        assert instantiation == original.substitute(substitution_map)
        
        nested = False
        for variable1 in substitution_map:
            variables = substitution_map[variable1].variables() | substitution_map[variable1].constants()
            for variable2 in substitution_map:
                if not variable1 == variable2:
                    if variable2 in variables:
                        nested = True
                        break
        
        if nested:
            temp_variables = {}
            new_variables = {}
            
            #Complex case - Produce intermediary dictionaries and perform universal generalization over all keys in substitution map
            for original_variable in substitution_map:
                temp_variable = next(fresh_variable_name_generator)
                temp_variables[original_variable] = temp_variable
                new_variables[temp_variable] = substitution_map[original_variable]
                line_number = self.add_ug(Formula('A', original_variable, self._lines[line_number].formula), line_number)
            
            #Universal instantiation to replace all original variables with temporary variables
            for _ in substitution_map:
                quantified_variable = self._lines[line_number].formula.variable
                new_formula = self._lines[line_number].formula.statement.substitute({quantified_variable: Term(temp_variables[quantified_variable])})
                line_number = self.add_universal_instantiation(new_formula, line_number, temp_variables[quantified_variable])
            
            #Universal generalization over all temporary variables
            for temp_variable in new_variables:
                line_number = self.add_ug(Formula('A', temp_variable, self._lines[line_number].formula), line_number)
            
            #Universal instantiation to replace all temporary variables with desired variables
            for _ in new_variables:
                quantified_variable = self._lines[line_number].formula.variable
                new_formula = self._lines[line_number].formula.statement.substitute({quantified_variable: new_variables[quantified_variable]})
                line_number = self.add_universal_instantiation(new_formula, line_number, new_variables[quantified_variable])
        
        else:
            #Simple case - Universal instantiation over all original variables
            for variable in substitution_map:
                line_number = self.add_ug(Formula('A', variable, self._lines[line_number].formula), line_number)
            
            #Universal instantiation to replace them with desired variables
            for _ in substitution_map:
                quantified_variable = self._lines[line_number].formula.variable
                new_formula = self._lines[line_number].formula.statement.substitute({quantified_variable: substitution_map[quantified_variable]})
                line_number = self.add_universal_instantiation(new_formula, line_number, substitution_map[quantified_variable])
        return line_number
        # Harris J. Bolus - Task 10.7

    def add_substituted_equality(self, substituted: Union[Formula, str],
                                 line_number: int,
                                 parametrized_term: Union[Term, str]) -> \
            int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, whose two sides are the results of substituting the two
        respective sides of the equality in the specified already existing line
        of the proof into the given parametrized term.

        Parameters:
            substituted: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of an equality.
            parametrized_term: term parametrized by the constant name ``'_'``,
                specified as either a term or its string representation, such
                that substituting each of the two sides of the equality with the
                given line number into this parametrized term respectively
                yields each of the two sides of the given equality.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.

        Examples:
            If Line `line_number` contains the formula ``'g(x)=h(y)'`` and
            `parametrized_term` is ``'_+7'``, then `substituted` should be
            ``'g(x)+7=h(y)+7'``.
        """
        if isinstance(substituted, str):
            substituted = Formula.parse(substituted)
        assert is_equality(substituted.root)
        assert line_number < len(self._lines)
        equality = self._lines[line_number].formula
        assert is_equality(equality.root)
        if isinstance(parametrized_term, str):
            parametrized_term = Term.parse(parametrized_term)
        assert substituted == \
               Formula('=', [parametrized_term.substitute(
                                 {'_': equality.arguments[0]}),
                             parametrized_term.substitute(
                                 {'_': equality.arguments[1]})])
        x, y = equality.arguments
        nonparametrized_term = parametrized_term.substitute({'_': x})
        phi = Formula('=', [nonparametrized_term, parametrized_term])
        instantiation_map = {'R': phi, 'c': x, 'd': y}
        me = Prover.ME.instantiate(instantiation_map)
        step1 = self.add_instantiated_assumption(me, Prover.ME, instantiation_map)
        step2 = self.add_mp(me.second, line_number, step1)
        step3 = self.add_instantiated_assumption(Prover.RX.instantiate({'c':nonparametrized_term}), Prover.RX, {'c':nonparametrized_term})
        return self.add_mp(me.second.second, step3, step2)
        # Harris J. Bolus - Task 10.8

    def _add_chaining_of_two_equalities(self, line_number1: int,
                                        line_number2: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies an
        equality that is the result of chaining together the two equalities in
        the specified already existing lines of the proof.

        Parameters:
            line_number1: line number in the proof of an equality of the form
                ``'``\ `first`\ ``=``\ `second`\ ``'``.
            line_number2: line number in the proof of an equality of the form
                ``'``\ `second`\ ``=``\ `third`\ ``'``.

        Returns:
            The line number of the newly appended line that justifies the
            equality ``'``\ `first`\ ``=``\ `third`\ ``'`` in the proof being
            created by the current prover.

        Examples:
            If Line `line_number1` contains the formula ``'a=b'`` and Line
            `line_number2` contains the formula ``'b=f(b)'``, then the last
            appended line will contain the formula ``'a=f(b)'``.
        """
        assert line_number1 < len(self._lines)
        equality1 = self._lines[line_number1].formula
        assert is_equality(equality1.root)
        assert line_number2 < len(self._lines)
        equality2 = self._lines[line_number2].formula
        assert is_equality(equality2.root)
        assert equality1.arguments[1] == equality2.arguments[0]

        x, y = equality1.arguments
        z = equality2.arguments[1]
        inst_map = {'R': Formula('=',[x,Term('_')]), 'c': y, 'd': z}
        me = Prover.ME.instantiate(inst_map)
        step1 = self.add_instantiated_assumption(me, Prover.ME, inst_map)
        step2 = self.add_mp(me.second, line_number2, step1)
        return self.add_mp(me.second.second, line_number1, step2)
        # Harris J. Bolus - Task 10.9a

    def add_chained_equality(self, chained: Union[Formula, str],
                             line_numbers: Sequence[int]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, which is the result of chaining together the equalities
        in the specified already existing lines of the proof.

        Parameters:
            chained: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation,
                of the form ``'``\ `first`\ ``=``\ `last`\ ``'``.
            line_numbers: line numbers in the proof of equalities of the form
                ``'``\ `first`\ ``=``\ `second`\ ``'``,
                ``'``\ `second`\ ``=``\ `third`\ ``'``, ...,
                ``'``\ `before_last`\ ``=``\ `last`\ ``'``, i.e., the left-hand
                side of the first equality is the left-hand side of the given
                equality, the right-hand of each equality (except for the last)
                is the left-hand side of the next equality, and the right-hand
                side of the last equality is the right-hand side of the given
                equality.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.

            Examples:
            If `line_numbers` is ``[7,3,9]``, Line 7 contains the formula
            ``'a=b'``, Line 3 contains the formula ``'b=f(b)'``, and Line 9
            contains the formula ``'f(b)=0'``, then `chained` should be
            ``'a=0'``.
        """
        if isinstance(chained, str):
            chained = Formula.parse(chained)
        assert is_equality(chained.root)
        assert len(line_numbers) >= 2
        current_term = chained.arguments[0]
        for line_number in line_numbers:
            assert line_number < len(self._lines)
            equality = self._lines[line_number].formula
            assert is_equality(equality.root)
            assert equality.arguments[0] == current_term
            current_term = equality.arguments[1]
        assert chained.arguments[1] == current_term

        step0 = line_numbers[0]
        equality1 = self._lines[step0].formula

        for line in line_numbers[1:]:
            equality2 = self._lines[line].formula
            x, y = equality1.arguments
            z = equality2.arguments[1]
            inst_map = {'R': Formula('=', [x, Term('_')]), 'c': y, 'd': z}
            me = Prover.ME.instantiate(inst_map)
            step1 = self.add_instantiated_assumption(me, Prover.ME, inst_map)
            step2 = self.add_mp(me.second, line, step1)
            step0 = self.add_mp(me.second.second, step0, step2)
            equality1 = me.second.second
        return step0
        # Harris J. Bolus - Task 10.9b

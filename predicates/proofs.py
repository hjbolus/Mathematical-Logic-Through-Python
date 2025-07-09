# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/proofs.py

"""Schemas and proofs in Predicate Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, Mapping, Sequence, Tuple, Union
from logic_utils import frozen, frozendict
import sys
sys.path.append('/Users/harrisbolus/Desktop/Fun/Mathematical logic thru python')
from propositions.semantics import is_tautology as is_propositional_tautology
from predicates.syntax import *

#: A mapping from constant names, variable names, and relation names to
#: terms, variable names, and formulas respectively.
InstantiationMap = Mapping[str, Union[Term, str, Formula]]

@frozen
class Schema:
    """An immutable schema of predicate-logic formulas, comprised of a formula
    along with the constant names, variable names, and nullary or unary relation
    names in that formula that serve as templates. A template constant name is a
    placeholder for any term. A template variable name is a placeholder for any
    variable name. A template nullary or unary relation name is a placeholder
    for any (parametrized for a unary template relation name) predicate-logic
    formula that does not refer to any variable name in the schema (except
    possibly through its instantiated argument for a unary relation name).

    Attributes:
        formula (`~predicates.syntax.Formula`): the formula of the schema.
        templates (`~typing.FrozenSet`\\[`str`]): the constant, variable, and
            relation names from the formula that serve as templates.
    """
    formula: Formula
    templates: FrozenSet[str]

    def __init__(self, formula: Formula,
                 templates: AbstractSet[str] = frozenset()):
        """Initializes a `Schema` from its formula and template names.

        Parameters:
            formula : the formula for the schema.
            templates: the constant, variable, and relation names from the
                formula to serve as templates.
        """
        for template in templates:
            assert is_constant(template) or is_variable(template) or \
                   is_relation(template)
            if is_relation(template):
                arities = {arity for relation,arity in formula.relations() if
                           relation == template}
                assert arities == {0} or arities == {1}
        self.formula = formula
        self.templates = frozenset(templates)

    def __repr__(self) -> str:
        """Computes a string representation of the current schema.

        Returns:
            A string representation of the current schema.
        """
        return 'Schema: ' + str(self.formula) + ' [templates: ' + \
               ('none' if len(self.templates) == 0 else
                ", ".join(sorted(self.templates))) + ']'

    def __eq__(self, other: object) -> bool:
        """Compares the current schema with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Schema` object that equals the
            current schema, ``False`` otherwise.
        """
        return isinstance(other, Schema) and self.formula == other.formula and \
               self.templates == other.templates

    def __ne__(self, other: object) -> bool:
        """Compares the current schema with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Schema` object or does not
            equal the current schema, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    class BoundVariableError(Exception):
        """Raised by `_instantiate_helper` when a variable name becomes bound
        during a schema instantiation in a way that is disallowed in that
        context.

        Attributes:
            variable_name (`str`): the variable name that became bound in a way
                that was disallowed during a schema instantiation.
            relation_name (`str`): the relation name during whose substitution
                the relevant occurrence of the variable name became bound.
        """
        variable_name: str
        relation_name: str

        def __init__(self, variable_name: str, relation_name: str):
            """Initializes a `~Schema.BoundVariableError` from the offending
            variable name and the relation name during whose substitution the
            error occurred.

            Parameters:
                variable_name: variable name that is to become bound in a way
                    that is disallowed during a schema instantiation.
                relation_name: the relation name during whose substitution the
                    relevant occurrence of the variable name is to become bound.
            """
            assert is_variable(variable_name)
            assert is_relation(relation_name)
            self.variable_name = variable_name
            self.relation_name = relation_name

    @staticmethod
    def _instantiate_helper(formula: Formula,
                            constants_and_variables_instantiation_map:
                            Mapping[str, Term],
                            relations_instantiation_map: Mapping[str, Formula],
                            bound_variables: AbstractSet[str] = frozenset()) \
            -> Formula:
        """Performs the following substitutions in the given formula:

        1. Substitute each occurrence of each constant name or variable name
           that is a key of the given constants and variables instantiation map
           with the term mapped to this name by this map.
        2. Substitute each nullary invocation of each relation name that is a    #Can I just sub in my constants and variables into my relations, then pass just my subbed relations to lower levels?
           key of the given relations instantiation map with the formula mapped
           to it by this map.
        3. For each unary invocation of each relation name that is a key of the
           given relations instantiation map, first perform all substitutions
           to the argument of this invocation (according to the given constants
           and variables instantiation map), then substitute the result for
           each occurrence of the constant name ``'_'`` in the formula mapped to
           the relation name by this map, and then substitute the result for
           this unary invocation of the relation name.

        Only name occurrences originating in the given formula are substituted
        (i.e., name occurrences originating in one of the above substitutions
        are not subjected to additional substitutions).

        Parameters:
            formula: formula in which to perform the substitutions.
            constants_and_variables_instantiation_map: mapping from constant
                names and variable names in the given formula to terms to be
                substituted for them, where the roots of terms mapped to
                variable names are variable names.
            relations_instantiation_map: mapping from nullary and unary relation
                names in the given formula to formulas to be substituted for
                them, where formulas to be substituted for unary relation names
                are parametrized by the constant name ``'_'``.
            bound_variables: variable names to be treated as bound (see below).

        Returns:
            The result of all substitutions.

        Raises:
            BoundVariableError: if one of the following occurs when substituting
                an invocation of a relation name:

                1. A free occurrence of a variable name in the formula
                   mapped to the relation name by the given relations
                   instantiation map is in `bound_variables`.
                2. A free occurrence of a variable name in the formula
                   mapped to the relation name by the given relations
                   instantiation map becomes bound by a quantification in
                   the given formula after all variable
                   names in the given formula have been substituted.
                3. For a unary invocation: a variable name that is in the
                   argument to that invocation after all substitutions have been
                   applied to this argument becomes bound by a quantification
                   in the formula mapped to the relation name by the given
                   relations instantiation map.

        Examples:
            The following succeeds:

            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'), {'x': Term('w')},
            ...     {'Q': Formula.parse('y=_')}, {'x', 'z'})
            Aw[(y=c->R(w))]

            however the following fails since ``'Q(c)'`` is to be substituted
            with ``'y=c'`` while ``'y'`` is specified to be treated as bound:

            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'), {},
            ...     {'Q': Formula.parse('y=_')}, {'x', 'y', 'z'})
            Traceback (most recent call last):
              ...
            predicates.proofs.Schema.BoundVariableError: ('y', 'Q')

            and the following fails since as ``'Q(c)'`` is to be substituted
            with ``'y=c'``, ``'y'`` is to become bound by the quantification
            ``'Ay'``:

            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'), {'x': Term('y')},
            ...     {'Q': Formula.parse('y=_')})
            Traceback (most recent call last):
              ...
            predicates.proofs.Schema.BoundVariableError: ('y', 'Q')

            The following succeeds:

            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'),
            ...     {'c': Term.parse('plus(d,x)')},
            ...     {'Q': Formula.parse('Ey[y=_]')})
            Ax[(Ey[y=plus(d,x)]->R(x))]

            however the following fails since as ``'_'`` is to be substituted
            with ``'plus(d,y)'`` in ``'Ey[y=_]'``, the ``'y'`` in
            ``'plus(d,y)'`` is to become bound by the quantification ``'Ey'``:

            >>> Schema._instantiate_helper(
            ...     Formula.parse('Ax[(Q(c)->R(x))]'),
            ...     {'c': Term.parse('plus(d,y)')},
            ...     {'Q': Formula.parse('Ey[y=_]')})
            Traceback (most recent call last):
              ...
            predicates.proofs.Schema.BoundVariableError: ('y', 'Q')
        """
        for construct in constants_and_variables_instantiation_map:
            assert is_constant(construct) or is_variable(construct)
            if is_variable(construct):
                assert is_variable(
                    constants_and_variables_instantiation_map[construct].root)
        for relation in relations_instantiation_map:
            assert is_relation(relation)
        for variable in bound_variables:
            assert is_variable(variable)
        root = formula.root

        if is_unary(root):
            try:
                first = Schema._instantiate_helper(formula.first,
                                constants_and_variables_instantiation_map,
                                relations_instantiation_map,
                                bound_variables)
            except ForbiddenVariableError as e:
                raise Schema.BoundVariableError(e.variable_name, formula.first.root)
            formula = Formula(root, first)

        elif is_binary(root):
            try:
                first = Schema._instantiate_helper(formula.first,
                                                   constants_and_variables_instantiation_map,
                                                   relations_instantiation_map,
                                                   bound_variables)
                second = Schema._instantiate_helper(formula.second,
                                                    constants_and_variables_instantiation_map,
                                                    relations_instantiation_map,
                                                    bound_variables)
            except ForbiddenVariableError as e:
                raise Schema.BoundVariableError(e.variable_name, formula.first.root)
            formula = Formula(root, first, second)

        elif is_relation(root):
            relation_name, arity = formula.relations().pop()
            if arity == 1: #parametrized
                formula = formula.substitute(constants_and_variables_instantiation_map)
                parameter = formula.arguments[0]
                if relation_name in relations_instantiation_map:
                    replacement_template = relations_instantiation_map[relation_name]

                    if sinners := replacement_template.free_variables() & bound_variables:
                        raise Schema.BoundVariableError(sinners.pop(), relation_name)
                    elif parameter in replacement_template.bound_variables():
                        raise Schema.BoundVariableError(parameter, relation_name)
                    try:
                        formula = replacement_template.substitute({'_':parameter})
                    except ForbiddenVariableError as e:
                        raise Schema.BoundVariableError(e.variable_name, relation_name)

            else: #parameterless
                if relation_name in relations_instantiation_map:
                    replacement_template = relations_instantiation_map[relation_name]
                    if sinners := replacement_template.free_variables() & bound_variables:
                        raise Schema.BoundVariableError(sinners.pop(), relation_name)
                    formula = replacement_template

        elif is_equality(root):
            formula = formula.substitute(constants_and_variables_instantiation_map)

        elif is_quantifier(root):
            variable = formula.variable
            if variable in constants_and_variables_instantiation_map:
                bound_variables = bound_variables - {variable}
                variable = str(constants_and_variables_instantiation_map[variable])
            bound_variables = bound_variables | {variable}
            formula = Schema._instantiate_helper(formula.statement,
                                                 constants_and_variables_instantiation_map,
                                                 relations_instantiation_map,
                                                 bound_variables)
            formula = Formula(root, variable, formula)
        return formula
        # Harris J. Bolus - Task 9.3

    def instantiate(self, instantiation_map: InstantiationMap) -> \
            Union[Formula, None]:
        """Instantiates the current schema according to the given map from
        templates of the current schema to expressions.

        Parameters:
            instantiation_map: mapping from templates of the current schema to
                expressions of the type for which they serve as placeholders.
                That is, constant names are mapped to terms, variable names are
                mapped to variable names (strings), and relation names are
                mapped to formulas where unary relation names are mapped to
                formulas parametrized by the constant name ``'_'``.

        Returns:
            The predicate-logic formula obtained by applying the substitutions
            specified by the given map to the formula of the current schema:

            1. Each occurrence in the formula of the current schema of each
               template constant name specified in the given map is substituted
               with the term to which that template constant name is mapped.
            2. Each occurrence in the formula of the current schema of each
               template variable name specified in the given map is substituted
               with the variable name to which that template variable name is
               mapped.
            3. Each nullary invocation in the formula of the current schema of
               each template relation name specified in the given map is
               substituted with the formula to which that template relation name
               is mapped.
            4. Each unary invocation in the formula of the current schema of
               each template relation name specified in the given map is
               substituted with the formula to which that template relation name
               is mapped, in which each occurrence of the constant name ``'_'``
               is substituted with  the instantiated argument of that invocation
               of the template relation name (that is, the term that results
               from instantiating the argument of that invocation by performing
               all the specified substitutions on it).

            ``None`` is returned if one of the keys of the given map is not a
            template of the current schema or if one of the following occurs
            when substituting an invocation of a template relation name:

            1. A free occurrence of a variable name in the formula substituted
               for the template relation name becomes bound by a quantification
               in the instantiated schema formula, except if the template
               relation name is unary and this free occurrence originates in the
               instantiated argument of the invocation of the template relation
               name.
            2. For a unary invocation: a variable name in the instantiated
               argument of that invocation becomes bound by a quantification in
               the formula that is substituted for the invocation of the
               template relation name.

        Examples:
            >>> s = Schema(Formula.parse('(Q(c1,c2)->(R(c1)->R(c2)))'),
            ...            {'c1', 'c2', 'R'})
            >>> s.instantiate({'c1': Term.parse('plus(x,1)'),
            ...                'R': Formula.parse('Q(_,y)')})
            (Q(plus(x,1),c2)->(Q(plus(x,1),y)->Q(c2,y)))
            >>> s.instantiate({'c1': Term.parse('plus(x,1)'),
            ...                'c2': Term.parse('c1'),
            ...                'R': Formula.parse('Q(_,y)')})
            (Q(plus(x,1),c1)->(Q(plus(x,1),y)->Q(c1,y)))

            >>> s = Schema(Formula.parse('(P()->P())'), {'P'})
            >>> s.instantiate({'P': Formula.parse('plus(a,b)=c')})
            (plus(a,b)=c->plus(a,b)=c)

            For the following schema:

            >>> s = Schema(Formula.parse('(Q(d)->Ax[(R(x)->Q(f(c)))])'),
            ...            {'R', 'Q', 'x', 'c'})

            the following succeeds:

            >>> s.instantiate({'R': Formula.parse('_=0'),
            ...                'Q': Formula.parse('x=_'),
            ...                'x': 'w'})
            (x=d->Aw[(w=0->x=f(c))])

            however, the following returns ``None`` because ``'d'`` is not a
            template of the schema:

            >>> s.instantiate({'R': Formula.parse('_=0'),
            ...                'Q': Formula.parse('x=_'),
            ...                'x': 'w',
            ...                'd': Term('z')})

            and the following returns ``None`` because ``'z'`` that is free in
            the assignment to ``'Q'`` is to become bound by a quantification in
            the instantiated schema formula:

            >>> s.instantiate({'R': Formula.parse('_=0'),
            ...                'Q': Formula.parse('s(z)=_'),
            ...                'x': 'z'})

            and the following returns ``None`` because ``'y'`` in the
            instantiated argument ``'f(plus(a,y))'`` of the second invocation of
            ``'Q'`` is to become bound by the quantification in the formula
            substituted for ``'Q'``:

            >>> s.instantiate({'R': Formula.parse('_=0'),
            ...                'Q': Formula.parse('Ay[s(y)=_]'),
            ...                'c': Term.parse('plus(a,y)')})
        """
        for construct in instantiation_map:
            if is_variable(construct):
                assert is_variable(instantiation_map[construct])
            elif is_constant(construct):
                assert isinstance(instantiation_map[construct], Term)
            else:
                assert is_relation(construct)
                assert isinstance(instantiation_map[construct], Formula)

        constants_and_variables_instantiation_map = {}
        relations_instantiation_map = {}
        for key in instantiation_map:
            if not key in self.templates:
                return None
            elif is_variable(key):
                assert isinstance(instantiation_map[key], str)
                constants_and_variables_instantiation_map[key] = Term(instantiation_map[key])
            elif is_constant(key):
                assert isinstance(instantiation_map[key], Term)
                constants_and_variables_instantiation_map[key] = instantiation_map[key]
            elif is_relation(key):
                assert isinstance(instantiation_map[key], Formula)
                relations_instantiation_map[key] = instantiation_map[key]

        if not (constants_and_variables_instantiation_map or relations_instantiation_map):
            return self.formula

        bound_variables = set()
        try:
            return Schema._instantiate_helper(self.formula, 
                                              constants_and_variables_instantiation_map, 
                                              relations_instantiation_map, 
                                              bound_variables)
        except Schema.BoundVariableError as e:
            print(f'BoundVariableError: {e.variable_name} is bound within the relation {e.relation_name}')
            return None
        # Harris J. Bolus - Task 9.4

    @staticmethod
    def parse(string: str) -> Schema:
        """Parses the given valid string representation into a Schema.

        Parameters:
            string: string to parse.

        Returns:
            A schema whose standard string representation is the given string.
        """
        formula, templates = string.split('Schema: ')[1].split(' ', maxsplit = 1)
        formula = Formula.parse(formula)
        templates = set(templates.split(': ')[1][:-1].split(', '))
        if templates == {'none'}:
            templates = {}
        return Schema(formula, templates)
        # personal task
@frozen
class Proof:
    """An immutable deductive proof in Predicate Logic, comprised of a list of
    assumptions/axioms, a conclusion, and a list of lines that prove the
    conclusion from (instances of) these assumptions/axioms and from
    tautologies, via the Modus Ponens (MP) and Universal Generalization (UG)
    inference rules.

    Attributes:
        assumptions (`~typing.FrozenSet`\\[`Schema`]): the assumption/axioms of
            the proof.
        conclusion (`~predicates.syntax.Formula`): the conclusion of the proof.
        lines (`~typing.Tuple`\\[`Line`\]): the lines of the proof.
    """
    assumptions: FrozenSet[Schema]
    conclusion: Formula
    lines: Tuple[Proof.Line, ...]

    def __init__(self, assumptions: AbstractSet[Schema], conclusion: Formula,
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its assumptions/axioms, conclusion,
        and lines.

        Parameters:
            assumptions: the assumption/axioms for the proof.
            conclusion: the conclusion for the proof.
            lines: the lines for the proof.
        """
        self.assumptions = frozenset(assumptions)
        self.conclusion = conclusion
        self.lines = tuple(lines)

    @frozen
    class AssumptionLine:
        """An immutable proof line justified as an instance of an
        assumption/axiom.

        Attributes:
            formula (`~predicates.syntax.Formula`): the formula justified by the
                line.
            assumption (`Schema`): the assumption/axiom that instantiates the
                formula.
            instantiation_map (`~typing.Mapping`\\[`str`, `~typing.Union`\\[`~predicates.syntax.Term`, `str`, `~predicates.syntax.Formula`]]):
                the mapping instantiating the formula from the assumption/axiom.
        """
        formula: Formula
        assumption: Schema
        instantiation_map: InstantiationMap

        def __init__(self, formula: Formula, assumption: Schema,
                     instantiation_map: InstantiationMap):
            """Initializes an `~Proof.AssumptionLine` from its formula, its
            justifying assumption/axiom, and its instantiation map from the
            justifying assumption/axiom.

            Parameters:
                formula: the formula to be justified by the line.
                assumption: the assumption/axiom that instantiates the formula.
                instantiation_map: the mapping instantiating the formula from
                    the assumption/axiom.
            """
            for construct in instantiation_map:
                if is_variable(construct):
                    assert is_variable(instantiation_map[construct])
                elif is_constant(construct):
                    assert isinstance(instantiation_map[construct], Term)
                else:
                    assert is_relation(construct)
                    assert isinstance(instantiation_map[construct], Formula)
            self.formula = formula
            self.assumption = assumption
            self.instantiation_map = frozendict(instantiation_map)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            return str(self.formula) + "    (Assumption " + \
                   str(self.assumption) + " instantiated with " + \
                   str(self.instantiation_map) + ")"

        def is_valid(self, assumptions: AbstractSet[Schema],
                     lines: Sequence[Proof.Line], line_number: int) -> bool:
            """Checks if the current line is validly justified in the context of
            the specified proof.

            Parameters:
                assumptions: assumptions/axioms of the proof.
                lines: lines of the proof.
                line_number: line number of the current line in the given lines.

            Returns:
                ``True`` if the assumption/axiom of the current line is an
                assumption/axiom of the specified proof and if the formula
                justified by the current line is a valid instance of this
                assumption/axiom via the instantiation map of the current line,
                ``False`` otherwise.
            """
            assert line_number < len(lines) and lines[line_number] is self
            assumption_is_valid = self.assumption in assumptions
            formula_is_valid = self.formula == self.assumption.instantiate(self.instantiation_map)
            if assumption_is_valid and formula_is_valid:
                return True
            else:
                print(f'Invalid line [{line_number, self}]\nassumption is valid: {assumption_is_valid}\nformula is valid: {formula_is_valid}')
                return False
            # Harris J. Bolus - Task 9.5

        @staticmethod
        def parse(string: str) -> Proof.AssumptionLine:
            """Parses the given valid string representation into an AssumptionLine.

            Parameters:
                string: string to parse.

            Returns:
                An AssumptionLine whose standard string representation is the given string.
            """
            formula = Formula.parse(string.split(') ', maxsplit=1)[1].split('    (')[0])
            assumption, instantiation_map = string.split('(Assumption ')[1].split(' instantiated with ')
            assumption = Schema.parse(assumption)
            instantiation_map = instantiation_map[1:-2].replace("'",'').replace(' ','').split(',')
            if instantiation_map and instantiation_map[0]:
                instantiation_map = dict(i.split(':') for i in instantiation_map)
                for key in instantiation_map:
                    if is_constant(key):
                        instantiation_map[key] = Term.parse(instantiation_map[key])
                    elif is_relation(key):
                        instantiation_map[key] = Formula.parse(instantiation_map[key])
            else:
                instantiation_map = {}
            return Proof.AssumptionLine(formula, assumption, instantiation_map)
            # personal task

    @frozen
    class MPLine:
        """An immutable proof line justified by the Modus Ponens (MP) inference
        rule.

        Attributes:
            formula (`~predicates.syntax.Formula`): the formula justified by the
                line.
            antecedent_line_number (`int`): the line number of the antecedent of
                the MP inference justifying the line.
            conditional_line_number (`int`): the line number of the conditional
                of the MP inference justifying the line.
        """
        formula: Formula
        antecedent_line_number: int
        conditional_line_number: int

        def __init__(self, formula: Formula, antecedent_line_number: int,
                     conditional_line_number: int):
            """Initializes a `~Proof.MPLine` from its formula and line numbers
            of the antecedent and conditional of the MP inference justifying it.

            Parameters:
                formula: the formula to be justified by the line.
                antecedent_line_number: the line number of the antecedent of the
                    MP inference to justify the line.
                conditional_line_number: the line number of the conditional of
                    the MP inference to justify the line.
            """
            self.formula = formula
            self.antecedent_line_number = antecedent_line_number
            self.conditional_line_number = conditional_line_number

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            return str(self.formula) + "    (MP from lines " + \
                   str(self.antecedent_line_number) + " and " + \
                   str(self.conditional_line_number) + ")"

        def is_valid(self, assumptions: AbstractSet[Schema],
                     lines: Sequence[Proof.Line], line_number: int) -> bool:
            """Checks if the current line is validly justified in the context of
            the specified proof.

            Parameters:
                assumptions: assumptions/axioms of the proof.
                lines: lines of the proof.
                line_number: line number of the current line in the given lines.

            Returns:
                ``True`` if the formula of the line from the given lines whose
                number is the conditional line number justifying the current
                line is ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'``,
                where `antecedent` is the formula of the line from the given
                lines whose number is the antecedent line number justifying the
                current line and `consequent` is the formula justified by the
                current line; ``False`` otherwise.
            """
            assert line_number < len(lines) and lines[line_number] is self
            formula_is_valid = lines[self.conditional_line_number].formula == Formula('->', lines[self.antecedent_line_number].formula, self.formula)
            if formula_is_valid and line_number > self.antecedent_line_number and line_number > self.conditional_line_number:
                return True
            else:
                print(f'Invalid line: [{self}]:\nformula is valid: {formula_is_valid}\nline is after antecedent: {line_number > self.antecedent_line_number}\nline is after consequent: {line_number > self.conditional_line_number}')
                return False
            # Harris J. Bolus - Task 9.6

        @staticmethod
        def parse(string: str) -> Proof.MPLine:
            """Parses the given valid string representation into an MPLine.

            Parameters:
                string: string to parse.

            Returns:
                An MPLine whose standard string representation is the given string.
            """
            formula = Formula.parse(string.split(') ', maxsplit=1)[1].split('    (', maxsplit=1)[0])
            antecedent, conditional = string.split(' lines ')[1][:-1].split(' and ')
            return Proof.MPLine(formula, int(antecedent), int(conditional))
            # personal task

    @frozen
    class UGLine:
        """An immutable proof line justified by the Universal Generalization
        (UG) inference rule.

        Attributes:
            formula (`~predicates.syntax.Formula`): the formula justified by the
                line.
            nonquantified_line_number (`int`): the line number of the statement
                quantified by the formula.
        """
        formula: Formula
        nonquantified_line_number: int

        def __init__(self, formula: Formula, nonquantified_line_number: int):
            """Initializes a `~Proof.UGLine` from its formula and line number of
            the statement quantified by the formula.

            Parameters:
                formula: the formula to be justified by the line.
                nonquantified_line_number: the line number of the statement
                    quantified by the formula.
            """
            self.formula = formula
            self.nonquantified_line_number = nonquantified_line_number

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            return str(self.formula) + "    (UG of line " + \
                   str(self.nonquantified_line_number) + ")"

        def is_valid(self, assumptions: AbstractSet[Schema],
                     lines: Sequence[Proof.Line], line_number: int) -> bool:
            """Checks if the current line is validly justified in the context of
            the specified proof.

            Parameters:
                assumptions: assumptions/axioms of the proof.
                lines: lines of the proof.
                line_number: line number of the current line in the given lines.

            Returns:
                ``True`` if the formula of the current line is of the form
                `'Ax[nonquantified]'`, where
                `nonquantified` is the formula of the line from the given lines
                whose number is the nonquantified line number justifying the
                current line and `x` is any variable name; ``False`` otherwise.
            """
            assert line_number < len(lines) and lines[line_number] is self
            assumption_is_prior = line_number > self.nonquantified_line_number
            if quantifier_is_valid := self.formula.root == 'A':
                variable_is_valid = is_variable(self.formula.variable)
                formula_is_valid = self.formula.statement == lines[self.nonquantified_line_number].formula
                if formula_is_valid and variable_is_valid and assumption_is_prior:
                    return True
                else:
                    print(f'Invalid line [{self}]\nassumption is prior: {assumption_is_prior}\nquantifier_is_valid: {quantifier_is_valid}\nvariable_is_valid: {variable_is_valid}\nformula_is_valid: {formula_is_valid}')
                    return False
            print(f'Invalid line [{self}]\nassumption is prior: {assumption_is_prior}\nquantifier_is_valid: {quantifier_is_valid}')
            return False
            # Harris J. Bolus - Task 9.7

        @staticmethod
        def parse(string: str) -> Proof.UGLine:
            """Parses the given valid string representation into a UGLine.

            Parameters:
                string: string to parse.

            Returns:
                A UGLine whose standard string representation is the given string.
            """
            prefix, suffix = string[:-1].split('    (UG of line ')
            formula = Formula.parse(prefix.split(') ',maxsplit=1)[1])
            return Proof.UGLine(formula, int(suffix))
            # personal task

    @frozen
    class TautologyLine:
        """An immutable proof line justified as a tautology.

        Attributes:
            formula (`~predicates.syntax.Formula`): the formula justified by the
                line.
        """
        formula: Formula

        def __init__(self, formula: Formula):
            """Initializes a `~Proof.TautologyLine` from its formula.

            Parameters:
                formula: the formula to be justified by the line.
            """
            self.formula = formula

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            return str(self.formula) + "    (Tautology)"

        def is_valid(self, assumptions: AbstractSet[Schema],
                     lines: Sequence[Proof.Line], line_number: int) -> bool:
            """Checks if the current line is validly justified in the context of
            the specified proof.

            Parameters:
                assumptions: assumptions/axioms of the proof.
                lines: lines of the proof.
                line_number: line number of the current line in the given lines.

            Returns:
                ``True`` if the formula justified by the current line is a
                (predicate-logic) tautology, ``False`` otherwise.
            """
            assert line_number < len(lines) and lines[line_number] is self
            prop_skeleton = self.formula.propositional_skeleton()[0]
            if is_tautology := is_propositional_tautology(prop_skeleton):
                return True
            else:
                print(f'Invalid line: {self}\nThe formula is not a predicate logic tautology because {prop_skeleton} is not a propositional logic tautology')
                return False
            # Harris J. Bolus - Task 9.9

        @staticmethod
        def parse(string: str) -> Proof.TautologyLine:
            """Parses the given valid string representation into a TautologyLine.

            Parameters:
                string: string to parse.

            Returns:
                A TautologyLine whose standard string representation is the given string.
            """
            return Proof.TautologyLine(Formula.parse(string.split(') ',maxsplit=1)[1].split('    (')[0]))
            # personal task

    #: An immutable proof line.
    Line = Union[AssumptionLine, MPLine, UGLine, TautologyLine]

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.conclusion) + ' from assumptions/axioms:\n'
        for assumption in self.assumptions:
            r += '  '  + str(assumption) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += 'QED\n'
        return r

    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed
        conclusion from (instances of) its assumptions/axioms.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            conclusion from (instances of) its assumptions/axioms, ``False``
            otherwise.
        """
        if len(self.lines) == 0 or self.lines[-1].formula != self.conclusion:
            return False
        for line_number in range(len(self.lines)):
            if not self.lines[line_number].is_valid(self.assumptions,
                                                    self.lines, line_number):
                return False
        return True

    @staticmethod
    def parse(string: str) -> Proof:
        """Parses the given valid string representation into a Proof.

        Parameters:
            string: string to parse.

        Returns:
            A proof whose standard string representation is the given string.
        """
        conclusion, suffix = string.split('\n', maxsplit=1)
        conclusion = Formula.parse(conclusion.split('Proof of ')[1].split(' from')[0])

        assumptions, suffix = suffix.split('Lines:\n')
        if assumptions:
            assumptions = [Schema.parse(i) for i in assumptions.replace('  ','').split('\n') if i]

        lines = [i for i in suffix.split('\n')[:-1]]
        new_lines = []
        for line in lines:
            if 'Assumption' in line:
                new_lines.append(Proof.AssumptionLine.parse(line))
            elif 'MP from lines' in line:
                new_lines.append(Proof.MPLine.parse(line))
            elif 'Tautology' in line:
                new_lines.append(Proof.TautologyLine.parse(line))
            elif 'UG of line' in line:
                new_lines.append(Proof.UGLine.parse(line))
        return Proof(assumptions, conclusion, new_lines)
        # personal task

    def cited_by(self, line_number) -> list:
        """Returns a list of lines cited by the given line"""

        line = self.lines[line_number]
        if isinstance(line, Proof.UGLine):
            return [line.nonquantified_line_number]
        elif isinstance(line, Proof.MPLine):
            return [line.antecedent_line_number, line.conditional_line_number]
        else:
            return []
        # personal task

    def uncite_duplicate_lines(self) -> list:
        """Adjusts the assumptions of any line that cites a previous line with a duplicate
       so that its assumptions cite the first occurence of that formula."""

        formulae = [line.formula for line in self.lines]
        duplicates = []
        first_occurrences = {}
        for line_number in range(len(formulae)):
            formula = formulae[line_number]
            if formula in formulae[:line_number]:
                duplicates.append(line_number)
                if formula not in first_occurrences:
                    first_occurrences[formula] = line_number

        replacement_dict = {}
        for line_number in duplicates:
            replacement_dict[line_number] = first_occurrences[self.lines[line_number].formula]

        adjusted = []
        for line in self.lines:
            if isinstance(line, Proof.UGLine):
                if line.nonquantified_line_number in replacement_dict:
                    adjusted.append(Proof.UGLine(line.formula,
                                              replacement_dict[line.nonquantified_line_number]))
                else:
                    adjusted.append(line)
            elif isinstance(line, Proof.MPLine):
                if line.antecedent_line_number in replacement_dict:
                    antecedent = replacement_dict[line.antecedent_line_number]
                else:
                    antecedent = line.antecedent_line_number

                if line.conditional_line_number in replacement_dict:
                    conditional = replacement_dict[line.conditional_line_number]
                else:
                    conditional = line.conditional_line_number

                adjusted.append(Proof.MPLine(line.formula,
                                              antecedent,
                                              conditional))
            else:
                adjusted.append(line)
        return Proof(self.assumptions, self.conclusion, adjusted)
        # personal task

    def uncited_lines(self) -> list:
        """Returns a list of all lines that are not cited by the conclusion, or
        not cited by any line that is cited by the conclusion."""
        #add conclusion
        cited = {len(self.lines)-1}
        temp = list(cited)
        #starting with conclusion, add cited lines to temp and cited. Follow up by finding lines cited by temp, and reset temp.
        while temp:
            current = temp.pop()
            new = self.cited_by(current)
            for i in new:
                temp.insert(0,i)
                cited.add(i)

        return set(range(len(self.lines)))-cited
        # personal task

    def remove_uncited_lines(self) -> Proof:
        """Returns a new Proof of the same conclusion, with unncessary lines removed."""
        lines_to_remove = self.uncited_lines()
        lines_to_keep = sorted(set(i for i in range(len(self.lines))) - set(lines_to_remove))

        line_dict = {lines_to_keep[i]:i for i in range(len(lines_to_keep))}

        new_lines = []
        for line in range(len(self.lines)):
            if line not in lines_to_remove:
                new_lines.append(self.lines[line])
                line = self.lines[line]

        renumbered_lines = []
        for line in new_lines:
            if isinstance(line, Proof.UGLine):
                renumbered_lines.append(Proof.UGLine(line.formula,
                                              line_dict[line.nonquantified_line_number]))

            elif isinstance(line, Proof.MPLine):
                renumbered_lines.append(Proof.MPLine(line.formula,
                                              line_dict[line.antecedent_line_number],
                                              line_dict[line.conditional_line_number]))
            else:
                renumbered_lines.append(line)
        return Proof(self.assumptions, self.conclusion, renumbered_lines)
        # personal task

    def clean(self) -> Proof:
        """Returns a proof with no duplicated or unnecessary lines."""
        proof = self.uncite_duplicate_lines()
        proof = self.remove_uncited_lines()
        print(f'Removed {len(self.lines)-len(proof.lines)} lines')
        assert self.is_valid() == proof.is_valid()
        return proof
        # personal task

from propositions.proofs import Proof as PropositionalProof, \
                                InferenceRule as PropositionalInferenceRule, \
                                SpecializationMap as \
                                PropositionalSpecializationMap
from propositions.axiomatic_systems import AXIOMATIC_SYSTEM as \
                                           PROPOSITIONAL_AXIOMATIC_SYSTEM, \
                                           MP, I0, I1, D, I2, N, NI, NN, R
from propositions.tautology import prove_tautology as \
                                   prove_propositional_tautology

# Schema equivalents of the propositional-logic axioms for implication and
# negation

#: Schema equivalent of the propositional-logic self implication axiom
#: `~propositions.axiomatic_systems.I0`.
I0_SCHEMA = Schema(Formula.parse('(P()->P())'), {'P'})
#: Schema equivalent of the propositional-logic implication introduction (right)
#: axiom `~propositions.axiomatic_systems.I1`.
I1_SCHEMA = Schema(Formula.parse('(Q()->(P()->Q()))'), {'P', 'Q'})
#: Schema equivalent of the propositional-logic self-distribution of implication
#: axiom `~propositions.axiomatic_systems.D`.
D_SCHEMA = Schema(Formula.parse(
    '((P()->(Q()->R()))->((P()->Q())->(P()->R())))'), {'P', 'Q', 'R'})
#: Schema equivalent of the propositional-logic implication introduction (left)
#: axiom `~propositions.axiomatic_systems.I2`.
I2_SCHEMA = Schema(Formula.parse('(~P()->(P()->Q()))'), {'P', 'Q'})
#: Schema equivalent of the propositional-logic converse contraposition axiom
#: `~propositions.axiomatic_systems.N`.
N_SCHEMA  = Schema(Formula.parse('((~Q()->~P())->(P()->Q()))'), {'P', 'Q'})
#: Schema equivalent of the propositional-logic negative-implication
#: introduction axiom `~propositions.axiomatic_systems.NI`.
NI_SCHEMA = Schema(Formula.parse('(P()->(~Q()->~(P()->Q())))'), {'P', 'Q'})
#: Schema equivalent of the propositional-logic double-negation introduction
#: axiom `~propositions.axiomatic_systems.NN`.
NN_SCHEMA = Schema(Formula.parse('(P()->~~P())'), {'P'})
#: Schema equivalent of the propositional-logic resolution axiom
#: `~propositions.axiomatic_systems.R`.
R_SCHEMA  = Schema(Formula.parse(
    '((Q()->P())->((~Q()->P())->P()))'), {'P', 'Q'})

#: Schema system equivalent of the axioms of the propositional-logic large
#: axiomatic system for implication and negation
#: `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS = {I0_SCHEMA, I1_SCHEMA, D_SCHEMA,
                                          I2_SCHEMA, N_SCHEMA, NI_SCHEMA,
                                          NN_SCHEMA, R_SCHEMA}

#: Mapping from propositional-logic axioms for implication and negation to their
#: schema equivalents.
PROPOSITIONAL_AXIOM_TO_SCHEMA = {
        I0: I0_SCHEMA, I1: I1_SCHEMA, D: D_SCHEMA, I2: I2_SCHEMA, N: N_SCHEMA,
        NI: NI_SCHEMA, NN: NN_SCHEMA, R: R_SCHEMA}

def _axiom_specialization_map_to_schema_instantiation_map(
        propositional_specialization_map: PropositionalSpecializationMap,
        substitution_map: Mapping[str, Formula]) -> Mapping[str, Formula]:
    """Composes the given propositional-logic specialization map, specifying the
    transformation from a propositional-logic axiom to a specialization of it,
    and the given substitution map, specifying the transformation from that
    specialization (as a propositional skeleton) to a predicate-logic formula,
    into an instantiation map specifying how to instantiate the schema
    equivalent of that axiom into the same predicate-logic formula.

    Parameters:
        propositional_specialization_map: mapping specifying how some
            propositional-logic axiom `axiom` (which is not specified) from
            `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM` specializes into
            some specialization `specialization` (which is also not specified),
            and containing no constants or operators beyond ``'~'``, ``'->'``,
            ``'|'``, and ``'&'``.
        substitution_map: mapping from each propositional variable name of
            `specialization` to a predicate-logic formula.

    Returns:
        An instantiation map for instantiating the schema equivalent of `axiom`
        into the predicate-logic formula obtained from its propositional
        skeleton `specialization` by the given substitution map.

    Examples:
        >>> _axiom_specialization_map_to_schema_instantiation_map(
        ...     {'p': PropositionalFormula.parse('(z1->z2)'),
        ...      'q': PropositionalFormula.parse('~z1')},
        ...     {'z1': Formula.parse('Ax[(x=5&M())]'),
        ...      'z2': Formula.parse('R(f(8,9))')})
        {'P': (Ax[(x=5&M())]->R(f(8,9))), 'Q': ~Ax[(x=5&M())]}
    """
    for variable in propositional_specialization_map:
        assert is_propositional_variable(variable)
        for operator in propositional_specialization_map[variable].operators():
            assert is_unary(operator) or is_binary(operator)
    for variable in substitution_map:
        assert is_propositional_variable(variable)

    new_dict = {}
    for key in propositional_specialization_map:
        specialization = propositional_specialization_map[key]
        pred_formula = Formula.from_propositional_skeleton(specialization, substitution_map)
        new_dict[key.upper()] = pred_formula
    return new_dict
    # Harris J. Bolus - Task 9.11a

def _prove_from_skeleton_proof(formula: Formula,
                               skeleton_proof: PropositionalProof,
                               substitution_map: Mapping[str, Formula]) -> \
        Proof:
    """Translates the given proof of a propositional skeleton of the given
    predicate-logic formula into a proof of that predicate-logic formula.

    Parameters:
        formula: predicate-logic formula to prove.
        skeleton_proof: valid propositional-logic proof of a propositional
            skeleton of the given formula, from no assumptions and via
            `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`, and containing
            no constants or operators beyond ``'~'``, ``'->'``, ``'|'``, and
            ``'&'``.
        substitution_map: mapping from each propositional variable name of the
            propositional skeleton of the given formula that is proven in the
            given proof to the respective predicate-logic subformula of the
            given formula.

    Returns:
        A valid predicate-logic proof of the given formula from the axioms
        `PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS` via only assumption lines and
        MP lines.
    """
    skeleton_proof = skeleton_proof.clean()
    assert len(skeleton_proof.statement.assumptions) == 0 and \
           skeleton_proof.rules.issubset(PROPOSITIONAL_AXIOMATIC_SYSTEM) and \
           skeleton_proof.is_valid()
    assert Formula.from_propositional_skeleton(
        skeleton_proof.statement.conclusion, substitution_map) == formula
    for line in skeleton_proof.lines:
        for operator in line.formula.operators():
            assert is_unary(operator) or is_binary(operator)

    lines = []
    for line in skeleton_proof.lines:
        new_formula = Formula.from_propositional_skeleton(line.formula, substitution_map)

        if line.rule in PROPOSITIONAL_AXIOM_TO_SCHEMA:
            new_rule = PROPOSITIONAL_AXIOM_TO_SCHEMA[line.rule]

            propositional_specialization_map = PropositionalInferenceRule._formula_specialization_map(line.rule.conclusion,line.formula)
            instantiation_map = _axiom_specialization_map_to_schema_instantiation_map(propositional_specialization_map, substitution_map)

            lines.append(Proof.AssumptionLine(new_formula, new_rule, instantiation_map))

        else:
            lines.append(Proof.MPLine(new_formula, *line.assumptions))

    return Proof(PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS, formula, lines)
    # Harris J. Bolus - Task 9.11b

def prove_tautology(tautology: Formula) -> Proof:
    """Proves the given predicate-logic tautology.

    Parameters:
        tautology: predicate-logic tautology, whose propositional skeleton
            contains no constants or operators beyond ``'->'`` and ``'~'``, to
            prove.

    Returns:
        A valid proof of the given predicate-logic tautology from the axioms
        `PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS` via only assumption lines
        and MP lines.
    """
    skeleton, substitution_map = tautology.propositional_skeleton()
    assert is_propositional_tautology(skeleton)
    assert skeleton.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    skeleton_proof = prove_propositional_tautology(skeleton).clean()
    return _prove_from_skeleton_proof(tautology, skeleton_proof, substitution_map)
    # Harris J. Bolus - Task 9.12

def is_tautology(formula: Union[Formula, str]) -> bool:
    if isinstance(formula, str):
        formula = Formula.parse(formula)
    return is_propositional_tautology(formula.propositional_skeleton()[0])
# personal task

# consider changing instantiate so that it can accept either strings or Term items as values of dict (not just strings for variable values and Term objects for constant values)
# pg. 148
# problematic example 1
# schema = Schema(Formula.parse('(Ex[R(c)]->R(c))'), {'c'})
# schema.instantiate({'c':Term('x')})
# returns unfortunate instance (Ex[R(x)]->R(x))

# problematic example 2
# schema = Schema(Formula.parse('Ey[~y=x]'), {'y'})
# schema.instantiate({'y':'x'})
# returns unfortunate instance Ey[~x=x]

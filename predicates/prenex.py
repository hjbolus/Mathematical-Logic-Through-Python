# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator, is_z_and_number
import sys
sys.path.append('/Users/harrisbolus/Desktop/Fun/Mathematical logic thru python')
from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        `False` if the given formula contains any quantifiers, `True`
        otherwise.
    """
    return formula.quantifiers() == set()
    # Harris J. Bolus - Task 11.3a

def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        `True` if the given formula in prenex normal form, `False`
        otherwise.
    """
    while is_quantifier(formula.root):
        formula = formula.statement
    return is_quantifier_free(formula)
    # Harris J. Bolus - Task 11.3b

def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula `'((`formula1`->`formula2`)&(`formula2`->`formula1`))'`.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))
#     return Formula('<->', formula1, formula2)

@lru_cache(maxsize=128)
def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        `False` if in the given formula some variable name has both bound and
        free occurrences or is quantified by more than one quantifier, `True`
        otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.statement)
        else:
            assert is_equality(formula.root) or is_relation(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)

def _uniquely_rename_quantified_variables_helper(formula):
    root = formula.root
    if is_binary(root):
        first, proof1 = _uniquely_rename_quantified_variables_helper(formula.first)
        second, proof2 = _uniquely_rename_quantified_variables_helper(formula.second)
        new_formula = Formula(root, first, second)
        steps = set()
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        if proof1:
            step1 = prover.add_proof(proof1.conclusion, proof1)
            steps.add(step1)
        if proof2:
            step2 = prover.add_proof(proof2.conclusion, proof2)
            steps.add(step2)
        step3 = prover.add_tautological_implication(equivalence_of(formula, new_formula), steps)

        proof = prover.qed()
        return new_formula, proof

    elif is_unary(root):
        new_formula, proof_of_affirmative = _uniquely_rename_quantified_variables_helper(formula.first)
        new_formula = Formula('~', new_formula)

        proof_of_negative = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        step1 = proof_of_negative.add_proof(proof_of_affirmative.conclusion, proof_of_affirmative)
        step2 = proof_of_negative.add_tautological_implication(equivalence_of(formula, new_formula), {step1})
        proof = proof_of_negative.qed()
        return new_formula, proof

    elif is_relation(root) or is_equality(root):
        return formula, None

    elif is_quantifier(root):
        if root == 'E':
            schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-1]
        else:
            schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2]

        variable = formula.variable
        new_variable = next(fresh_variable_name_generator)
        inner_sub_formula, proof_of_inner_subs = _uniquely_rename_quantified_variables_helper(formula.statement)
        new_formula = Formula(root, new_variable, inner_sub_formula.substitute({variable: Term(new_variable)}))

        if proof_of_inner_subs:
            #then I just need to change one variable to go from inner_sub_formula to new_formula
            prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
            step1 = prover.add_proof(proof_of_inner_subs.conclusion, proof_of_inner_subs)
            inst_map = {
                    'R': formula.statement.substitute({variable:Term('_')}),
                    'Q': inner_sub_formula.substitute({variable: Term('_')}),
                    'x': variable,
                    'y': new_variable}
            step2 = prover.add_instantiated_assumption(schema.instantiate(inst_map), schema, inst_map)
            step3 = prover.add_mp(prover._lines[step2].formula.second, step1, step2)

        else:
            #prove formula -> new_formula
            prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
            inst_map = {'R': formula.statement.substitute({variable: Term('_')}),
                        'Q': formula.statement.substitute({variable: Term('_')}),
                        'x': variable,
                        'y': new_variable}
            step2 = prover.add_instantiated_assumption(schema.instantiate(inst_map), schema, inst_map)
            step3 = prover.add_tautological_implication(prover._lines[step2].formula.second, {step2})
        return new_formula, prover.qed()

def _uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            `z` followed by a number.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`(`~logic_utils.fresh_variable_name_generator`)`. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`(`formula`,`returned_formula`)`)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(
        ...     formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    if isinstance(formula, str):
        formula = Formula.parse(formula)
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    if has_uniquely_named_variables(formula):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    else:
        return _uniquely_rename_quantified_variables_helper(formula)
    # Harris J. Bolus - Task 11.5

def _pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    `'~`Q1`x1`[`Q2`x2`[`...`Qn`xn`[`inner_formula`]`...`]]'` to an equivalent
    formula of the form `'`Q'1`x1`[`Q'2`x2`[`...`Q'n`xn`[~`inner_formula`]`...`]]'`,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form `'~`Q1`x1`[`Q2`x2`[`...`Qn`xn`[`inner_formula`]`...`]]'` where
            `n`>=0, each `Qi` is a quantifier, each `xi` is a variable name, and
            `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the given
        formula, but of the form `'`Q'1`x1`[`Q'2`x2`[`...`Q'n`xn`[~`inner_formula`]`...`]]'`
        where each `Q'i` is a quantifier, and where the `xi` variable names and `inner_formula`
        are the same as in the given formula. The second element of the pair is a proof of
        the equivalence of the given formula and the returned formula (i.e., a proof of
        `equivalence_of`(`formula`,`returned_formula`)`) via `~predicates.prover.Prover.AXIOMS`
        and `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)

    if is_quantifier_free(formula):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        prover.add_tautology(equivalence_of(formula, formula))
        new_formula = formula
    else:
        variable = formula.first.variable
        statement = formula.first.statement

        if formula.first.root == 'A':
            transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[0]
            quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-1] #consider switching this to -1
            new_formula = Formula('E', formula.first.variable, Formula('~', statement))
        else:
            transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[1]
            quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2] #and this to -2
            new_formula = Formula('A', formula.first.variable, Formula('~', statement))

        new_statement, new_statement_proof = _pull_out_quantifications_across_negation(new_formula.statement)
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

        if is_quantifier_free(statement):
            inst_map = {'R': statement.substitute({variable: Term('_')}), 'x': variable}
            prover.add_instantiated_assumption(transfer_schema.instantiate(inst_map), transfer_schema, inst_map)

        else:
            step1 = prover.add_proof(new_statement_proof.conclusion, new_statement_proof)
            inst_map = {'R': Formula('~', statement).substitute({variable: Term('_')}),
                        'Q': new_statement.substitute({variable: Term('_')}),
                        'x': variable,
                        'y': variable}
            step2 = prover.add_instantiated_assumption(quantification_schema.instantiate(inst_map), quantification_schema, inst_map)
            step3 = prover.add_mp(prover._lines[step2].formula.second, step1, step2)
            new_formula = prover._lines[step3].formula.first.second

            inst_map = {'R': statement.substitute({variable: Term('_')}),
                        'x': variable}
            step4 = prover.add_instantiated_assumption(transfer_schema.instantiate(inst_map), transfer_schema, inst_map)
            step5 = prover.add_tautological_implication(equivalence_of(formula, new_formula), {step3, step4})
    return new_formula, prover.qed()
    # Harris J. Bolus - Task 11.6

def _pull_out_quantifications_from_left_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    `'(`Q1x1`[`Q2x2`[`... `Qnxn`[`inner_first`]`... `]]`*``second`)'`
    to an equivalent formula of the form
    `'`Q'1x1`[`Q'2x2`[`... `Q'nxn`[(`inner_first``*``second`)]`... `]]'`
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            `'(`Q1``x1`[`Q2``x2`[`... `Qn``xn`[`inner_first`]`... `]]`*``second`)'`
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        `'`Q'1``x1`[`Q'2``x2`[`... `Q'n``xn`[(`inner_first``*``second`)]`... `]]'`
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`(`formula`,`returned_formula`)`)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    root = formula.root
    assert has_uniquely_named_variables(formula)
    assert is_binary(root)

    if not is_quantifier(formula.first.root):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        prover.add_tautology(equivalence_of(formula, formula))
        new_formula = formula

    else:
        quantifier = formula.first.root
        variable = formula.first.variable
        first_statement = formula.first.statement
        second = formula.second
        assert formula == Formula(root, Formula(quantifier, variable, first_statement), second)
        new_formula = Formula(quantifier, variable, Formula(root, first_statement, second))
        new_statement = new_formula.statement
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

        if root == '&':
            if quantifier == 'A':
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[2]
                #(∀x[φ(x)]&ψ)<->∀x[(φ(x)&ψ)]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2]
                #((φ(x)<->ψ(x))->(∀x[φ(x)]<->∀y[ψ(y)]))

            else:
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[3]
                #(∃x[φ(x)]&ψ)<->∃x[(φ(x)&ψ)]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-1]
                #((φ(x)<->ψ(x))->(∃x[φ(x)]<->∃y[ψ(y)]))

        elif root == '|':
            if quantifier == 'A':
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[6]
                #(∀x[φ(x)]|ψ)<->∀x[(φ(x)|ψ)]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2]
                ##((φ(x)<->ψ(x))->(∀x[φ(x)]<->∀y[ψ(y)]))

            else:
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[7]
                #(∃x[φ(x)]|ψ)<->∃x[(φ(x)|ψ)]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-1]
                #((φ(x)<->ψ(x))->(∃x[φ(x)]<->∃y[ψ(y)])

        elif root == '->':
            if quantifier == 'A':
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[10]
                #(∀x[φ(x)]→ψ) is equivalent to ∃x[(φ(x)→ψ)]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-1]
                ##((φ(x)<->ψ(x))->(∀x[φ(x)]<->∀y[ψ(y)]))
                new_formula = Formula('E', variable, Formula(root, first_statement, second))

            else:
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[11]
                #(∃x[φ(x)]→ψ) is equivalent to ∀x[(φ(x)→ψ)]’
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2]
                #((φ(x)<->ψ(x))->(∃x[φ(x)]<->∃y[ψ(y)])
                new_formula = Formula('A', variable, Formula(root, first_statement, second))


        if is_binary(new_formula.statement.root):
            intermediate_formula, intermediate_proof = _pull_out_quantifications_from_left_across_binary_operator(new_formula.statement)
#             step1: prove inner transformation
            step1 = prover.add_proof(intermediate_proof.conclusion, intermediate_proof)
            if is_quantifier_free(intermediate_formula):
                #prove (Ax[T(x)]&S()) <-> Ax[T(x)&S()]
                inst_map = {'R': first_statement.substitute({variable: Term('_')}),
                        'Q': second.substitute({variable: Term('_')}),
                        'x': variable}
                prover.add_instantiated_assumption(transfer_schema.instantiate(inst_map), transfer_schema, inst_map)

            else:
#                 step2: prove (Ax[T(x)]&S()) <-> Ax[(T(x)&S())] -> Ay[(Ax[T(x)]&S())] <-> Ay[Ax[(T(x)&S())]] by quantification schema
                inst_map = {'R': new_formula.statement.substitute({variable: Term('_')}),
                            'Q': intermediate_formula.substitute({variable: Term('_')}),
                            'x': variable,
                            'y': variable}
                step2 = prover.add_instantiated_assumption(quantification_schema.instantiate(inst_map), quantification_schema, inst_map)

#                 step3: prove Ay[(Ax[T(x)]&S())] <-> Ay[Ax[(T(x)&S())]] by mp from step1 and step2
                step3 = prover.add_mp(prover._lines[step2].formula.second, step1, step2)

#                 step4: prove (Ay[Ax[T(x)]]&S()) <-> Ay[(Ax[T(x)]&S())] by transfer schema
                inst_map = {'R': first_statement.substitute({variable: Term('_')}),
                            'Q': second.substitute({variable: Term('_')}),
                            'x': variable}
                step4 = prover.add_instantiated_assumption(transfer_schema.instantiate(inst_map), transfer_schema, inst_map)

#                 step5: taut imp from step3 and step4 to prove (Ay[Ax[T(x)]]&S()) <-> Ay[Ax[(T(x)&S())]]
                new_formula = prover._lines[step3].formula.first.second
                step5 = prover.add_tautological_implication(equivalence_of(formula, new_formula), {step3, step4})
        else:
            inst_map = {'R': first_statement.substitute({variable: Term('_')}),
                        'Q': second.substitute({variable: Term('_')}),
                        'x': variable}
            prover.add_instantiated_assumption(transfer_schema.instantiate(inst_map), transfer_schema, inst_map)
    return new_formula, prover.qed()
    # Harris J. Bolus - Task 11.7a

def _pull_out_quantifications_from_right_across_binary_operator(formula:
                                                                Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    `'(`first`*`Q1`x1`[`Q2`x2`[`...`Qn`xn`[`inner_second`]`...`]])'`
    to an equivalent formula of the form
    `'`Q'1`x1`[`Q'2`x2`[`...`Q'n`xn`[(`first`*`inner_second`)]`...`]]'`
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            `'(`first`*`Q1`x1`[`Q2`x2`[`...`Qn`xn`[`inner_second`]`...`]])'`
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        `'`Q'1`x1`[`Q'2`x2`[`...`Q'n`xn`[(`first`*`inner_second`)]`...`]]'`
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`(`formula`,`returned_formula`)`)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    root = formula.root
    assert has_uniquely_named_variables(formula)
    assert is_binary(root)

    if not is_quantifier(formula.second.root):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        prover.add_tautology(equivalence_of(formula, formula))
        new_formula = formula

    else:
        quantifier = formula.second.root
        variable = formula.second.variable
        second_statement = formula.second.statement
        first = formula.first
        assert formula == Formula(root, first, Formula(quantifier, variable, second_statement))
        new_formula = Formula(quantifier, variable, Formula(root, first, second_statement))
        new_statement = new_formula.statement
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

        if root == '&':
            if quantifier == 'A':
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[4]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2]

            else:
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[5]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-1]

        elif root == '|':
            if quantifier == 'A':
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[8]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2]

            else:
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[9]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-1]

        elif root == '->':
            if quantifier == 'A':
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[12]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2]

            else:
                transfer_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[13]
                quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-1]

        if is_binary(new_formula.statement.root):
            intermediate_formula, intermediate_proof = _pull_out_quantifications_from_right_across_binary_operator(new_formula.statement)
            step1 = prover.add_proof(intermediate_proof.conclusion, intermediate_proof)

            if is_quantifier_free(intermediate_formula):
                inst_map = {'R': second_statement.substitute({variable: Term('_')}),
                        'Q': first.substitute({variable: Term('_')}),
                        'x': variable}
                prover.add_instantiated_assumption(transfer_schema.instantiate(inst_map), transfer_schema, inst_map)

            else:
                inst_map = {'R': new_formula.statement.substitute({variable: Term('_')}),
                            'Q': intermediate_formula.substitute({variable: Term('_')}),
                            'x': variable,
                            'y': variable}
                step2 = prover.add_instantiated_assumption(quantification_schema.instantiate(inst_map), quantification_schema, inst_map)

                step3 = prover.add_mp(prover._lines[step2].formula.second, step1, step2)

                inst_map = {'R': second_statement.substitute({variable: Term('_')}),
                            'Q': first.substitute({variable: Term('_')}),
                            'x': variable}
                step4 = prover.add_instantiated_assumption(transfer_schema.instantiate(inst_map), transfer_schema, inst_map)

                new_formula = prover._lines[step3].formula.first.second
                step5 = prover.add_tautological_implication(equivalence_of(formula, new_formula), {step3, step4})
        else:
            inst_map = {'R': second_statement.substitute({variable: Term('_')}),
                        'Q': first.substitute({variable: Term('_')}),
                        'x': variable}
            prover.add_instantiated_assumption(transfer_schema.instantiate(inst_map), transfer_schema, inst_map)
    return new_formula, prover.qed()
    # Harris J. Bolus - Task 11.7b

def _pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    `'(`Q1`x1`[`Q2`x2`[`...`Qn`xn`[`inner_first`]`...`]]`*`P1`y1`[`P2`y2`[`...`Pm`ym`[`inner_second`]`...`]])'`
    to an equivalent formula of the form
    `'`Q'1`x1`[`Q'2`x2`[`...`Q'n`xn`[`P'1`y1`[`P'2`y2`[`...`P'm`ym`[(`inner_first`*`inner_second`)]`...`]]]`...`]]'`
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            `'(`Q1`x1`[`Q2`x2`[`...`Qn`xn`[`inner_first`]`...`]]`*`P1`y1`[`P2`y2`[`...`Pm`ym`[`inner_second`]`...`]])'`
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        `'`Q'1`x1`[`Q'2`x2`[`...`Q'n`xn`[`P'1`y1`[`P'2`y2`[`...`P'm`ym`[(`inner_first`*`inner_second`)]`...`]]]`...`]]'`
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`(`formula`,`returned_formula`)`)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    
    formula1, proof1 = _pull_out_quantifications_from_left_across_binary_operator(formula)
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    step1 = prover.add_proof(proof1.conclusion, proof1)

    inner_second = formula1
    quantification_layers = []
    while is_quantifier(inner_second.root):
        quantification_layers.append((inner_second.root, inner_second.variable))
        inner_second = inner_second.statement
    
    formula2, proof2 = _pull_out_quantifications_from_right_across_binary_operator(inner_second)
    stepx = prover.add_proof(proof2.conclusion, proof2)
    stepz = None
    for quantifier, variable in quantification_layers[::-1]:
        quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2] if quantifier == 'A' else ADDITIONAL_QUANTIFICATION_AXIOMS[-1]
        inst_map = {'R': inner_second.substitute({variable: Term('_')}),
                    'Q': formula2.substitute({variable: Term('_')}),
                    'x': variable,
                    'y': variable}
        stepy = prover.add_instantiated_assumption(quantification_schema.instantiate(inst_map), quantification_schema, inst_map)
        stepz = prover.add_mp(prover._lines[stepy].formula.second, stepx, stepy)
        inner_second = prover._lines[stepz].formula.first.first
        formula2 = prover._lines[stepz].formula.first.second
        stepx = stepz
    if stepz:
        prover.add_tautological_implication(equivalence_of(formula, formula2), {step1, stepz})
    return formula2, prover.qed()
    # Harris J. Bolus - Task 11.8

def _to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`(`formula`,`returned_formula`)`)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if is_in_prenex_normal_form(formula):
        new_formula = formula
        prover.add_tautology(equivalence_of(formula, new_formula))
        
    else:
        root = formula.root

        if is_unary(root):
            new_first, new_first_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
            new_formula, new_proof = _pull_out_quantifications_across_negation(Formula('~', new_first))
            
            step1 = prover.add_proof(new_first_proof.conclusion, new_first_proof)
            step2 = prover.add_proof(new_proof.conclusion, new_proof)
            
            if not new_proof.conclusion == equivalence_of(formula, new_formula):
                step3 = prover.add_tautological_implication(equivalence_of(formula, new_formula), {step1, step2})
            
        elif is_binary(root):
            new_first, new_first_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
            new_second, new_second_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.second)
            new_formula, new_proof = _pull_out_quantifications_across_binary_operator(Formula(root, new_first, new_second))
            
            step1 = prover.add_proof(new_first_proof.conclusion, new_first_proof)
            step2 = prover.add_proof(new_second_proof.conclusion, new_second_proof)
            step3 = prover.add_tautological_implication(equivalence_of(formula, Formula(root, new_first, new_second)), {step1, step2})
            step4 = prover.add_proof(new_proof.conclusion, new_proof)
            step5 = prover.add_tautological_implication(equivalence_of(formula, new_formula), {step3, step4})
            
        elif is_quantifier(root):
            variable = formula.variable
            new_statement, new_statement_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula.statement)
            new_formula = Formula(root, formula.variable, new_statement)
            
            step1 = prover.add_proof(new_statement_proof.conclusion, new_statement_proof)

            quantification_schema = ADDITIONAL_QUANTIFICATION_AXIOMS[-2] if root == 'A' else ADDITIONAL_QUANTIFICATION_AXIOMS[-1]
            inst_map = {'R': formula.statement.substitute({variable: Term('_')}),
                        'Q': new_statement.substitute({variable: Term('_')}),
                        'x': variable,
                        'y': variable}
            step2 = prover.add_instantiated_assumption(quantification_schema.instantiate(inst_map), quantification_schema, inst_map)
            step3 = prover.add_tautological_implication(prover._lines[step2].formula.second, {step1, step2})

    return new_formula, prover.qed()
    # Harris J. Bolus - Task 11.9

def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            `z` followed by a number.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`(`formula`,`returned_formula`)`)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    
    if is_in_prenex_normal_form(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        prenex_formula = formula
        
    elif has_uniquely_named_variables(formula):
        prenex_formula, prenex_proof = _to_prenex_normal_form_from_uniquely_named_variables(formula)
        prover.add_proof(prenex_proof.conclusion, prenex_proof)
        
    else:
        renamed_formula, renaming_proof = _uniquely_rename_quantified_variables(formula)
        prenex_formula, prenex_proof = _to_prenex_normal_form_from_uniquely_named_variables(renamed_formula)
        
        step1 = prover.add_proof(renaming_proof.conclusion, renaming_proof)
        step2 = prover.add_proof(prenex_proof.conclusion, prenex_proof)
        step3 = prover.add_tautological_implication(equivalence_of(formula, prenex_formula), {step1, step2})

    return prenex_formula, prover.qed().clean()
    # Harris J. Bolus - Task 11.10

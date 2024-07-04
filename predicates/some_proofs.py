# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/some_proofs.py

"""Some proofs in Predicate Logic."""
import sys
sys.path.append('/Users/harrisbolus/Desktop/Fun/Mathematical logic thru python')
from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import equivalence_of

def prove_syllogism(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_instantiated_assumption(
        '(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))',
        Prover.UI, {'R': '(Man(_)->Mortal(_))', 'c': 'aristotle'})
    step3 = prover.add_mp('(Man(aristotle)->Mortal(aristotle))', step1, step2)
    step4 = prover.add_assumption('Man(aristotle)')
    step5 = prover.add_mp('Mortal(aristotle)', step4, step3)
    return prover.qed()

def prove_syllogism_with_universal_instantiation(print_as_proof_forms: bool =
                                                 False) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_universal_instantiation('(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    return prover.qed()

def prove_syllogism_all_all(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautology(
        '((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))')
    step6 = prover.add_mp(
        '((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))', step2, step5)
    step7 = prover.add_mp('(Greek(x)->Mortal(x))', step4, step6)
    step8 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step7)
    return prover.qed()

def prove_syllogism_all_all_with_tautological_implication(print_as_proof_forms:
                                                          bool = False) -> \
        Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautological_implication(
        '(Greek(x)->Mortal(x))', {step2, step4})
    step6 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step5)
    return prover.qed()

def prove_syllogism_all_exists(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)

    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI,
        {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_ug('Ax[(Man(x)->Ex[Mortal(x)])]', step5)
    step7 = prover.add_instantiated_assumption(
        '((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])', Prover.ES,
        {'R': 'Man(_)', 'Q': 'Ex[Mortal(x)]'})
    step8 = prover.add_tautological_implication(
        'Ex[Mortal(x)]', {step2, step6, step7})
    return prover.qed()

def prove_syllogism_all_exists_with_existential_derivation(print_as_proof_forms:
                                                           bool = False) -> \
        Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)

    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI, {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_existential_derivation('Ex[Mortal(x)]', step2, step5)
    return prover.qed()

def prove_lovers(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)

    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[Ey[Loves(x,y)]]')
    step2 = prover.add_universal_instantiation('Ey[Loves(x,y)]', step1, 'x')
    step3 = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]')
    step4 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', step3, 'x')
    step5 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step4, 'z')
    instantiation_map = {'R':Formula.parse('Loves(x,_)'), 'Q':Formula.parse('Loves(z,x)'), 'x':'y'}
    step6 = prover.add_instantiated_assumption(Prover.ES.instantiate(instantiation_map), Prover.ES, instantiation_map)
    step7 = prover.add_and_introduction(7, step2)
    step8 = prover.add_mp('Loves(z,x)',11,8)
    step9 = prover.add_ug('Az[Loves(z,x)]', step8)
    step10 = prover.add_ug('Ax[Az[Loves(z,x)]]', step9)
    return prover.qed()
    # Task 10.4

def prove_homework(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)

    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'}, print_as_proof_forms)
    step1 = prover.add_assumption('~Ex[(Homework(x)&Fun(x))]')
    step2 = prover.add_instantiated_assumption('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])', Prover.EI, {'R': '(Homework(_)&Fun(_))', 'c': 'x'})
    step3 = prover.add_tautological_implication('~(Homework(x)&Fun(x)))',{step1,step2})
    step5 = prover.add_assumption('Ex[(Homework(x)&Reading(x))]')
    step6 = prover.add_tautology('(~(Homework(x)&Fun(x))->((Homework(x)&Reading(x))->(Reading(x)&~Fun(x))))')
    step7 = prover.add_mp('((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))', step3, step6)
    instantiation_map = {'R': Formula.parse('(Reading(_)&~Fun(_))'), 'c': Term('x'), 'x': 'x'}
    step8 = prover.add_instantiated_assumption('((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])', Prover.EI, instantiation_map)
    step9 = prover.add_tautology('(((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))->(((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])->((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])))')
    step10 = prover.add_mp('(((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])->((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))]))', step7, step9)
    step11 = prover.add_mp('((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])', step8, step10)
    step12 = prover.add_existential_derivation('Ex[(Reading(x)&~Fun(x))]', step5, step11)
    return prover.qed()
    # Task 10.5

#: The three group axioms
GROUP_AXIOMS = frozenset({'plus(0,x)=x', 'plus(minus(x),x)=0',
                          'plus(plus(x,y),z)=plus(x,plus(y,z))'})

def prove_group_right_neutral(stop_before_flipped_equality: bool,
                              stop_before_free_instantiation: bool,
                              stop_before_substituted_equality: bool,
                              stop_before_chained_equality: bool,
                              print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof created up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof created up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof created up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof created up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        '0=plus(minus(minus(x)),minus(x))', flipped_negation, {'x': 'minus(x)'})
    step8 = prover.add_flipped_equality(
        'plus(minus(minus(x)),minus(x))=0', step7)
    step9 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))',
        associativity, {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step10 = prover.add_free_instantiation('plus(0,0)=0', zero, {'x': '0'})
    step11 = prover.add_free_instantiation(
        'plus(x,0)=plus(0,plus(x,0))', flipped_zero, {'x': 'plus(x,0)'})
    step12 = prover.add_free_instantiation(
        'plus(0,plus(x,0))=plus(plus(0,x),0)', flipped_associativity,
        {'x': '0', 'y': 'x', 'z': '0'})
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)',
        step7, 'plus(plus(_,x),0)')
    step14 = prover.add_substituted_equality(
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)',
        step9, 'plus(_,0)')
    step15 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)',
        negation, 'plus(plus(minus(minus(x)),_),0)')
    step16 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))',
        associativity, {'x': 'minus(minus(x))', 'y': '0', 'z': '0'})
    step17 = prover.add_substituted_equality(
        'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)',
        step10, 'plus(minus(minus(x)),_)')
    step18 = prover.add_substituted_equality(
        'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))',
        flipped_negation, 'plus(minus(minus(x)),_)')
    step19 = prover.add_free_instantiation(
        'plus(minus(minus(x)),plus(minus(x),x))='
        'plus(plus(minus(minus(x)),minus(x)),x)', flipped_associativity,
        {'x': 'minus(minus(x))','y': 'minus(x)','z': 'x'})
    step20 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)', step8, 'plus(_,x)')
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        'plus(x,0)=x',
        [step11, step12, step13, step14, step15, step16, step17, step18, step19,
         step20, zero])
    return prover.qed()

def prove_group_unique_zero(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS.union({'plus(a,c)=a'}), print_as_proof_forms)
    step1 = prover.add_assumption('plus(a,c)=a')
    step2 = prover.add_assumption('plus(0,x)=x')
    step3 = prover.add_ug('Ax[plus(0,x)=x]', step2)
    step4 = prover.add_universal_instantiation('plus(0,a)=a', step3, 'a')
    step5 = prover.add_flipped_equality('a=plus(0,a)', step4)
    step6 = prover.add_chained_equality('plus(a,c)=plus(0,a)', [step1, step5])
    step7 = prover.add_substituted_equality(Formula.parse('plus(minus(a),plus(a,c))=plus(minus(a),plus(0,a))'), step6, Term.parse('plus(minus(a),_)'))
    step8 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')

    inst_map = {'x': Term.parse('minus(a)'), 'y': 'a', 'z': 'c'}
    step9 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))', step8, inst_map)
    inst_map = {'x': Term.parse('minus(a)'), 'y': 'a', 'z': '0'}

    step10 = prover.add_assumption('plus(minus(x),x)=0')
    step11 = prover.add_free_instantiation('plus(minus(a),a)=0', step10, {'x':'a'})
    inst_map = {'R': Formula.parse('plus(plus(minus(a),a),0)=plus(_,0)'), 'c': Term.parse('plus(minus(a),a)'), 'd': Term('0')}

    step12 = prover.add_assumption('plus(0,x)=x')

    inst_map = {'R': Formula.parse('plus(plus(minus(a),a),c)=plus(_,c)'), 'c': Term.parse('plus(minus(a),a)'), 'd': Term('0')}
    step13 = prover.add_instantiated_assumption(Prover.ME.instantiate(inst_map), Prover.ME, inst_map)
    step14 = prover.add_mp('(plus(plus(minus(a),a),c)=plus(plus(minus(a),a),c)->plus(plus(minus(a),a),c)=plus(0,c))', step11, step13)
    step15 = prover.add_instantiated_assumption('plus(plus(minus(a),a),c)=plus(plus(minus(a),a),c)', Prover.RX, {'c': Term.parse('plus(plus(minus(a),a),c)')})
    step16 = prover.add_mp('plus(plus(minus(a),a),c)=plus(0,c)', step15, step14)
    step17 = prover.add_free_instantiation('plus(0,c)=c', step12, {'x':'c'})

    inst_map = {'R': Formula.parse('plus(minus(a),plus(0,a))=plus(minus(a),_)'), 'c': Term.parse('plus(0,a)'), 'd': Term('a')}
    step18 = prover.add_instantiated_assumption(Prover.ME.instantiate(inst_map), Prover.ME, inst_map)
    step19 = prover.add_mp('(plus(minus(a),plus(0,a))=plus(minus(a),plus(0,a))->plus(minus(a),plus(0,a))=plus(minus(a),a))', step4, step18)
    step20 = prover.add_instantiated_assumption(Prover.RX.instantiate({'c':Term.parse('plus(minus(a),plus(0,a))')}), Prover.RX, {'c':'plus(minus(a),plus(0,a))'})
    step21 = prover.add_mp('plus(minus(a),plus(0,a))=plus(minus(a),a)', step20, step19)
    step22 = prover.add_flipped_equality('plus(0,c)=plus(plus(minus(a),a),c)', step16)
    step23 = prover.add_flipped_equality('c=plus(0,c)', step17)
    step24 = prover.add_chained_equality('c=0', [step23, step22, step9, step7, step21, step11])
    return prover.qed()
    # Task 10.10

#: The six field axioms
FIELD_AXIOMS = frozenset(GROUP_AXIOMS.union(
    {'plus(x,y)=plus(y,x)', 'times(x,1)=x', 'times(x,y)=times(y,x)',
     'times(times(x,y),z)=times(x,times(y,z))', '(~x=0->Ey[times(y,x)=1])',
     'times(x,plus(y,z))=plus(times(x,y),times(x,z))'}))

def prove_field_zero_multiplication(print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)
    # add assumptions
    step1_1 = prover.add_assumption('plus(0,x)=x')
    step1_2 = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')
    step1_3 = prover.add_assumption('plus(minus(x),x)=0')
    step1_4 = prover.add_assumption('plus(x,y)=plus(y,x)')
    step1_5 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    step1_6 = prover.add_assumption('times(x,y)=times(y,x)')

    # 0+0=0 ; plus(0,0)=0 - free instantiation of axiom 3
    step2 = prover.add_free_instantiation('plus(0,0)=0', step1_1, {'x':'0'})

    # x*0=x*(0+0) ; times(x,0)=times(x,plus(0,0)) - ME
    step3_1 = prover.add_flipped_equality('0=plus(0,0)', step2)
    inst_map = {'R': Formula.parse('times(x,0)=times(x,_)'), 'c': Term.parse('0'), 'd': Term.parse('plus(0,0)')}
    step3_2 = prover.add_instantiated_assumption(Prover.ME.instantiate(inst_map), Prover.ME, inst_map)
    step3_3 = prover.add_mp(prover._lines[step3_2].formula.second, step3_1, step3_2)
    step3_4 = prover.add_instantiated_assumption('times(x,0)=times(x,0)', Prover.RX, {'c': 'times(x,0)'})
    step3_5 = prover.add_mp(prover._lines[step3_3].formula.second, step3_4, step3_3)

    # x*(0+0)=(x*0)+(x*0) ; times(x,plus(0,0))=plus(times(x,0),times(x,0)) - free instantiation of axiom 6
    step4 = prover.add_free_instantiation('times(x,plus(0,0))=plus(times(x,0),times(x,0))', step1_2, {'y':'0', 'z':'0'})

    # x*0=(x*0)+(x*0) ; times(x,0)=plus(times(x,0),times(x,0)) - chain from the previous two
    step5_1 = prover.add_chained_equality('times(x,0)=plus(times(x,0),times(x,0))', [step3_5, step4])

    # -(x*0)+((x*0)+(x*0))=-(x*0)+(x*0) ; ME with c=(x*0)+(x*0), d=x*0, R='-(x*0)+_=-(x*0)+(x*0)'
    inst_map = {'R': Formula.parse('plus(minus(times(x,0)),_)=plus(minus(times(x,0)),times(x,0))'), 'c': Term.parse('times(x,0)'), 'd': Term.parse('plus(times(x,0),times(x,0))')}
    step6_1 = prover.add_instantiated_assumption(Prover.ME.instantiate(inst_map), Prover.ME, inst_map)
    step6_2 = prover.add_mp(prover._lines[step6_1].formula.second, step5_1, step6_1)
    step6_3 = prover.add_instantiated_assumption('plus(minus(times(x,0)),times(x,0))=plus(minus(times(x,0)),times(x,0))', Prover.RX, {'c': 'plus(minus(times(x,0)),times(x,0))'})
    step6_4 = prover.add_mp(prover._lines[step6_2].formula.second, step6_3, step6_2)

    # -(x*0)+(x*0)=0 ; free instantiation of axiom 2
    step7 = prover.add_free_instantiation('plus(minus(times(x,0)),times(x,0))=0', step1_3, {'x':'times(x,0)'})
    step7_1 = prover.add_flipped_equality('0=plus(minus(times(x,0)),times(x,0))', step7)

    # (-(x*0)+(x*0))+(x*0)=0
    step8 = prover.add_chained_equality('plus(minus(times(x,0)),plus(times(x,0),times(x,0)))=0' , [step6_4,step7])

    # 0+(x*0)=(-(x*0)+(x*0))+(x*0)
    inst_map = {'R': Formula.parse('plus(0,times(x,0))=plus(_,times(x,0))'), 'c': Term.parse('0'), 'd': Term.parse('plus(minus(times(x,0)),times(x,0))')}
    step9_1 = prover.add_instantiated_assumption(Prover.ME.instantiate(inst_map), Prover.ME, inst_map)
    step9_2 = prover.add_mp(prover._lines[step9_1].formula.second, step7_1, step9_1)
    step9_3 = prover.add_instantiated_assumption('plus(0,times(x,0))=plus(0,times(x,0))', Prover.RX, {'c': 'plus(0,times(x,0))'})
    step9_4 = prover.add_mp(prover._lines[step9_2].formula.second, step9_3, step9_2)

    # x=plus(x,0) from x=plus(0,x)
    step10_1 = prover.add_flipped_equality('x=plus(0,x)', step1_1)
    step10_2 = prover.add_free_instantiation('plus(0,x)=plus(x,0)', step1_4, {'x': '0', 'y': 'x'})
    step10_3 = prover.add_chained_equality('x=plus(x,0)', [step10_1, step10_2])

    # x*0=(x*0)+0 ; times(x,0)=plus(times(x,0),0)
    step11_1 = prover.add_free_instantiation('times(x,0)=plus(times(x,0),0)', step10_3, {'x': Term.parse('times(x,0)')})

    step12 = prover.add_free_instantiation('plus(times(x,0),0)=plus(0,times(x,0))', step1_4, {'x': 'times(x,0)', 'y': '0'})

    step13 = prover.add_free_instantiation('plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(minus(times(x,0)),plus(times(x,0),times(x,0)))', step1_5, {'x': 'minus(times(x,0))', 'y': 'times(x,0)', 'z': 'times(x,0)'})

    # times(0,x) = times(x,0)
    step14 = prover.add_free_instantiation('times(0,x)=times(x,0)', step1_6, {'x': '0', 'y': 'x'})

    prover.add_chained_equality('times(0,x)=0', [step14, step11_1, step12, step9_4, step13, step8])
    return prover.qed()
    # Task 10.11

#: Axiom schema of induction
INDUCTION_AXIOM = Schema(
    Formula.parse('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])'), {'R'})
#: The seven axioms of Peano arithmetic
PEANO_AXIOMS = frozenset({'(s(x)=s(y)->x=y)', '~s(x)=0', 'plus(x,0)=x',
                          'plus(x,s(y))=s(plus(x,y))', 'times(x,0)=0',
                          'times(x,s(y))=plus(times(x,y),x)', INDUCTION_AXIOM})

def prove_peano_left_neutral(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)

    # prove (plus(0,x)=x->s(plus(0,x))=s(x))
    inst_map = {'R': Formula.parse('s(plus(0,x))=s(_)'), 'c': Term.parse('plus(0,x)'), 'd': Term.parse('x')}
    step1 = prover.add_instantiated_assumption(Prover.ME.instantiate(inst_map), Prover.ME, inst_map)
    step2 = prover.add_instantiated_assumption('s(plus(0,x))=s(plus(0,x))', Prover.RX, {'c':'s(plus(0,x))'})
    taut = Formula.from_propositional_skeleton(PropositionalFormula.parse('(q->(p->q))'), {'p':Formula.parse('plus(0,x)=x'), 'q':Formula.parse('s(plus(0,x))=s(plus(0,x))')})
    step3 = prover.add_tautology(taut)
    step4 = prover.add_mp(prover._lines[step3].formula.second, step2, step3)
    taut = Formula.from_propositional_skeleton(PropositionalFormula.parse('((p->(q->r))->((p->q)->(p->r)))'), {'p':Formula.parse('plus(0,x)=x'), 'q':Formula.parse('s(plus(0,x))=s(plus(0,x))'), 'r':Formula.parse('s(plus(0,x))=s(x)')})
    step5 = prover.add_tautology(taut)
    step6 = prover.add_mp(prover._lines[step5].formula.second, step1, step5)
    step7 = prover.add_mp(prover._lines[step6].formula.second, step4, step6)

    # prove (plus(0,x)=x->plus(0,s(x))=s(x))
    step8 = prover.add_assumption('plus(x,s(y))=s(plus(x,y))')
    step9 = prover.add_free_instantiation('plus(0,s(x))=s(plus(0,x))', step8, {'x': '0', 'y': 'x'})         #this or step10 will be q for the next tautology
    step10 = prover.add_flipped_equality('s(plus(0,x))=plus(0,s(x))', step9)

    inst_map = {'R': Formula.parse('plus(0,s(x))=_'), 'c': Term.parse('s(plus(0,x))'), 'd': Term.parse('s(x)')}
    step10 = prover.add_instantiated_assumption(Prover.ME.instantiate(inst_map), Prover.ME, inst_map)

    taut = PropositionalFormula.parse('((p->(q->r))->(q->(p->r)))')
    inst_map = {'p': Formula.parse('s(plus(0,x))=s(x)'), 'q': Formula.parse('plus(0,s(x))=s(plus(0,x))'), 'r': Formula.parse('plus(0,s(x))=s(x)')}
    step11 = prover.add_tautology(Formula.from_propositional_skeleton(taut,inst_map))
    step12 = prover.add_mp(prover._lines[step11].formula.second, step10, step11)
    step13 = prover.add_mp(prover._lines[step12].formula.second, step9, step12)

    taut= PropositionalFormula.parse('((p->q)->((q->r)->(p->r)))')
    inst_map = {'p': Formula.parse('plus(0,x)=x'), 'q': Formula.parse('s(plus(0,x))=s(x)'), 'r': Formula.parse('plus(0,s(x))=s(x)')}
    step14 = prover.add_tautology(Formula.from_propositional_skeleton(taut, inst_map))
    step15 = prover.add_mp(prover._lines[step14].formula.second, step7, step14)
    step16 = prover.add_mp(prover._lines[step15].formula.second, step13, step15)

    #end game
    step17 = prover.add_assumption('plus(x,0)=x')
    step18 = prover.add_free_instantiation('plus(0,0)=0', step17, {'x':'0'})
    step19 = prover.add_ug(Formula('A','x', prover._lines[step16].formula), step16)
    step20 = prover.add_and_introduction(step18, step19)
    inst_map = {'R': Formula.parse('plus(0,_)=_')}
    step21 = prover.add_instantiated_assumption(INDUCTION_AXIOM.instantiate(inst_map), INDUCTION_AXIOM, inst_map)
    step22 = prover.add_mp('Ax[plus(0,x)=x]', step20, step21)
    step23 = prover.add_universal_instantiation('plus(0,x)=x', step22, 'x')
    return prover.qed()
    # Task 10.12

#: Axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]'), {'R'})

def prove_russell_paradox(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)
    COMPREHENSION_AXIOM.instantiate({'R': Formula.parse('~In(_,_)')})
    step1 = prover.add_instantiated_assumption(COMPREHENSION_AXIOM.instantiate({'R': Formula.parse('~In(_,_)')}), COMPREHENSION_AXIOM, {'R': Formula.parse('~In(_,_)')})
    inst_map = {'R': Formula.parse('((In(_,y)->~In(_,_))&(~In(_,_)->In(_,y)))]'), 
                'c': Term.parse('y'), 
                'x': 'x'}
    step2 = prover.add_instantiated_assumption(Prover.UI.instantiate(inst_map), Prover.UI, inst_map)
    step3 = prover.add_tautology('(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(P()&~P()))')
    step4 = prover.add_tautological_implication('(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->((z=z&~z=z)&(Hegel()->Sux(balls))))', {step2, step3})
    step5 = prover.add_existential_derivation('((z=z&~z=z)&(Hegel()->Sux(balls)))', step1, step4)
    step6 = prover.add_tautological_implication('(Hegel()->Sux(balls))', {step5})
    step7 = prover.add_tautological_implication('(z=z&~z=z)', {step5})
    return prover.qed()
    # Task 10.13

def _prove_not_exists_not_implies_all(variable: str, formula: Formula,
                                      print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    '(~E`variable`[~`formula`]->A`variable`[`formula`])'.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    if isinstance(formula, str):
        formula = Formula.parse(formula)
    not_exists_not_schema = Schema(Formula('~',Formula('E',variable,Formula('~',formula))))

    prover = Prover({not_exists_not_schema},False)
    inst_map = {'R': Formula('~',formula.substitute({variable: Term('_')})), 'c': Term(variable), 'x': variable}
    step1 = prover.add_instantiated_assumption(Prover.EI.instantiate(inst_map), Prover.EI, inst_map)
    step2 = prover.add_assumption(not_exists_not_schema.formula)
    step3 = prover.add_tautological_implication(formula, {step1, step2})
    step4 = prover.add_ug(Formula('A', variable, formula), step3)
    return remove_assumption(prover.qed(), not_exists_not_schema.formula, print_as_proof_forms)
    # Optional Task 11.4a

def _prove_exists_not_implies_not_all(variable: str, formula: Formula,
                                      print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    `'(E`variable`[~`formula`]->~A`variable`[`formula`])'`.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    if isinstance(formula, str):
        formula = Formula.parse(formula)
    exists_not_schema = Schema(Formula('E', variable, Formula('~', formula)))
    
    prover = Prover({exists_not_schema}, False)
    step1 = prover.add_assumption(exists_not_schema.formula)
    inst_map = {'R': formula.substitute({variable: Term('_')}), 'c': Term(variable), 'x': variable}
    step2 = prover.add_instantiated_assumption(Prover.UI.instantiate(inst_map), Prover.UI, inst_map)
    step3 = prover.add_tautological_implication(Formula('->', Formula('~', formula), Formula('~', Formula('A', variable, formula))), {step2})
    step4 = prover.add_ug(Formula('A', variable, prover._lines[step3].formula), step3)
    inst_map = {'Q': Formula('~', Formula('A', variable, formula)), 'R': Formula('~', formula).substitute({variable: Term('_')}), 'x': variable}
    step5 = prover.add_instantiated_assumption(Prover.ES.instantiate(inst_map), Prover.ES, inst_map)
    step6 = prover.add_tautological_implication(Formula('~', Formula('A', variable, formula)), {step1, step4, step5})
    return remove_assumption(prover.qed(), exists_not_schema.formula, print_as_proof_forms)
    # Optional Task 11.4b

def prove_not_all_iff_exists_not(variable: str, formula: Formula,
                                 print_as_proof_forms: bool = False) -> Proof:
    """Proves that
    `equivalence_of`('(~A`variable`[`formula`]', 'E`variable`[~`formula`]')`.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    import predicates.prenex
    assert is_variable(variable)
    prover = Prover({})
    proof1 = _prove_not_exists_not_implies_all(variable, formula)
    step1 = prover.add_proof(proof1.conclusion, proof1)
    proof2 = _prove_exists_not_implies_not_all(variable, formula)
    step2 = prover.add_proof(proof2.conclusion, proof2)
    conclusion = predicates.prenex.equivalence_of(
                    Formula('~', Formula('A', variable, formula)),
                    Formula('E', variable, Formula('~', formula)))
    step3 = prover.add_tautological_implication(conclusion, {step1, step2})
    return prover.qed()
    # Optional Task 11.4c

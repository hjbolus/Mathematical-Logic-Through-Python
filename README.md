Read the official documentation here: https://www.logicthrupython.org/api/.

This textbook provides code skeletons for functions that, when implemented, automate tasks in formal logic. I worked on them over the last year, and the result is essentially a Python package for classical first order and propositional logic. This repository is the first (and only, as of July 2024) set of solutions available. I have added some utilities without changing the existing ones, so everything in the documentation above is accurate.

# First order logic
## Formulas
  Formulas are stored as objects of class `Formula`, which are composed of operators, subformulas, and terms (`Term` objects) in an expression tree or directed-acyclic graph. Terms are either constants, variables, or functions. Terms and formulas can be parsed from strings into objects of their respective type using the `parse()` methods of their respective classes. For example,

`In [1]: formula = Formula.parse('Ax[(Man(x)->Mortal(x))]')`  

`In [2]: print(f'{formula} is composed of the quantifier {formula.root}, bound variable {formula.variable}, and statement {formula.statement}. The statement is composed of subformulas {formula.statement.first} and {formula.statement.second}, with the operator {formula.statement.root}')`  

`Out [2]: Ax[(Man(x)->Mortal(x))] is composed of the quantifier A, bound variable x, and statement (Man(x)->Mortal(x)). The statement is composed of subformulas Man(x) and Mortal(x), with the operator ->`  

## Models
Models are stored as `Model` objects, based on the notion of set-theoretic structures. They are initialized with arguments `universe`, `constant_interpretations`, `relation_interpretations`, and `function_interpretations`. The `evaluate_term` and `evaluate_formula` methods of class `Model` return the constant interpretation or truth value, respectively, of a term or formula in the given model. Given a set of formulas, the method `is_model_of()` of class `Model` determines whether or not all of the formulas evaluate to true in the given model. 

Although functions and equality are allowed by default, the file `functions.py` includes functions that eliminate the use of functions and/or equality from models and formulas by replacing them with equivalent relations and relation interpretations.

## Axioms, schemas, and assumptions
  Axioms, axiom schemas, and assumptions are implemented as `Schema` objects, which include a formula and a set of templates indicating which terms and relations may be instantiated with other values. The following schema expresses the substitutability of equals, and can be instantiated as follows (I added a parsing method to the class `Schema` to allow copying and pasting from displayed objects):
  
`In [3]: schema = Schema.parse('Schema: (c=d->(R(c)->R(d))) [templates: R, c, d]')`  

`In [4]: schema.instantiate({'R': Formula.parse('_=z'), 'c': Term('x'), 'd': Term('y')})`  

`Out [4]: (x=y->(x=z->y=z))`  

## Proofs
  Proofs are stored as `Proof` objects, and are composed of a set of assumptions (`Schema` objects), an ordered sequence of lines each of which contains a formula and justification, and a conclusion which is stated both at the outset and as the last line of the proof. The following short proof shows how this data structure is represented:

`In [5]: proof = prove_syllogism() # a proof stored in a function (for nefarious reasons)`  

`In [6]: proof`  

`Out [6]: Proof of Mortal(aristotle) from assumptions/axioms:`  
`  Schema: Ax[(Man(x)->Mortal(x))] [templates: none]`  
`  Schema: Man(aristotle) [templates: none]`  
`  ...`  
`  Schema: ((Ax[(R(x)->Q())]&Ex[R(x)])->Q()) [templates: Q, R, x]`  
`Lines:`  
`  0) Ax[(Man(x)->Mortal(x))]    (Assumption Schema: Ax[(Man(x)->Mortal(x))] [templates: none] instantiated with {})`  
`  1) (Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))    (Assumption Schema: (Ax[R(x)]->R(c)) [templates: R, c, x] instantiated with {'R': (Man(_)->Mortal(_)), 'c': aristotle})`  
`  2) (Man(aristotle)->Mortal(aristotle))    (MP from lines 0 and 1)`  
`  3) Man(aristotle)    (Assumption Schema: Man(aristotle) [templates: none] instantiated with {})`  
`  4) Mortal(aristotle)    (MP from lines 3 and 2)`  
`QED`  

  The package can check the validity of the proof:

`In [7]: proof.is_valid()`  

`Out [7]: True`  

  And it can perform certain transformations on `Proof` objects, such as removing an assumption, or converting a proof from assumption P of a contradiction into a proof of ~P, without assumption P. For example:

`In [8]: remove_assumption(proof, formula)`  

`Out [8]: Proof of (Ax[(Man(x)->Mortal(x))]->Mortal(aristotle)) from assumptions/axioms:`  
`  Schema: Man(aristotle) [templates: none]`  
`  ...`  
`  Schema: c=c [templates: c]`  
`Lines:`  
`  0) (Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))    (Assumption Schema: (Ax[R(x)]->R(c)) [templates: R, c, x] instantiated with {'R': (Man(_)->Mortal(_)), 'c': aristotle})`  
`  ...`  
`  6) (Ax[(Man(x)->Mortal(x))]->Mortal(aristotle))    (MP from lines 3 and 5)`  
`QED`  

Moreover, any formula can be converted to prenex normal form using the function `to_prenex_normal_form()`, which returns a a prenex equivalent as well as a proof of the equivalence. In the process, if any quantifiers share variable names, then they will all be replaced with unique ones, leading to unfortunate names like `z15`. For example:

`In [9]: formula, proof = to_prenex_normal_form(Formula.parse('~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])'))`  

`In [10]: formula`  

`Out [10]: Ez1[Az2[Ez14[Az15[~~(~R(z1,z2)&~z14=z15)]]]]`  

`In [11]: proof`  

`Out [11]: Proof of ((~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])->Ez1[Az2[Ez14[Az15[~~(~R(z1,z2)&~z14=z15)]]]])&`  
`(Ez1[Az2[Ez14[Az15[~~(~R(z1,z2)&~z14=z15)]]]]->~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]]))) from assumptions/axioms:`  
`  Schema: (Ax[R(x)]->R(c)) [templates: R, c, x]`  
`  ...`  
`Lines:`  
`  0) (((R(x,y)->R(x,y))&(R(x,y)->R(x,y)))->((Ey[R(x,y)]->Ez2[R(x,z2)])&(Ez2[R(x,z2)]->Ey[R(x,y)])))    (Assumption Schema: (((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)]))) [templates: Q, R, x, y] instantiated with {'R': R(x,_), 'Q': R(x,_), 'x': 'y', 'y': 'z2'})`  
`  ...`  
`  114) ((~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])->Ez1[Az2[Ez14[Az15[~~(~R(z1,z2)&~z14=z15)]]]])&`  
`(Ez1[Az2[Ez14[Az15[~~(~R(z1,z2)&~z14=z15)]]]]->~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])))    (MP from lines 111 and 113)`  
`QED`  

Any FOL tautology can be proven using the function prove_tautology(). Under the hood, this relies on converting the FOL formula to a propositional formula and proving the corresponding propositional tautology.

Given a set of closed prenex normal form sentences, the function model_or_inconsistency() will return a model if they are satisfiable or else a proof that they are not. Other functions from the file completeness.py can be used to existentially and universally close a given set of unclosed prenex normal form sentences.

Duplicated and unnecessary lines can be removed from proofs using the `clean()` method that I added, without changing the validity of the proof. A similar method of the same name is also available for propositional proofs, described below.

## Prover objects
It also includes an interface through objects of class `Prover` that assist the construction of FOL proofs by providing convenient methods for adding multiple lines in one line of code. These check for validity at each step, and allow for powerful techniques like chaining equalities and tautological implications of any size. For example, say `prover` is a `Prover` object containing a proof, for which line 7 contains the formula `a=b`, line 3 contains the formula `b=f(b)`, and line 9 contains the formula `f(b)=0`. Then `prover.add_chained_equality('a=0', [7,3,9])` adds a valid series of lines to the proof, ending with a line containing the formula `a=0`.

FOL proofs are allowed to introduce any tautology on a new line, with 'tautology' defined as a formula whose propositional skeleton is a propositional logic tautology. This is justified by the implementation of the Tautology Theorem for propositional logic, which provides a method to prove any propositional tautology.

You can inline proofs using `Prover` objects by using the method `add_proof(proof.conclusion, proof)` of class `Prover`. This automatically adjusts line numbers so that the proof remains valid.

## Additions
Of note, I added a file called `Operators.py`, with functions that translate a formula that uses one set of operators to one that uses a different set. This is similar to the file `Operators.py` in Propositions, with the addition that it is used to allow representation of FOL formulae in Fregean notation by first translating operators to ~ and ->.

`In [12]: formula = Formula.parse('(R(x,y)|R(y,x))')`  

`In [13]: Operators.to_implies_not(formula)`  

`Out [13]: (~R(x,y)->R(y,x))`   

`In [14]: formula = Formula.parse('Ax[Ey[((P(x,y)&Q(y))->R(x))]]')`  

`In [15]: Operators.frege(formula)`  

`Out [15]: ├──x─┬y┬─┬─────── R(x)`  
`                   └─┬─┬─┬─ Q(y)`  
`                       └─── P(x,y)`  

# Propositional logic
The section on propositional logic includes many similar classes, methods, and functions. The major difference is that any proof from a certain set of axioms can be generated automatically using functions described below. The automated proof strategies rely on Modus Ponens being the only inference rule that requires assumptions; others are written as assumptionless inference rules (such as `[] ==> '~F'`), meaning they can be introduced on any lines. The most notable features are described below.

## Syntax
Formulas are be represented in traditional infix notation by default, but can be translated to Polish notation using the method `polish()` of class `Formula` or can be displayed in Fregean notation using the method `frege()`, which I added. For example:

`In [1]: Formula.parse('(p->q)').frege()`  

`Out [1]: `  
`├──┬─ q`  
`   └─ p`  

`In [2]: Formula.parse('((~p->q)->~(p->~q))').frege()`  

`Out [2]:`  
`├──┬─┬─┬─┬─ q`  
`   │   └─── p`  
`   └───┬─── q`  
`       └─┬─ p`  

## Semantics
Given any set of constant names, the function `all_models()` returns (a generator yielding) all possible truth-value assignments.

`In [1]: list(all_models(('p', 'q')))`  

`Out [1]: [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]`   

By evaluating a given formula over all models, functions implemented in the file `semantics.py` can perform tasks like determining if a given formula is a contradiction, tautology, or satisfiable; or determine if an inference rule is sound. The function `print_truth_table()` prints a truth table for any formula.

`In [2]: formula = Formula.parse('~(q&p)')`  

`In [3]: print_truth_table(formula)`  

`Out[3]: `  
| p | q | ~(q&p) |
|---|----|---------|
| F | F  | T       |
| F | T  | T       |
| T | F  | T       |
| T | T  | F       |

It can also go the other direction, by synthesizing a formula in CNF or DNF to capture a particular model or set of models, using the functions `synthesize()` or `synthesize_cnf()`, respectively.

## Automated proofs
Given a formula and a model, if the formula evaluates to `True` in the model, `prove_in_model_full(formula, model)` returns a valid proof of the formula. If the formula evalutes to `False` in the model, it returns a valid proof of its negation.

`In [4]: formula = Formula.parse('(p->q)')`  

`In [5]: model = {'p': True, 'q': False}`  

`In [6]: prove_in_model_full(formula, model)`  

`Out [6]: Proof of ['p', '~q'] ==> '~(p->q)' via inference rules:`  
`  [] ==> '~F'`  
`  ...`  
`  [] ==> '((~q->~p)->(p->q))'`  
`Lines:`  
`  0) p`  
`  1) ~q`  
`  2) (p->(~q->~(p->q)))    (Inference Rule [] ==> '(p->(~q->~(p->q)))')`  
`  3) (~q->~(p->q))    (Inference Rule ['p', '(p->q)'] ==> 'q' on lines 0,2)`  
`  4) ~(p->q)    (Inference Rule ['p', '(p->q)'] ==> 'q' on lines 1,3)`  
`QED`  

Similarly, given any tautology `tautology`, the function `prove_tautology_full(tautology)` returns a valid proof of the tautology, generated by first proving the formula in all models, then combining those proofs and removing the assumptions unique to their models.

If a formula `formula` is a tautology, the function `proof_or_counterexample_full(formula)` returns a valid proof of it; otherwise it returns a model in which `formula` evaluates to `False`.

If a formula `formula` is a contradiction, the function `model_or_inconsistency_full(formula)` returns a proof of a contradiction derived by assuming `formula`; otherwise it returns a model in which it evaluates to `True`.

In order to evaluate if an FOL formula is a tautology, functions for predicate logic convert the formula to a propositional skeleton and take advantage of methods from propositional logic.

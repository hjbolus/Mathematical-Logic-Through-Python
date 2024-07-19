Read the official documentation here: https://www.logicthrupython.org/api/
I have added some utilities without changing the existing ones, so everything there should be accurate.

The Python package that results from the completed code automates a variety of tasks in classical first order logic as well as propositional logic. 

# First order logic
### Formulas
  In first order logic, Formulas are stored as objects of class Formula, which are composed of subformulas and terms (Term objects) in an expression tree or directed-acyclic graph structure. Term objects are either constants, variables, or functions. Terms and formula can be parsed from strings into objects of their respective type using the .parse() methods of their classes. For example,

`>>> formula = Formula.parse('Ax[(Man(x)->Mortal(x))]')`
`Ax[(Man(x)->Mortal(x))]`
`>>> print(f'\n{formula} is composed of the quantifier {formula.root}, bound variable {formula.variable}, and statement {formula.statement}. The statement is composed of subformulas {formula.statement.first} and {formula.statement.second}, with the operator {formula.statement.root}')
Ax[(Man(x)->Mortal(x))] is composed of the quantifier A, bound variable x, and statement (Man(x)->Mortal(x)). The statement is composed of subformulas Man(x) and Mortal(x), with the operator ->`

### Axioms and schemas
  Axioms are implemented as Schema objects, which include a Formula and a set of templates indicating which terms and relations may be instantiated with other values. The following schema expresses the substitutability of equals, and can be instantiated as follows (I added a parsing method to the class Schema to allow copying and pasting from displayed objects):
  
`>>> schema = Schema.parse('Schema: (c=d->(R(c)->R(d))) [templates: R, c, d]')`
`>>> schema.instantiate({'R': Formula.parse('_=z'), 'c': Term('x'), 'd': Term('y')})`
`(x=y->(x=z->y=z))`

### Proofs
  Proofs are stored as Proof objects, and are composed of a set of assumptions (Schema objects), an ordered sequence of lines each of which contains a formula and justification, and a conclusion which is stated both at the outset and as the last line of the proof. The following short proof shows how this data structure is represented:

`>>> proof = prove_syllogism()`
`>>> proof`
`Proof of Mortal(aristotle) from assumptions/axioms:`
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

  Moreover, the package can check the validity of the proof:

`>>> proof.is_valid()
True`

  And it can perform certain transformations on Proof objects, such as removing an assumption, or converting a proof from assumption P of a contradiction into a proof of ~P, without assumption P. For example:
`
>>> remove_assumption(proof, formula)
Proof of (Man(aristotle)->Mortal(aristotle)) from assumptions/axioms:
  Schema: Ax[(Man(x)->Mortal(x))] [templates: none]
  ...
  Schema: (Ax[R(x)]->R(c)) [templates: R, c, x]
Lines:
  0) Ax[(Man(x)->Mortal(x))]    (Assumption Schema: Ax[(Man(x)->Mortal(x))] [templates: none] instantiated with {})
  ...
  12) (Man(aristotle)->Mortal(aristotle))    (MP from lines 9 and 11)
QED`

It also includes an interface through objects of class Prover that assist the construction of FOL proofs by providing convenient methods for adding multiple lines in one line of code. 

Moreover, any formula can be converted to prenex normal form using the function to_prenex_normal_form(), which returns a a prenex equivalent as well as a proof of the equivalence. For example:

`>>> formula, proof = to_prenex_normal_form(Formula.parse('~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])'))
>>> formula
Ez3884[Az3885[Ez3897[Az3898[~~(~R(z3884,z3885)&~z3897=z3898)]]]]
>>> proof
Proof of ((~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])->Ez3884[Az3885[Ez3897[Az3898[~~(~R(z3884,z3885)&~z3897=z3898)]]]])&(Ez3884[Az3885[Ez3897[Az3898[~~(~R(z3884,z3885)&~z3897=z3898)]]]]->~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]]))) from assumptions/axioms:
  Schema: (Ax[R(x)]->R(c)) [templates: R, c, x]
  ...
Lines:
  0) (((R(x,y)->R(x,y))&(R(x,y)->R(x,y)))->((Ey[R(x,y)]->Ez3292[R(x,z3292)])&(Ez3292[R(x,z3292)]->Ey[R(x,y)])))    (Assumption Schema: (((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)]))) [templates: Q, R, x, y] instantiated with {'R': R(x,_), 'Q': R(x,_), 'x': 'y', 'y': 'z3292'})
  ...
  114) ((~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])->Ez3291[Az3292[Ez3304[Az3305[~~(~R(z3291,z3292)&~z3304=z3305)]]]])&(Ez3291[Az3292[Ez3304[Az3305[~~(~R(z3291,z3292)&~z3304=z3305)]]]]->~~(~Ax[Ey[R(x,y)]]&~Ax[Ey[x=y]])))    (MP from lines 111 and 113)
`


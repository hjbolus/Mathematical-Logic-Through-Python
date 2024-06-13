This short project is inspired by avbop's "Syllogisms" repository, my implementation of propositional 
and predicate logic, and a paper titled "The four essential Aristotelian syllogisms, via substitution
and symmetry" by Vaughn R. Pratt: http://boole.stanford.edu/pub/nemhaj.pdf.

avbop's "Syllogisms" repository can be found here: https://github.com/avbop/syllogisms/tree/master. 
Their method correctly reduces 18/24 valid syllogisms, while this method correctly reduces 23/24.

Pratt points out that obversion, conversion, and contraposition can be used as edges to form two 
connected graphs of valid syllogisms, that this allows us to think of one syllogism as being 
"reduced" to another, and claims that this is the central desired property of a proof theory. Here I
implement his descriptions of obversion, conversion, and contraposition to check that all valid 
syllogisms eventually reduce to one of four chosen as end points, and that no invalid syllogisms do.
Interestingly, Calemes (AEE-4) does not, but this is because of early termination.

Moreover, this script can easily be adapted to check what subsets of syllogisms may be used as endpoints
to reduce any other set of syllogisms. Barbara, Barbari, and Ferio or Celarent are the smallest sets of 
first-figure end points found by this script which are sufficient to reduce all 24 valid moods by these 
rules. All first-figure sets found here which are sufficient to reduce these 24 include both Barbara and 
Barbari. There are at least 20 sets of two moods taken from any figure capable of serving as endpoints 
for the reduction of all 15 unconditional syllogisms, including Barbara + Ferio from the first figure.

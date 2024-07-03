class Proposition:
    first: str
    second: str
    terms: tuple
    copula: str

    def __init__(self, first: str, copula: str, second: str):
        self.first = first
        self.second = second
        self.terms = (first, second)
        assert copula in {'a','e', 'i', 'o'}, print(f'Invalid copula "{copula}"')
        self.copula = copula

    def __repr__(self):
        if self.copula == 'a':
            return f'Everything that is a(n) {self.first} is a(n) {self.second}'
        elif self.copula == 'e':
            return f'Nothing that is a(n) {self.first} is a(n) {self.second}'
        elif self.copula == 'i':
            return f'Some things that are a(n) {self.first} are a(n) {self.second}'
        else:
            return f'Not all things that are a(n) {self.first} are a(n) {self.second}'

    def __eq__(self, other):
        return isinstance(other, Proposition) and str(self) == str(other)

    def contrary(self):
        if self.copula == 'a':
            copula = 'e'
        elif self.copula == 'e':
            copula = 'a'
        elif self.copula == 'i':
            copula = 'o'
        else:
            copula = 'i'
        return Proposition(self.first, copula, self.second)

    def contradiction(self):
        if self.copula == 'a':
            copula = 'o'
        elif self.copula == 'e':
            copula = 'i'
        elif self.copula == 'i':
            copula = 'e'
        else:
            copula = 'a'
        return Proposition(self.first, copula, self.second)

    def subalternate(self):
        if self.copula == 'a':
            copula = 'i'
        elif self.copula == 'e':
            copula = 'o'
        elif self.copula == 'i':
            copula = 'a'
        else:
            copula = 'e'
        return Proposition(self.first, copula, self.second)

class Syllogism:
    major: Proposition
    minor: Proposition
    conclusion: Proposition
    subject: str
    predicate: str
    middle_term: str
    figure: str
    mood: str
    lines: list
    sm:int
    mp: int
    sp: int

    figure1 = {
    ('a', 'a', 'a'): 'Barbara',
    ('e', 'a', 'e'): 'Celarent',
    ('a', 'i', 'i'): 'Darii',
    ('e', 'i', 'o'): 'Ferio',
    ('a', 'a', 'i'): 'Barbari',
    ('e', 'a', 'o'): 'Celaront'}
    figure2 = {
    ('e', 'a', 'e'): 'Cesare',
    ('a', 'e', 'e'): 'Camestres',
    ('e', 'i', 'o'): 'Festino',
    ('a', 'o', 'o'): 'Baroco',
    ('e', 'a', 'o'): 'Cesaro',
    ('a', 'e', 'o'): 'Camestros'}
    figure3 = {
    ('a', 'i', 'i'): 'Datisi',
    ('i', 'a', 'i'): 'Disamis',
    ('e', 'i', 'o'): 'Ferison',
    ('o', 'a', 'o'): 'Bocardo',
    ('e', 'a', 'o'): 'Felapton',
    ('a', 'a', 'i'): 'Darapti'}
    figure4 = {
    ('a', 'e', 'e'): 'Calemes',
    ('i', 'a', 'i'): 'Dimatis',
    ('e', 'i', 'o'): 'Fresison',
    ('a', 'e', 'o'): 'Calemos',
    ('e', 'a', 'o'): 'Fesapo',
    ('a', 'a', 'i'): 'Bamalip'}

    moods = {'barbara': ('1', ('a', 'a', 'a')),
    'celarent': ('1', ('e', 'a', 'e')),
    'darii': ('1', ('a', 'i', 'i')),
    'ferio': ('1', ('e', 'i', 'o')),
    'barbari': ('1', ('a', 'a', 'i')),
    'celaront': ('1', ('e', 'a', 'o')),
    'cesare': ('2', ('e', 'a', 'e')),
    'camestres': ('2', ('a', 'e', 'e')),
    'festino': ('2', ('e', 'i', 'o')),
    'baroco': ('2', ('a', 'o', 'o')),
    'cesaro': ('2', ('e', 'a', 'o')),
    'camestros': ('2', ('a', 'e', 'o')),
    'datisi': ('3', ('a', 'i', 'i')),
    'disamis': ('3', ('i', 'a', 'i')),
    'ferison': ('3', ('e', 'i', 'o')),
    'bocardo': ('3', ('o', 'a', 'o')),
    'felapton': ('3', ('e', 'a', 'o')),
    'darapti': ('3', ('a', 'a', 'i')),
    'calemes': ('4', ('a', 'e', 'e')),
    'dimatis': ('4', ('i', 'a', 'i')),
    'fresison': ('4', ('e', 'i', 'o')),
    'calemos': ('4', ('a', 'e', 'o')),
    'fesapo': ('4', ('e', 'a', 'o')),
    'bamalip': ('4', ('a', 'a', 'i'))}

    def __init__(self, major: Proposition, minor: Proposition, conclusion=None):
        self.major = major
        self.minor = minor

        #determine figure
        if major.first == minor.second:
            self.figure = '1'
            self.subject = minor.first
            self.predicate = major.second
            self.middle_term = major.first
            self.sm = Syllogism.probabilities[minor.copula]
            self.mp = Syllogism.probabilities[major.copula]

        elif major.second == minor.second:
            self.figure = '2'
            self.subject = minor.first
            self.predicate = major.first
            self.middle_term = major.second
            self.sm = Syllogism.probabilities[minor.copula]
            self.mp = 0

        elif major.first == minor.first:
            self.figure = '3'
            self.subject = minor.second
            self.predicate = major.second
            self.middle_term = major.first
            self.sm = 0
            self.mp = Syllogism.probabilities[major.copula]
        else:
            self.figure = '4'
            self.subject = minor.second
            self.predicate = major.first
            self.middle_term = major.second
            self.sm = 0
            self.mp = 0
        self.sp = self.sm*self.mp

        if conclusion:
            self.conclusion = conclusion
        else:
            print('Pick a conclusion from the following:')
            for copula in ['a', 'e', 'i', 'o']:
                print(f'{copula}: {Proposition(self.subject, copula, self.predicate)}')
            copula = str(input())
            assert copula in {'a', 'e', 'i', 'o'}, print('invalid copula')
            self.conclusion = Proposition(self.subject, copula, self.predicate)
        
        self.lines = (self.major, self.minor, self.conclusion)
        
        #determine mood
        self.copulae = (self.major.copula, self.minor.copula, self.conclusion.copula)
        if self.figure == '1':
            if self.copulae in Syllogism.figure1:
                self.mood = Syllogism.figure1[self.copulae]
            else:
                self.mood = ''.join([self.figure, *[line.copula for line in self.lines]])
        elif self.figure == '2':
            if self.copulae in Syllogism.figure2:
                self.mood = Syllogism.figure2[self.copulae]
            else:
                self.mood = ''.join([self.figure, *[line.copula for line in self.lines]])
        elif self.figure == '3':
            if self.copulae in Syllogism.figure3:
                self.mood = Syllogism.figure3[self.copulae]
            else:
                self.mood = ''.join([self.figure, *[line.copula for line in self.lines]])
        elif self.figure == '4':
            if self.copulae in Syllogism.figure4:
                self.mood = Syllogism.figure4[self.copulae]
            else:
                self.mood = ''.join([self.figure, *[line.copula for line in self.lines]])

    def __repr__(self):
        return f"{self.major},\n{self.minor},\n\tTherefore,\n{self.conclusion}."

    def __eq__(self, other):
        if isinstance(other, Syllogism):
            return self.major == other.major and self.minor == other.minor and self.conclusion == other.conclusion
        return False

    def is_valid(self):
        if self.mood in Syllogism.moods:
            if self.figure == '1':
                return self.major.first == self.minor.second and self.major.second == self.conclusion.second and self.minor.first == self.conclusion.first
            elif self.figure == '2':
                return self.major.second == self.minor.second and self.major.first == self.conclusion.second and self.minor.first == self.conclusion.first
            elif self.figure == '3':
                return self.major.first == self.minor.first and self.major.second == self.conclusion.second and self.minor.second == self.conclusion.first
            else:
                return self.major.first == self.conclusion.second and self.major.second == self.minor.first and self.minor.second == self.conclusion.first
        return False

    def from_terms_figure_and_copulae(subject='S', middle_term='M', predicate='P', figure='1', copulae=('a','a','a')):
        assert figure in {'1','2','3','4'}
        assert len(copulae) == 3 and all(i in {'a','e','i','o'} for i in copulae)
        if figure == '1':
            major = Proposition(middle_term, copulae[0], predicate)
            minor = Proposition(subject, copulae[1], middle_term)

        elif figure == '2':
            major = Proposition(predicate, copulae[0], middle_term)
            minor = Proposition(subject, copulae[1], middle_term)

        elif figure == '3':
            major = Proposition(middle_term, copulae[0], predicate)
            minor = Proposition(middle_term, copulae[1], subject)

        else:
            major = Proposition(predicate, copulae[0], middle_term)
            minor = Proposition(middle_term, copulae[1], subject)

        conclusion = Proposition(subject, copulae[2], predicate)
        return Syllogism(major, minor, conclusion)

    def from_terms_and_mood(subject, middle_term, predicate, mood):
        assert mood.lower() in Syllogism.moods
        figure, copulae = Syllogism.moods[mood.lower()]
        return Syllogism.from_terms_figure_and_copulae(subject, middle_term, predicate, figure, copulae)

    def from_mood(mood):
        if mood.lower() in Syllogism.moods:
            figure, copulae = Syllogism.moods[mood.lower()]
        else:
            assert len(mood) == 4
            if mood[0].isnumeric():
                figure = mood[0]
                copulae = list(mood[1:])
            elif mood[-1].isnumeric():
                figure = mood[-1]
                copulae = list(mood[:-1])
        return Syllogism.from_terms_figure_and_copulae('S', 'M', 'P', figure, copulae)
    
    def to_propositional_logic(self):
        pass

    def to_predicate_logic(self):
        pass

    def contrapositions(self):
        conclusion = self.conclusion.contradiction()
        
        #major_contraposition
        major = self.major.contradiction()
        if major.second in self.minor.terms:
            major_contraposition = Syllogism(self.minor, conclusion, major)
        else:
            assert major.second in conclusion.terms
            major_contraposition = Syllogism(conclusion, self.minor, major)
        
        #minor_contraposition
        minor = self.minor.contradiction()
        if minor.second in self.major.terms:
            minor_contraposition = Syllogism(self.major, conclusion, minor)
        else:
            assert minor.second in self.conclusion.terms
            minor_contraposition = Syllogism(conclusion, self.major, minor)
        
        return major_contraposition, minor_contraposition
    
    def converse(self):
        new_lines = []
        for line in self.lines:
            if line.copula in {'e','i'}:
                new_lines.append(Proposition(line.second, line.copula, line.first))
            else:
                new_lines.append(line)
        return Syllogism(*new_lines)
    
    def obverse(self):
        if self.major.second == self.minor.second:
            major = self.major.contrary()
            minor = self.minor.contrary()
            return Syllogism(major, minor, conclusion)
        else:
            return self

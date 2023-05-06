(*<*)
theory "01_Introduction"
  imports
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter\<open>Snippets\<close>

section\<open>Earley\<close>

text\<open>
Context-free grammars have been used extensively for describing the syntax of programming languages
and natural languages. Parsing algorithms for context-free grammars consequently play a large role in
the implementation of compilers and interpreters for programming languages and of programs which understand
or translate natural languages. Numerous parsing algorithms have been developed. Some are general,
in the sense that they can handle all context-free grammars, while others can handle only subclasses of
grammars. The latter, restricted algorithms tend to be much more efficient The algorithm described here
seems to be the most efficient of the general algorithms, and also it can handle a larger class of grammars
in linear time than most of the restricted algorithms.

A language is a set of strings over a finite set of symbols. We call these terminal symbols and represent
them by lowercase letters: a, b, c. We use a context-free grammar as a formal device for specifying which
strings are in the set. This grammar uses another set of symbols, the nonterminals, which we can think of
as syntactic classes. We use capitals for nonterminals: A, B, C. String of either terminals or non-terminals
are represented by greek letters: alpha, beta, gamma. The empty string is epsilon. There is a finite set of
productions or rewriting rules of the form A -> alpha. The nonterminal which stands for sentence is called the
root R of the grammar. The productions with a particular nonterminal A on their left sides are called the
alternatives of A. We write alpha => beta if exists gamma, delta, ny, A such taht a = gamma A delta and
beta = gamma ny delta and A -> ny is a production. We write alpha =>* beta if exists alpha0, alpha1, ...
alpham (m > =0) such that alpha = alpha0 => alpha1 => ... => alpham = beta The sequence alphai is called a
derivation of beta from alpha. A sentential form is a string alpha such the the root R =>* alpha. A sentence
is a sentential form consisting entirely of terminal symbols. The language defined by a grammar L(G) is the
set of its sentences. We may represent any sentential form in at least one way as a derivation tree or parse
tree reflecting the steps made in deriving it. The degree of ambiguity of a sentence is the number of its
distinct derivation trees. A sentence is unambiguous if it has degree 1 of ambiguity. A grammar is unambiguous
if each of its sentences is unambiguous. A grammar is reduced if every nonterminal appears in some derivation
of some sentence. A recognizer is an algorithm which takes a input a string and either accepts or rejects it
depending on whether or not the string is a sentence of the grammer. A parser is a recogizer which also outputs
the set of all legal derivation trees for the string.
\<close>

section\<open>Scott\<close>

text\<open>
The Computer Science community has been able to automatically generate parsers for a very wide class of context
free languages. However, many parsers are still written manually, either using tool support or even completely
by hand. This is partly because in some application areas such as natural language processing and bioinformatics
we don not have the luxury of designing the language so that it is amendable to know parsing techniques, but also
it is clear that left to themselves computer language designers do not naturally write LR(1) grammars. A grammar
not only defines the syntax of a language, it is also the starting point for the definition of the semantics,
and the grammar which facilitates semantics definition is not usually the one which is LR(1). Given this difficulty
in constructing natural LR(1) grammars that support desired semantics, the general parsing techniques, such as
the CYK Younger \cite{Younger:1967}, Earley \cite{Earley:1970} and GLR Tomita \cite{Tomita:1985} algorithms, developed
for natural language processing are also of interest to the wider computer science community. When using grammars as
the starting point for semantics definition, we distinguish between recognizers which simply determine whether or not
a given string is in the language defined by a given grammar, and parserwhich also return some form of derivation
of the string, if one exists. In their basic form the CYK and Earley algorithms are recognizers while GLR-style
algorithms are designed with derivation tree construction, and hence parsing, in mind.

There is no known liner time parsing or recognition algorithm that can be used with all context free grammars.
In their recognizer forms the CYK algorithm is worst case cubic on grammars in Chomsky normal form and Earley's
algorithm is worst case cubic on general context free grammers and worst case n2 on non-ambibuous grammars.
General recognizers must, by definition, be applicable to ambiguous grammars. Tomita's GLR algorithm is of unbounded
polynomial order in the worst case. Expanding general recognizers to parser raises several problems, not least
because there can be exponentially many or even infinitely many derivations for a given input string. A cubic
recognizer which was modified to simply return all derivations could become an unbounded parser.
Of course, it can be argued that ambiguous grammars reflect ambiguous semantics and thus should not be used in
practice. This would be far too extreme a position to take. For example, it is well known that the if-else
statement in hthe AnSI-standard grammar for C is ambiguous, but a longest match resolution results in a linear
time parser that attach the else to the most recent if, as specified by the ANSI-C semantics. The ambiguous
ANSI-C grammar is certainly practical for parser implementation. However, in general ambiguity is not so easily handled,
and it is well known that grammar ambiguity is in fact undecidable Hopcroft \textit{et al} \cite{Hopcroft:2006}, thus
we cannot expect a parser generator simply to check for ambiguity inthe grammar and report the problem back to the user.
Another possiblity is to avoid the issue by just returning one derivation. However, if only one derivation is returned
then this creates problems for a user who wants all derivations and, even in the case where only one derivation is
required, there is the issue of ensuring that it is the required derivationthat is returned. A truely general parser
will reutrn all possible derivations in some form. Perhaps the most well known representation is the shared packed
parse foreset SPPF described and used by Tomita \cite{Tomita:1985}. Tomita's description of the representation does ont allow
for the infinitely many derivations which arise from grammars which contain cycles, the source adapt the SPPF representation
to allow these. Johnson \cite{Johnson:1991} has shown that Tomita-style SPPFs are worst case unbounded polynomial size. Thus
using such structures will alo turn any cubic recognition technique into a worst case unbounded polynomial parsing technique.
Leaving aside the potential increase in complexity when turning a recogniser into a parser, it is clear that this proccess is often difficult to carry
out correctly. Earley gave an algorithm for constructing derivations of a string accepted by his recognizer,
but this was subsequently shown by Tomita \cite{Tomita:1985} to return spurious derivations in certain cases.
Tomita's original version of his algorithm failed to terminate on grammars with hidden left recursio and, as remarked above
, had no mechanism for contructing complete SPPFs for grammers with cycles.

A shared packed parse forest SPPF is a representation designed to reduce the space required to represent multiple derivation
trees for an ambiguous sentence. In an SPPF, nodes which have the same tree below them are shared and nodes which correspond
to different derivations of the same substring from the same non-terminal are combined by creating a packed node for each
family of children. Nodes can be packed only if their yields correspond to the same portion of the input string. Thus, to make it easier
to determine whether two alternates can be packed under a given node, SPPF nodes are labelled with a triple (x,i,j) where
$a_{j+1} \dots a_i$ is a substring matched by x. To obtain a cubic algorithm we use binarised SPPFs which contain intermediate additional
nodes but which are of worst case cubic size. (EXAMPlE SPPF running example???)

We can turn earley's algorithm into a correct parser by adding pointers between items rather than instances of non-terminals, and labelling th epointers
in a way which allows a binariesd SPPF to be constructed by walking the resulting structure. However, inorder to
construct a binarised SPPF we also have to introduce additional nodes for grammar rules of length greater than two,
complicating the final algorithm.
\<close>

section\<open>Aycock\<close>

text\<open>
Earley's parsing algorithm is a general algorithm, capable of parsing according to any context-free
grammar. General parsing algorithms like Earley parsing allow unfettered expression of ambiguous grammar
contructs which come up often in practice (REFERENCE).

In terms of implementation, the Earley sets are built in increasing order as the input is read. Also,
each set is typically represented as a list of items. This list representation of a set is particularly
convenient, because the list of items acts as a work queue when building the sets: items are examined
in order, applying the transformations as necessary: items added to the set are appended onto the end of
the list.

At any given point $i$ in the parse, we have two partially constructed sets. Scanner may add items to
$S_{i+1}$ and $S_i$ may have items added to it by Predictor and Completer. It is this latter possibility,
adding items to $S_i$ while representing sets as lists, which causes grief with epsilon-rules.
When Completer processes an item A -> dot, j which corresponds to the epsilon-rule A -> epsiolon, it must
look through $S_j$ for items with the dot before an A. Unfortunately, for epsilon-rule items, j is always
equal to i. Completer is thus looking through the partially constructed set $S_i$. Since implementations
process items in $S_i$ in order, if an item B -> alpha dot A beta, k is added to $S_i$ after Completer
has processed A -> dot, j, Completer will never add B -> \alpha A dot \beta, k to $S_i$. In turn, items
resulting directly and indirectly from B -> \alpha A dot \beta, k will be omitted too. This effectively
prunes protential derivation paths which might cause correct input to be rejected. (EXAMPLE)
Aho \textit{et al} \cite{Aho:1972} propose the stay clam and keep running the Predictor and Completer
in turn until neither has anything more to add. Earley himself suggest to have the Completer note that
the dot needed to be moved over A, then looking for this whenever future items were added to $S_i$.
For efficiency's sake the collection of on-terminals to watch for should be stored in a data structure
which allows fast access. Neither approach is very satisfactory. A third solution \cite{Aycoack:2002}
is a simple modification of the Predictor based on the idea of nullability. A non-terminal A is said to be
nullable if A derives star epsilon. Terminal symbols of course can never be nullable. The nullability of
non-terminals in a grammar may be precomputed using well-known techniques \cite{Appel:2003} \cite{Fischer:2009}
Using this notion the Predictor can be stated as follows: if A -> \alpha dot B \beta, j is in $S_i$,
add B -> dot \gamma, i to $S_i$ for all rules B -> \gamma. If B is nullable, also add A -> \alpha B dot \beta, j
to $S_i$. Explanation why I decided against it. Involves every grammar can be rewritten to not contain epsilon
productions. In other words we eagerly move the dot over a nonterminal if that non-terminal can derive epsilon
and effectivley disappear. The source implements this precomputation by constructing a variant of 
a LR(0) deterministic finite automata (DFA). But for an earley parser we must keep track of which parent
pointers and LR(0) items belong together which leads to complex and inelegant implementations \cite{McLean:1996}.
The source resolves this problem by constructing split epsilon DFAs, but still need to adjust the classical
earley algorithm by adding not only predecessor links but also causal links, and to construct the split
epsilon DFAs not the original grammar but a slightly adjusted equivalent grammar is used that encodes
explicitly information that is crucial to reconstructing derivations, called a grammar in nihilist normal form (NNF)
which might increase the size of the grammar whereas the authors note empirical results that the increase
is quite modest (a factor of 2 at most).

Example:
S -> AAAA, A -> a, A -> E, E -> epsilon, input a
$S_0$ S -> dot AAAA,0, A -> dot a, 0, A -> dot E, 0, E -> dot, 0, A -> E dot, 0, S -> A dot AAA, 0
$S_1$ A -> a dot, 0, S -> A dot AAA, 0, S -> AA dot AA, 0, A -> dot a, 1, A -> dot E, 1, E -> dot, 1, A -> E dot, 1, S -> AAA dot A, 0
\<close>

chapter\<open>Introduction\<close>

section\<open>Motivation\<close>

text\<open>some introduction about parsing, formal development of correct algorithms: an example based on
earley's recogniser, the benefits of formal methods, LocalLexing and the Bachelor thesis.\<close>

section\<open>Related Work\<close>

text\<open>Tomita \cite{Tomita:1987} presents an generalized LR parsing algorithm for augmented
context-free grammars that can handle arbitrary context-free grammars.

Izmaylova \textit{et al} \cite{Izmaylova:2016} develop a general parser 
combinator library based on memoized Continuation-Passing Style (CPS) recognizers that supports all
context-free grammars and constructs a Shared Packed Parse Forest (SPPF) in worst case cubic time and space.
\<close>

text\<open>
Obua \textit{et al} \cite{Obua:2017} introduce local lexing, a novel parsing concept which interleaves
lexing and parsing whilst allowing lexing to be dependent on the parsing process. They base their
development on Earley's algorithm and have verified the correctness with respect to its local lexing
semantics in the theorem prover Isabelle/HOL. The background theory of this Master's thesis is based
upon the local lexing entry \cite{LocalLexing-AFP} in the Archive of Formal Proofs.

Lasser \textit{et al} \cite{Lasser:2019} verify an LL(1) parser generator using the Coq proof assistant.

Barthwal \textit{et al} \cite{Barthwal:2009} formalize background theory
about context-free languages and grammars, and subsequently verify an SLR automaton and parser produced
by a parser generator.

Blaudeau \textit{et al} \cite{Blaudeau:2020} formalize the metatheory on Parsing expression grammars (PEGs) and
build a verified parser interpreter based on higher-order parsing combinators for expression grammars
using the PVS specification language and verification system. Koprowski \textit{et al} \cite{Koprowski:2011}
present TRX: a parser interpreter formally developed in Coq which also parses expression grammars.

Jourdan \textit{et al} \cite{Jourdan:2012} present a validator which checks if a context-free grammar
and an LR(1) parser agree, producing correctness guarantees required by verified compilers.

Lasser \textit{et al} \cite{Lasser:2021} present the verified parser CoStar based on the ALL(*) algorithm.
They proof soundness and completeness for all non-left-recursive grammars using the Coq proof assistant.
\<close>

section\<open>Structure\<close>

section\<open>Contributions\<close>

(*<*)
end
(*>*)
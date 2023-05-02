(*<*)
theory "01_Introduction"
  imports
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter \<open>QUESTIONS\<close>

text\<open>
  \begin{itemize}
    \item How much explain the proofs? \\
    \item How reference thm names? \\
  \end{itemize}
\<close>

chapter\<open>Snippets\<close>

section\<open>Earley\<close>

section\<open>Jones\<close>

section\<open>Scott\<close>

section\<open>Aycock\<close>

text\<open>
Earley's parsing algorithm is a general algorithm, capable of parsing according to any context-free
grammar. General parsing algorithms like Earley parsing allow unfettered expression of ambiguous grammar
contructs which come up often in practice (REFERENCE).

Earley parsers operate by constructing a sequence of sets, sometime called Earley sets. Given an input
$x_1 x_2 \dots x_n$ the parser builds $n+1$ sets: an initial set $S_0$ and one set $S_i$ for each input
symbol $x_i$. Elements of these sets are referred to as Earley items, which consist of three parts:
a grammar rule, a position in the right-hand side of the rule indicating how much of that rule has been
seen and a pointer to an earlier Earley set. Typically Earley items are written as $\dots$ where the position
in the rule's right-hand side is denoted by a dot and $j$ is a pointer to set $S_j$.
An Earley set $S_i$ is computed from an initial set of Earley items in $S_i$ and $S_{i+1}$ is initialized, by
applying the followingn three steps to the items in $S_i$ until no more can be added. $\dots$
An item is added to a set only if it is not in the set already. The initial set $S_0$ contains the items $\dots$
to begin with. If the final set contains the item $\dots$ then the input is accepted.

We have not used a lookahead in this description of Earley parsing since it's primary purpose is to
increase the efficieny of the Earley parser on a large class of grammars (REFERENCE).

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

section\<open>Related Work\<close>

subsection\<open>Related Parsing Algorithms\<close>

text\<open>Tomita \cite{Tomita:1987} presents an generalized LR parsing algorithm for augmented
context-free grammars that can handle arbitrary context-free grammars.

Izmaylova \textit{et al} \cite{Izmaylova:2016} develop a general parser 
combinator library based on memoized Continuation-Passing Style (CPS) recognizers that supports all
context-free grammars and constructs a Shared Packed Parse Forest (SPPF) in worst case cubic time and space.
\<close>

subsection\<open>Related Verification Work\<close>

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

section\<open>Future Work\<close>

text\<open>
Different approaches:

(1) SPPF style parse trees as in Scott et al -> need Imperative/HOL for this

Performance improvements:

(1) Look-ahead of k or at least 1 like in the original Earley paper.
(2) Optimize the representation of the grammar instead of single list, group by production, ...
(3) Keep a set of already inserted items to not double check item insertion.
(4) Use a queue instead of a list for bins.
(5) Refine the algorithm to an imperative version using a single linked list and actual pointers instead
    of natural numbers.
\<close>

text\<open>
Parse tree disambiguation:

Parser generators like YACC resolve ambiguities in context-free grammers by allowing the user
the specify precedence and associativity declarations restricting the set of allowed parses. But they
do not handle all grammatical restrictions, like 'dangling else' or interactions between binary operators
and functional 'if'-expressions.

Grammar rewriting:

Adams \textit{et al} \cite{Adams:2017} describe a grammar rewriting approach reinterpreting CFGs as
the tree automata, intersectiong them with tree automata encoding desired restrictions and reinterpreting
the results back into CFGs.

Afroozeh \textit{et al} \cite{Afroozeh:2013} present an approach to specifying operator precedence
based on declarative disambiguation rules basing their implementation on grammar rewriting.

Thorup \cite{Thorup:1996} develops two concrete algorithms for disambiguation of grammars based on the idea of 
excluding a certain set of forbidden sub-parse trees.

Parse tree filtering:

Klint \textit{et al} \cite{Klint:1997} propose a framework of filters to describe and compare a wide
range of disambiguation problems in a parser-independent way. A filter is a function that selects
from a set of parse trees the intended trees.
\<close>

chapter\<open>Introduction\<close>

section\<open>Motivation\<close>

text\<open>some introduction about parsing, formal development of correct algorithms: an example based on
earley's recogniser, the benefits of formal methods, LocalLexing and the Bachelor thesis.\<close>

text\<open>work with the snippets, reformulate!\<close>

section\<open>Structure\<close>

text\<open>standard blabla\<close>

section\<open>Related Work\<close>

text\<open>see folder and bibliography\<close>

section\<open>Contributions\<close>

text\<open>what did I do, what is new\<close>

(*<*)
end
(*>*)
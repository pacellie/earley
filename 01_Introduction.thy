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
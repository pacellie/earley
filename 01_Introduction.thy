(*<*)
theory "01_Introduction"
  imports
    "MyLaTeXSugar"
begin
(*>*)

chapter\<open>Introduction\<close>

text\<open>
DRAFT:

Start with the fact that language is essential for communication, not only between humans but also
between humans and machines. The work of Chomsky @{cite "Chomsky:1956"} laid the foundation to formalize grammars. A parser or recognizer
is the first step to go from unstructured text with the help of a grammar to capture the syntax or extension
of a language and consequently define its intension or semantics.

Definition Parser: Something that transforms a string of symbols into a structure according to a description
  of the mapping from strings to structures. Structures can be considered to be parse trees.

Definition Recognizer: Something that takes a string and ansers yes if the string is in the language
  otherwise no.

Context-free grammars have been used extensively for describing the syntax of programming languages
and natural languages. Parsing algorithms for context-free grammars consequently play a large role in
the implementation of compilers and interpreters for programming languages and of programs which understand
or translate natural languages. Numerous parsing algorithms have been developed. Some are general,
in the sense that they can handle all context-free grammars, while others can handle only subclasses of
grammars. The latter, restricted algorithms tend to be much more efficient The algorithm described here
seems to be the most efficient of the general algorithms, and also it can handle a larger class of grammars
in linear time than most of the restricted algorithms.

Since the invention of ALGOL 60 @{cite "Backus:1963"} and Irons @{cite "Irons:1961"} maybe first paper on
something we would nowadays call a parser, a block structured language the quest to solve the parsing problem begins:
Find an efficient, general, declarative, and practical parser.

Lucas @{cite "Lucas:1961"} publishes his description of a top-down recursive descent parser.

Knuth @{cite "Knuth:1965"} discovers the classes of LR(k) grammars and shift-reduce bottom-up LR parsing.
DeRemer @{cite "DeRemer:1969"} later develops his famous LALR algorithm combining the efficiency of
LR parsers with a compact representation of parser tables and were popularized by tools YACC and Bison.
Later Tomita \cite{Tomita:1985} extends LR parsing to generalized LR parsing to handle non-deterministic
and ambiguous grammars.

Note that top-down grammars lacked a mathematical description. Lewis and Stearns @{cite "Lewis:1968"}
fill that gap by defining LL(k) grammars.

Earley @{cite "Earley:1970"} publishes the first fully general parsing algorithm for all context-free grammars,
but is ahead of its time, since table-driven parsing, is daunting for the hardware of the 1960s.

Leo @{cite "Leo:1991"} discovers a way of speeding up right recursions in Earley's algorithm and is
linar for all LRR grammars, or a superset of LR(k) and therefore just about every unambiguous grammar
of practical interest.

Aycock and Horspool @{cite "Aycock:2002"} publish their attempt at a fast, practical Earley parser,
missing Leo's improvement but solving the zero-length production rule bug.

Ford @{cite "Ford:2004"} was proposed as an alternative to CFGS parsing expression grammars (PEGs)
provide an alternative, recognition-based formal foundation for describing machine-oriented
syntax, allows for more expressive grammars and features such as prioritized choice and unlimited
lookahead. And Ford @{cite "Ford:2006"} packrat parsing is a memoization based technique that efficiently
handles PEGs.

Wadler @{cite "Wadler:1995"} introduces monads and the illustrations include an example of
monadic combinator based parsing. Hutton and Meijer @{cite "Hutton:1996"} extend this later in their
paper on combinator parsing.

Izmaylova \textit{et al} \cite{Izmaylova:2016} develop a general parser 
combinator library based on memoized Continuation-Passing Style (CPS) recognizers that supports all
context-free grammars and constructs a Shared Packed Parse Forest (SPPF) in worst case cubic time and space.

Kegler @{cite "Kegler:2023"} can be considered state-of-the-art Earley parsing. It implements Leo performance
improvement for right recursions and fixes the zero-length production rule bug by incorporating the
work of Aycock and Horspool. It is linear for nearley all unambiguous gramamrs, in particular
for all LL(k), LR(k), LALR, operator grammars.

Incorporate our main contributions:
(1) formalization of large parts of Earley @{cite "Earley:1970"} and Jones @{cite "Jones:1972"} for the recognizer
(2) correction of Earley pointers which were shown by Tomita \cite{Tomita:1985} to be spurious with the pointers of Scott @{cite "Scott:2008"}.
(2) development of a functional algorithm for single parse trees and a generalization to a parse forest
  (that unfortunately is not promising)
\<close>

section\<open>Related Work\<close>

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

text\<open>
Chapter 2 informally describes the Earley recognizer algorithm and sketches a high-level correctness proof.
Chapter 3 introduces the interactive theorem prover Isabelle, formalizes context-free grammars and the algorithm
  of Chapter 2, and presents the soundness and completeness proofs.
Chapter 4 refines the algorithm of Chapter 3 to an executable implementation that already contains the
  necessary information to construct parse trees in the form of pointers. It then proves termination and
  correctness of the algorithm. Additionally, it provides an informal argument for the running time and
  discusses alternative implementations.
Chapter 5 starts by defining and proving the semantics of the pointers of Chapter 4. It then presents
  a functional algorithm that builds a single parse tree and proves its correctness, before generalizing
  this approach to an algorithm for a complete parse forest, proving soundness. It ends with a discussion
  about the missing completeness proof and alternative implementation approaches for parse forests.
Chapter 6 illustrates the complete formalization with a simple example that highlight the main theorems.
Chapter 7 concludes with a summary of this thesis and points the reader towards worthwhile future work.
\<close>

(*<*)
end
(*>*)
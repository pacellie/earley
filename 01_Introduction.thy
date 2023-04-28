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
    \item How to tum blau assumes shows fun ... keywords? \\
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

text\<open>TODO: LocalLexing!!!\<close>

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
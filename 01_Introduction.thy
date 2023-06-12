(*<*)
theory "01_Introduction"
  imports
    "MyLaTeXSugar"
begin
(*>*)

chapter\<open>Introduction\<close>

text\<open>
Communication is key, not only in everyday life while conveying ideas to other people, but also in
the interaction between human and machine. In both cases the medium to transport ideas between parties
is language. The exact structure of the language might range from more or less defined natural
speech to precisely and formally specified programming languages, but one thing is common to any
communication through language: it needs to be parsed. The work of Chomsky @{cite "Chomsky:1956"} laid
the foundation to formalize a grammar of a language. And nowadays one of the most popular approaches
to define the extension or syntax of a language, and consequently also its intension or semantics, are
his context-free grammars.

In the field of computer science a recognizer is a program that takes a string of symbols
and answers \textit{yes} if the string of symbols is in the language, otherwise it answers \textit{no}. A parser additionally
transforms the string of symbols into some structure, most commonly a parse tree, according to the grammar
of the language, if the answer is \textit{yes}. To define the syntax of a language
a recognizer suffices, to talk about the semantics of a language one necessarily requires a parser.

The conception of ALGOL 60 @{cite "Backus:1963"} and Irons @{cite "Irons:1961"} paper,
on what we would nowadays call a parser for a programming language, started the quest
to solve the parsing problem: find an efficient, general, declarative and practical parser.

During the early days, predating ALGOL 60, and surprisingly still to this day parsers are often written in an ad-hoc fashion.
And, more often than not, these algorithms work top-down starting with the highest-level non-terminal symbol
of the grammar and recursively descent to derive the input string. In 1961, Lucas @{cite "Lucas:1961"}
publishes the first description of what we would today call a top-down recursive descent parser,
and in 1968 Lewis and Stearns @{cite "Lewis:1968"} finally define LL(k) grammars with mathematical rigor.

In a parallel development Knuth @{cite "Knuth:1965"} discovers the classes of LR(k) grammars in 1965 and
conceives bottom-up LR parsing that starts from the input and successively reduces it to the target
language constructs. DeRemer @{cite "DeRemer:1969"} later develops his famous LALR algorithm, combining
the efficiency of LR parsers with a compact representation of parser tables, that is subsequently popularized
by tools such as YACC and Bison.

In a more recent development the functional programming community takes a stab at parsing.
In 1995, Wadler @{cite "Wadler:1995"} introduces monads and one of the motivating examples for their
applications is combinator-based parsing. Later Hutton and Meijer @{cite "Hutton:1996"} elaborate on this
approach in their infamous paper on monadic parser combinators. In 2004, Ford @{cite "Ford:2004"}
proposes parsing expression grammars (PEGs) as an alternative to context-free grammars, and later
introduces packrat parsing @{cite "Ford:2006"}.

Most parsing algorithms can only handle certain subclasses of grammars,
but for some applications such as natural language processing general parsing algorithms that can
handle arbitrary context-free grammars are needed. Sakai @{cite "Sakai:1961"} discovers table-parsing
in 1961 and his algorithm, nowadays more commonly called CYK algorithm, is rediscovered several times
by Hayes or Cocke @{cite "Cocke:1969"}, Younger @{cite "Younger:1967"}, and Kasami and Torii @{cite "Kasami:1969"}.
In 1985, Tomita \cite{Tomita:1985} extends LR parsing to generalized LR parsing. By then Earley @{cite "Earley:1970"}
had already published his top-down, table-driven parsing algorithm. Both handle non-deterministic and ambiguous grammars.

The main contributions of this thesis is the first verification of an Earley parser. We formalize
a slightly simplified functional version of Earley's @{cite "Earley:1970"} recognizer algorithm
using the interactive theorem prover Isabelle/HOL @{cite "Nipkow:2002"}, and prove soundness and completeness.
The base for our proofs are the extensive paper proofs of Jones @{cite "Jones:1972"}. We also incorporate
the work of Scott @{cite "Scott:2008"} to fix a bug in Earley's original implementation that was discovered
by Tomita \cite{Tomita:1985}, and develop two functional algorithms constructing respectively a single parse
tree and a parse forest, proving correctness of the former and soundness of the latter.
\<close>


section\<open>Related Work\<close>

text\<open>
The field of parsing is old and vast, but surprisingly only few algorithms and theorems seem to have been
verified formally. The basis for this thesis is Obua's formalization of Local Lexing @{cite "Obua:2017"} @{cite "LocalLexing-AFP"} in Isabelle,
a parsing concept that interleaves lexing and parsing allowing lexing to be dependent on the parsing process.
Lasser \textit{et al} \cite{Lasser:2019} verify an LL(1) parser generator using the Coq proof assistant.
Barthwal \textit{et al} \cite{Barthwal:2009} formalize background theory about context-free languages
and grammars, and subsequently verify an SLR automaton and parser produced by a parser generator.
Blaudeau \textit{et al} \cite{Blaudeau:2020} formalize the meta theory on PEGs and build a verified parser
interpreter based on higher-order parsing combinators for expression grammars using the PVS specification
language and verification system. Koprowski \textit{et al} \cite{Koprowski:2011} present TRX: a parser
interpreter formally developed in Coq which also parses expression grammars. Jourdan \textit{et al}
\cite{Jourdan:2012} present a validator which checks if a context-free grammar and an LR(1) parser
agree, producing correctness guarantees required by verified compilers. Lasser \textit{et al} \cite{Lasser:2021}
present the verified parser CoStar based on the ALL(*) algorithm using the Coq proof assistant.
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
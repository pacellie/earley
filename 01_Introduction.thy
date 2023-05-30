(*<*)
theory "01_Introduction"
  imports
    "MyLaTeXSugar"
begin
(*>*)

chapter\<open>Introduction\<close>

text\<open>some introduction about parsing, formal development of correct algorithms: an example based on
earley's recogniser, the benefits of formal methods, LocalLexing and the Bachelor thesis.\<close>

section\<open>Related Work\<close>

text\<open>Tomita @{cite "Tomita:1987"} presents an generalized LR parsing algorithm for augmented
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

text\<open>
SNIPPET:

Context-free grammars have been used extensively for describing the syntax of programming languages
and natural languages. Parsing algorithms for context-free grammars consequently play a large role in
the implementation of compilers and interpreters for programming languages and of programs which understand
or translate natural languages. Numerous parsing algorithms have been developed. Some are general,
in the sense that they can handle all context-free grammars, while others can handle only subclasses of
grammars. The latter, restricted algorithms tend to be much more efficient The algorithm described here
seems to be the most efficient of the general algorithms, and also it can handle a larger class of grammars
in linear time than most of the restricted algorithms.
\<close>

text\<open>
SNIPPET:

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
\<close>

(*<*)
end
(*>*)
(*<*)
theory "07_Conclusion"
  imports
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter\<open>Conclusion\<close>

section\<open>Summary\<close>

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

(*<*)
end
(*>*)
(*<*)
theory "07_Conclusion"
  imports
    "06_Examples"
begin
(*>*)

chapter\<open>Conclusion\<close>

text\<open>
In this chapter we shortly summarize the contributions of this thesis and point the reader towards
relevant and worthwhile future work.
\<close>

section\<open>Summary\<close>

text\<open>
Chapter 2: introduce Earley recognizer informally with a running example and formulate the final theorem, and three correspoinding lemmas
Chapter 3: formalize Earley recognizer by defining grammar, derivations, Earley items, the basic operations and the generation of a bin
  as the fixpoint, and finally functions Earley and Earley. We then proved well-formedness, soundness and completeness highlighting
  the common proof structure, how to work with and prove things about derivations, and digging into the core argument of the completeness
  proof. Finally we prove that the set of Earley items is finite.
Chapter 4: refine the approach of chapter 3 into a functional executable algorithm modelling the imperative implementation of Earley and
  additionally adding the necessary information to construct parse trees in the form of pointers. We prove termination of the algorithm
  as well as soundness and completeness by proving subsumption in both directions. For the completeness is non-tivial since the algorithm
  is incorrect for grammars containing nonempty derivations. We discuss possible solutions and in the end follow Jones and restrict the
  applicable grammars. We also give an informal arguemnt for the runnign time of the algorithm O(n4) as well as discuss performance improvements as well as
  sketch alternative implementations.
Chapter 5: define and prove the semantics of the pointers of Chapter 4, implement a parse tree algorithm,
  prove termination, soundness and correctness. Then try to generalize this into a parse forest and a corresponding
  algorithm, prove termination and soundness, but also discover some complications (termination and performance),
  ultimately abandon approach and point out a more promising approach.
Chapter 6: highlight the Isabelle version of the running example as well as the main theorems

Overall we formalized Earley original paper (modulo lookahead and some performance improvements) correcting
the pointers to represent pointers such as described in Scott. The main approach of stepwise refinement
of the algorithm and most of the proofs are inspired by the paper of Jones.
\<close>

section\<open>Future Work\<close>

text\<open>
Chapter 3: define the set of Earley items inductively instead of the operational approach which might lead to more elegant proofs
Chapter 4: since algorithm is modelled after imperative Earley, a second refinement step towards an imperative implementation
  also performance improvements: lookhead, set for faster bin append, set for faster predict, set for faster complete
Chapter 5: formalize the SPPF algorithm of Scott in particular the built-in version which would replace
  the classic pointers of earley by a direct construction of a parse forest.
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
(*<*)
theory "07_Conclusion"
  imports
    "06_Examples"
begin
(*>*)

chapter\<open>Conclusion\<close>

section\<open>Summary\<close>

text\<open>
We formalized and verified an Earley Parser. Our approach and proof development is incremental and
tries to separate the concerns of recognizing and parsing as much as possible.

In an initial step, we introduced an abstract set-based implementation of an Earley recognizer. Our contributions
build upon the foundation of the work on Local Lexing of Obua @{cite "Obua:2017"} @{cite "LocalLexing-AFP"},
who formalized the basic building blocks about context-free grammars and derivations. We then proved
the core theorems soundness, completeness and finiteness putting the main focus on the completeness proof
that is mostly inspired by the work of Jones @{cite "Jones:1972"}.

Subsequently, we refined the Earley recognizer algorithm to a functional executable implementation modeled
after the original imperative implementation of Earley @{cite "Earley:1970"}. Then we followed once more
Jones footsteps, by not explicitly reproving correctness of the algorithm, but instead replacing set-based
specifications by list-based implementations and proving subsumption in both directions. In the process,
we encountered the hurdles that concern Earley recognizers and grammars containing non-empty derivations, and
ultimately followed Jones one final time and restrained the grammar. Finally, we provided an informal argument
for the running time of our functional implementation and discussed alternative implementation approaches.

We moved on to extend the recognizer into a fully-fledged parser. First, we enriched the recognizer with
the necessary information to construct parse trees in the form of pointers that we modeled after the work
of Scott @{cite "Scott:2008"} and thus avoided erroneous derivations that occurred in Earley's original
version. We then developed a functional algorithm that utilizes the pointers to construct a single parse tree
and proved its correctness. In a last step, we attempted to generalize our algorithm from a parse tree to
a parse forest. We succeeded in proving soundness, but ultimately abandoned the approach.
Nonetheless, we learned valuable lessons that lay the foundation for future work.

We rounded off the development and highlighted the main theorems by implementing the running example
in Isabelle.
\<close>

section\<open>Future Work\<close>

text\<open>
The work on the formalization of Earley parsing is by no means completed. In the following
we sketch - in our opinion - worthwhile future work, roughly presented in decreasing order of importance,
although this might by subject to personal preference.

As mentioned in Chapter \ref{chapter:3}, we followed an operational approach to specify an abstract
set-based implementation of an Earley recognizer. In hindsight, it would have been more elegant to not
follow the approach of Obua but instead define the set of Earley items inductively in Isabelle. This
would probably also simplify some of the subsumption proofs of Chapter \ref{chap:04} that revolve around
function iteration.

From a practical point of view, the last missing piece of this formalization is the construction of a
complete parse forest that represent all possible derivation trees compactly. As discussed in Chapter \ref{chap:05},
the most promising approaches are the algorithms presented by Scott @{cite "Scott:2008"}, in particular
the algorithm that intertwines the construction of the shared-packed parse forest with the generation of
the Earley bins and thus does not need to concern itself with any technicalities whilst proving termination.
Note that Scott describes her algorithm at a high level of abstraction and consequently any attempted
formalization entails a significant amount of work.

A possible next step are the various opportunities to improve the performance of the algorithm(s).
One non-trivial optimization is another refinement step towards an imperative implementation that incorporates the
necessary performance optimizations to achieve the optimal cubic time and space bounds described in
Chapter \ref{chapter:3}. A formal proof of the complexity bounds should be attempted at this point.
Other performance improvements include incorporating a look-head symbol to prune dead end derivation
trees, and optimizing the representation of the grammar and the bins to enable faster prediction and
completion operations. Or one could reach for the stars and verify the state-of-the-art Earley-based
parsing algorithm Marpa introduced by Kepler @{cite "Kegler:2023"}. It allows arbitrary context-free
grammars, including grammars with empty derivations, by incorporating the work of Aycock and Horspool @{cite "Aycock:2002"},
and is based on the algorithms of Earley @{cite "Earley:1970"} and Leo @{cite "Leo:1991"} who significantly improves
the running time for right recursions. It claims to run in linear time for nearly all unambiguous grammars,
in particular all LL(k), LR(k), LALR, LRR and operator grammars.

In a last step, one might want to investigate how to incorporate parse tree disambiguation into an
Earley parser. One of strengths of an Earley parser is its ability to work with arbitrary context-free
grammars (at least grammars that contain non-empty derivations in our case). Nonetheless, one might
want to resolve some ambiguities by allowing the user the specify precedence and associativity declarations
restricting the set of allowed parses, as commonly found in parser generators. During our initial
research we investigated possible approaches. The following list is by no means conclusive:
Adams \textit{et al} \cite{Adams:2017} describe a grammar rewriting approach that reinterprets context-free
grammars as tree automata, intersects them with automata encoding the desired restrictions and reinterprets
the results into a context-free grammar. Afroozeh \textit{et al} \cite{Afroozeh:2013} present an approach
of specifying operator precedence based on declarative disambiguation rules basing their implementation
on grammar rewriting. Thorup \cite{Thorup:1996} develops two concrete algorithms for the disambiguation of
grammars based on the idea of excluding a certain set of forbidden sub-parse trees.
Possibly the most interesting approach, since it avoids grammar rewriting and is solely based on parse
tree filtering, is the work of Klint \textit{et al} \cite{Klint:1997}. They propose a framework of filters, that select from
a set of parse trees the intended trees, to describe and compare a wide range of disambiguation problems
in a parser-independent way. Last but not least, Marpa also allows the user to mix classical Chomskyan
parsing and precedence parsing to annotate expressions with precedence and association rules.
\<close>

(*<*)
end
(*>*)
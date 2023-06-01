(*<*)
theory "05_Earley_Parser"
  imports
    "04_Earley_Recognizer"
    "HOL-Library.Monad_Syntax"
begin
(*>*)

chapter\<open>Earley Parser Implementation \label{chap:05}\<close>

text\<open>
Although a recognizer is a useful tool, for most practical applications we would like to not only
know if the language specified by the grammar accepts the input, but we also want to obtain additional information
of how the input can be derived in the form of parse trees. In particular, for our running example, the
grammar $S ::= S + S \, | \, x$ and the input $\omega = x + x + x$ we want to obtain the two possible parse
trees illustrated in Figures \ref{fig:tree1} \ref{fig:tree2}. But constructing all possible parse trees at once is no
trivial task.

\begin{figure}[htpb]
    \centering
    \begin{minipage}{0.45\textwidth}
        \centering
        \psframebox[linestyle=none,framesep=10pt]{%
        \pstree{\LFTr{t}{\fontspec{Noto Sans}[Script=Latin]S}}{\pstree{\Tp[edge=none]}{%
          \pstree{\LFTr{t}{\fontspec{Noto Sans}[Script=Latin]S}}{\pstree{\Tp[edge=none]}{%
            \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]x}
            \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]+}
            \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]x}}}
          \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]+}
          \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]S}}}}
        \caption{Parse Tree: $\omega = (x + x) + x$} \label{fig:tree1}
    \end{minipage}\hfill
    \begin{minipage}{0.45\textwidth}
        \centering
        \psframebox[linestyle=none,framesep=10pt]{%
        \pstree{\LFTr{t}{\fontspec{Noto Sans}[Script=Latin]S}}{\pstree{\Tp[edge=none]}{%
          \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]x}
          \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]+}
          \pstree{\LFTr{t}{\fontspec{Noto Sans}[Script=Latin]S}}{\pstree{\Tp[edge=none]}{%
            \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]x}
            \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]+}
            \LFTw{t}{\fontspec{Noto Sans}[Script=Latin]x}}}}}}
        \caption{Parse Tree: $\omega = x + (x + x)$} \label{fig:tree2}
    \end{minipage}
\end{figure}

Earley @{cite "Earley:1970"} turns his recognizer into a parser by adding the following
pointers. If the algorithm performs a completion and constructs an item $B \rightarrow \, \alpha A \bullet \beta, i, k$,
it adds a pointer from the \textit{instance of the non-terminal} $A$ to the complete item
$A \rightarrow \, \gamma \bullet, j, k$. If there exists more than one possible way to complete the non-terminal
$A$ and obtain the item $B \rightarrow \, \alpha A \bullet \beta, i, k$, then multiple pointers originate
from the instance of the non-terminal $A$. Annotating every non-terminal of the right-hand side of the item
$A \rightarrow \, \gamma \bullet, j, k$ recursively with pointers thus represents the derivation trees for
the non-terminal $A$. After termination of the algorithm, the non-terminal that represents the start symbol
contains pointers representing all possible derivation trees.

Note that Earley's pointers connect instances of non-terminals, but Tomita @{cite "Tomita:1985"} showed
that this approach is incorrect and may lead to spurious derivations in certain cases. Scott @{cite "Scott:2008"}
presents an example for the grammar $S ::= SS \, | \, x$ and the input $\omega = xxx$. Earley's parser
correctly constructs the parse trees for the input but additionally returns erroneous parse trees representing
derivations of $xx$ and $xxxx$. The problem lies in the fact that left- and rightmost derivations are
intertwined when they should not be, since pointers originate from instances of non-terminals and don't
connect Earley items.

The most well-known data structure for representing all possible derivations, a shared packed parse
forest (SPPF), was introduced by Tomita @{cite "Tomita:1985"}. But Johnson @{cite "Johnson:1991"} has
shown that Tomita's representation of SPPFs are of worst case unbounded polynomial size and thus
would turn our $\mathcal{O}(n^4)$ recognizer into an unbounded polynomial parser. Scott @{cite "Scott:2008"}
adjust the SPPF data structure slightly and presents two algorithms based on Earley's recognizer that
are of worst case cubic space and time. Unfortunately, these algorithms are highly non-trivial and
very much imperative in nature, and thus not only exceed the scope of this thesis but are also
very difficult to map to a functional approach.

In this chapter we develop an efficient functional algorithm constructing a single parse
tree in Section \ref{sec:parse-tree} and prove its correctness. In Section \ref{sec:parse-forest}
we generalize this approach, introducing a data structure representing all possible parse trees
as a parse forest, adjusting the parse tree algorithm to compute such a forest and prove termination
and soundness of the algorithm. Finally, in Section \ref{sec:word} we discuss the performance, the missing
completeness proof of the algorithm and compare our approach to the algorithm of Scott in greater detail.
\<close>

section \<open>A Single Parse Tree \label{sec:parse-tree}\<close> 

text\<open>
The data structure @{term tree} represents parse trees as shown in Figures \ref{fig:tree1} \ref{fig:tree2}.
A @{term Leaf} always contains a single symbol (either terminal or non-terminal for partial derivation trees), a @{term Branch} consists of one non-terminal
symbol and a list of subtrees. The function @{term root_tree} returns the symbol of the root of the
parse tree. The yield of a leaf is the single symbol; to compute the yield for a branch with
subtrees @{term ts} we apply the function @{term yield_tree} recursively and concatenate the results. 
\<close>

datatype 'a tree =
  Leaf 'a
| Branch 'a "'a tree list"

fun root_tree :: "'a tree \<Rightarrow> 'a" where
  "root_tree (Leaf a) = a"
| "root_tree (Branch N _) = N"

fun yield_tree :: "'a tree \<Rightarrow> 'a sentential" where
  "yield_tree (Leaf a) = [a]"
| "yield_tree (Branch _ ts) = concat (map yield_tree ts)"

text\<open>
We introduce three notions of well-formedness for parse trees:
\begin{itemize}
  \item @{term wf_rule_tree}: A parse tree must represent a valid (partial) derivation tree according the the grammar @{term \<G>}.
    A leaf of a parse tree is always well-formed by construction, for each branch @{term "Branch N ts"}
    there has to exists a corresponding rule of the grammar @{term \<G>} such that $N \rightarrow \, $
    @{term "map root_tree ts"} and each subtree @{term "t \<in> set ts"} is well-formed.
  \item @{term wf_item_tree}: Each branch @{term "Branch N ts"} corresponds to an Earley item
    $N \rightarrow \, \alpha \bullet \beta, i, j$ such that the roots of the subtrees @{term ts} and
    @{term \<alpha>} coincide. Note that a branch is only well-formed according to the grammar if
    the roots of the subtrees are a \textit{complete} right-hand side of a production rule of the grammar.
    In contrast, a branch is well-formed according to an item if the roots of the subtrees are equal
    to @{term \<alpha>}, or, since we assume that Earley items are themselves well-formed, a \textit{prefix}
    of a right-hand side of a production rule.
  \item @{term wf_yield_tree}: For an item $N \rightarrow \, \alpha \bullet \beta, i, j$, the yield
    of a parse tree has to match the substring @{term "\<omega>[i..j\<rangle>"} of the input.
\end{itemize}
\<close>

fun wf_rule_tree :: "'a cfg \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_rule_tree _ (Leaf a) \<longleftrightarrow> True"
| "wf_rule_tree \<G> (Branch N ts) \<longleftrightarrow> (
    (\<exists>r \<in> set (\<RR> \<G>). N = rule_head r \<and> map root_tree ts = rule_body r) \<and>
    (\<forall>t \<in> set ts. wf_rule_tree \<G> t))"

fun wf_item_tree :: "'a cfg \<Rightarrow> 'a item \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_item_tree \<G> _ (Leaf a) \<longleftrightarrow> True"
| "wf_item_tree \<G> x (Branch N ts) \<longleftrightarrow> (
    N = item_rule_head x \<and>
    map root_tree ts = take (item_bullet x) (item_rule_body x) \<and>
    (\<forall>t \<in> set ts. wf_rule_tree \<G> t))"

definition wf_yield_tree :: "'a sentential \<Rightarrow> 'a item \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_yield_tree \<omega> x t \<equiv> yield_tree t = \<omega>[item_origin x..item_end x\<rangle>"


subsection \<open>Pointer Lemmas\<close>

text\<open>
In Chapter \ref{chap:04} we extended the algorithm of Chapter \ref{chapter:3} in two orthogonal
ways: implementing sets as lists and adding the additional information to construct parse trees
in the form null, predecessor, and predecessor/reduction pointers. But we did not formally define
the semantics of these pointers nor prove anything about their construction. In the following, we
define and proof soundness of the pointers.

\begin{itemize}
  \item A null pointer @{term Null} of an entry is sound if it @{term predicts} the item $x$ of
    the entry, or the bullet of $x$ is at the beginning of the right-hand side of its production rule
    and we have not yet scanned any substring of the input.
  \item A predecessor pointer @{term "Pre pre"} of an entry $e$ is sound for the input @{term \<omega>}, bins @{term bs},
    and the index of the current bin $k$ if $k > 0$, the predecessor index does not exceed the length
    of the predecessor bin at index $k-1$, and the predecessor item in bin $k-1$ at index $pre$ @{term scans}
    then item of the entry $e$. Item $x'$ @{term scans} item $x$ for index $k$ if the next symbol of
    $x'$ coincides with the terminal symbol at index $k-1$ in the input @{term \<omega>} and the item $x$ can be obtained
    by @{term "inc_item x' k"}. 
  \item We define the soundness a pointer @{term "PreRed p ps"} of an entry $e$ for each predecessor/reduction
    triple @{term "(k', pre, red) \<in> set (p#ps)"}. The index $k'$ of the predecessor bin must be strictly
    smaller than $k$, and both the predecessor and the reduction index must be within the bounds of their
    respective bins, or bin $k'$ and $k$. Additionally, predicate @{term completes} holds for $k$,
    the predecessor item $x'$, the item $x$ of entry $e$ and the reduction item $y$, capturing the semantics of
    the @{term Complete} operation: The next symbol of $x'$ is the non-terminal $N$ which coincides
    with the item rule head of $y$. Furthermore, the item $y$ is complete and the origin index of $y$
    aligns with the end index of $x'$. Finally, item $x$ can be obtained once more by @{term "inc_item x' k"}.
\end{itemize}
\<close>

definition predicts :: "'a item \<Rightarrow> bool" where
  "predicts x \<equiv> item_bullet x = 0 \<and> item_origin x = item_end x"

definition sound_null_ptr :: "'a entry \<Rightarrow> bool" where
  "sound_null_ptr e \<equiv> pointer e = Null \<longrightarrow> predicts (item e)"

definition scans :: "'a sentential \<Rightarrow> nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "scans \<omega> k x' x \<equiv> x = inc_item x' k \<and> (\<exists>a. next_symbol x' = Some a \<and> \<omega>!(k-1) = a)"

definition sound_pre_ptr :: "'a sentential \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a entry \<Rightarrow> bool" where
  "sound_pre_ptr \<omega> bs k e \<equiv> \<forall>pre. pointer e = Pre pre \<longrightarrow>
    k > 0 \<and> pre < |bs!(k-1)| \<and>
    scans \<omega> k (item (bs!(k-1)!pre)) (item e)"

definition completes :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "completes k x' x y \<equiv> x = inc_item x' k \<and> is_complete y \<and> item_origin y = item_end x' \<and>
    (\<exists>N. next_symbol x' = Some N \<and> N = item_rule_head y)"

definition sound_prered_ptr :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a entry \<Rightarrow> bool" where
  "sound_prered_ptr bs k e \<equiv> \<forall>p ps k' pre red. pointer e = PreRed p ps \<and>
    (k', pre, red) \<in> set (p#ps) \<longrightarrow> k' < k \<and> pre < |bs!k'| \<and> red < |bs!k| \<and>
    completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"

definition sound_ptrs :: "'a sentential \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "sound_ptrs \<omega> bs \<equiv> \<forall>k < |bs|. \<forall>e \<in> set (bs!k).
    sound_null_ptr e \<and> sound_pre_ptr \<omega> bs k e \<and> sound_prered_ptr bs k e"

text\<open>
We then prove the semantics of the pointers. The structure of the proofs is as always: we first
proof pointer soundness for the basic operations @{term bin_upd}, @{term bin_upds}, and @{term bins_upd}.
Followed by the corresponding proofs for the computation of a single bin or functions @{term Earley_bin_list'}
and @{term Earley_bin_list}. Finally, we prove that the initial bins are sound, and functions @{term Earley_list}
and @{term \<E>arley_list} maintain this property. Although it should be intuitively clear that the
semantics of pointers hold, the proofs are surprisingly not trivial at all, especially the soundness
proofs for functions @{term bin_upd} and @{term Earley_bin_list'}. The complexity mostly stems from
the predecessor/reduction case that requires a quite significant amount of case splitting due to the indexing and depending
on the type of the newly inserted items. Nonetheless, since the proofs are very technical but do not
reveal anything new in structure, we only state them and omit going into detail.
\<close>

lemma sound_ptrs_bin_upd:
  assumes "k < |bs|"
  assumes "distinct (items (bs!k))"
  assumes "sound_ptrs \<omega> bs"
  assumes "sound_null_ptr e"
  assumes "sound_pre_ptr \<omega> bs k e"
  assumes "sound_prered_ptr bs k e"
  shows "sound_ptrs \<omega> (bs[k := bin_upd e (bs!k)])"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_bin_upds:
  assumes "k < |bs|"
  assumes "distinct (items (bs!k))"
  assumes "distinct (items es)"
  assumes "sound_ptrs \<omega> bs"
  assumes "\<forall>e \<in> set es. sound_null_ptr e \<and> sound_pre_ptr \<omega> bs k e \<and> sound_prered_ptr bs k e"
  shows "sound_ptrs \<omega> (bs[k := bin_upds es (bs!k)])"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_Earley_bin_list':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "nonempty_derives \<G>"
  assumes "sound_items \<G> \<omega> (bins bs)"
  assumes "sound_ptrs \<omega> bs" 
  shows "sound_ptrs \<omega> (Earley_bin_list' k \<G> \<omega> bs i)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_Earley_bin_list:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "nonempty_derives \<G>"
  assumes "sound_items \<G> \<omega> (bins bs)"
  assumes "sound_ptrs \<omega> bs"
  shows "sound_ptrs \<omega> (Earley_bin_list k \<G> \<omega> bs)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_Init_list:
  shows "sound_ptrs \<omega> (Init_list \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_Earley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  assumes "k \<le> |\<omega>|"
  shows "sound_ptrs \<omega> (Earley_list k \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  shows "sound_ptrs \<omega> (\<E>arley_list \<G> \<omega>)"
(*<*)
  sorry
(*>*)


subsection \<open>The Parse Tree Algorithm\<close>

text\<open>
After execution of the @{term \<E>arley_list} algorithm we obtain bins representing the complete set
of Earley items. The null, predecessor, and predecessor/reduction pointers provide a way to navigate
between items or through these bins, and, since they are sound, a way to construct derivation trees.
The function @{term build_tree'} constructs the \textit{single} parse tree corresponding to the
derivation tree represented by the item $x$ of entry $e$ at index $i$ at the $k$-th bin according to the
well-formedness definitions of the beginning of this section.

If the pointer of entry $e$ is a null pointer, the algorithm starts building the tree rooted at
the left-hand side non-terminal $N$ of the production rule of the item $x$ by constructing an initially
empty branch containing the non-terminal $N$ and an empty list of subtrees. If the algorithm encounters
a predecessor pointer @{term "Pre pre"}, it first recursively calls itself, for bin $B_{k-1}$ and the
predecessor index @{term pre}, obtaining a partial parse tree @{term "Branch N ts"}. Since the predecessor pointer is sound,
in particular the @{term scans} predicate holds, we append a Leaf containing the terminal symbol at index
$k-1$ of the input @{term \<omega>} to the list of substrees @{term ts}. In the case that
the pointer contains predecessor/reduction triples the algorithm only considers the first triple
@{term "(k', pre, red)"} since we are only constructing a single derivation tree. As for the predecessor
case, it recursively calls itself obtaining a partial derivation tree @{term "Branch N ts"} for the predecessor index @{term pre}
and bin $k'$, followed by yet another recursive call for the reduction item at the reduction index @{term red}
in the current bin $k$, constructing a complete derivation tree $t$. This time the @{term completes}
predicate holds, thus the next symbol of the predecessor item coincides with the item rule head of
the reduction item, or we are allowed to append the complete tree $t$ to the list of substrees @{term ts}.

Some minor implementation details to note are: the function @{term build_tree'} is a partial function,
and not tail recursive, hence we it has to return an optional value, as explained in Section \ref{sec:04-wellformedness}.
We are using the monadic do-notation commonly found in functional programming languages for the option
monad. An alternative but equivalent implementation would use explicit case distinctions. Finally, if
the function computes some value it is always a branch, never a single leaf.
\<close>

partial_function (option) build_tree' :: "'a bins \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tree option" where
  "build_tree' bs \<omega> k i = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some (Branch (item_rule_head (item e)) [])
    | Pre pre \<Rightarrow> (
        do {
          t \<leftarrow> build_tree' bs \<omega> (k-1) pre;
          case t of
            Branch N ts \<Rightarrow> Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))
          | _ \<Rightarrow> None })
    | PreRed (k', pre, red) _ \<Rightarrow> (
        do {
          t \<leftarrow> build_tree' bs \<omega> k' pre;
          case t of
            Branch N ts \<Rightarrow>
              do {
                t \<leftarrow> build_tree' bs \<omega> k red;
                Some (Branch N (ts @ [t]))
              }
          | _ \<Rightarrow> None })))"

text\<open>
Finally, function @{term build_tree} computes a complete derivation tree if there exists one. It searches the last bin for any finished items or items of the form
$S \rightarrow \gamma, 0, n$ where $S$ is the start symbol of the grammar @{term \<G>} and $n$ denotes
the length of the input @{term \<omega>}. If there exists such an item it calls function @{term build_tree'}
obtaining some parse tree representing the derivation @{term "\<G> \<turnstile> S \<Rightarrow>\<^sup>* \<omega>"} (we will have to proof that it never returns @{term None}),
otherwise it returns @{term None} since there cannot exist a valid parse tree due to the correctness
proof of Chapter \ref{chapter:3}.
\<close>

definition build_tree :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> 'a tree option" where
  "build_tree \<G> \<omega> bs \<equiv>
    let k = |bs| - 1 in (
    case filter_with_index (\<lambda>x. is_finished \<G> \<omega> x) (items (bs!k)) of
      [] \<Rightarrow> None
    | (_, i)#_ \<Rightarrow> build_tree' bs \<omega> k i)"


subsection \<open>Termination\<close>

text\<open>
The function @{term build_tree'} uses the null, predecessor and predecessor/reduction pointers to
navigate through the given bins by calling itself recursively. Sound pointers ensure that we are not
indexing outside of the bins, but this does not imply that the algorithm terminates. In the following
we outline when it always terminates with some parse tree. Lets assume the
function starts its computation at index $i$ of the $k$-th bin. If it encounters a null pointer, it
terminates immediately. If the pointer is a simple predecessor pointer, it calls itself recursively
for the previous bin. Due to the soundness of the predecessor pointer the index $k-1$ of this bin
is strictly smaller than $k$. A similar argument holds for the first recursive call if the pointer
is a predecessor/reduction pointer for the predecessor case (@{term "k' < k"}). Or, we are following
the pointers \textit{strictly} back to the origin bin and thus must terminate at some point. But for
the reduction pointer we run into a problem: the recursive call is for item at index $i$ is in the same
bin $k$ for a different index $red$, which in turn might contain again reduction triples and so on.
Hence, it is possible that we end up in a cycle of reductions and never terminate. Take for example the
grammer $A ::= x \, | \, B \qquad B ::= A$ and the input $\omega = x$. Table \ref{tab:cyclic-pointers}
illustrates the bins computed by the algorithm of Chapter \ref{chapter:3}. Bin $B_1$ contains the entry
$B \rightarrow \, A \bullet, 0, 1; (0, 2, 0),(0, 2, 2)$ at index $1$ and its second reduction triple
$(0, 2, 2)$ a reduction pointer to index $2$ of the same bin. There we find the entry
$A \rightarrow \, B \bullet, 0, 1; (0, 0, 1)$ with a reduction pointer to index $1$ completing the
cycle. This is indeed valid since the grammar itself is cyclic, allowing for derivations of the form
$A \rightarrow \, B \rightarrow \, A \rightarrow \dots \rightarrow \, A \rightarrow \, x$.

  \begin{table}[htpb]
    \caption[Cyclic reduction pointers]{Cyclic reduction pointers} \label{tab:cyclic-pointers}
    \centering
    \begin{tabular}{| l | l | l |}
          & $B_0$                                     & $B_1$ \\
      \midrule
        0 & $A \rightarrow \, \bullet B, 0, 0; \bot$  & $A \rightarrow \, x \bullet, 0, 1; 1$ \\
        1 & $A \rightarrow \, \bullet x, 0, 0; \bot$  & $B \rightarrow \, A \bullet, 0, 1; (0, 2, 0),(0, 2, 2)$ \\
        2 & $B \rightarrow \, \bullet A, 0, 0; \bot$  & $A \rightarrow \, B \bullet, 0, 1; (0, 0, 1)$ \\
    \end{tabular}
  \end{table}

We need to address this problem when constructing all possible parse trees in Section \ref{sec:parse-forest},
but for now we are lucky. While constructing a single parse tree the algorithm always follows the
first reduction triple that is created when the entry is constructed initially. Since we only
append new entries to bins, the complete reduction item necessarily appears before the new entry with
the reduction triple. Furthermore, the implementation of function @{term bin_upd} also makes sure to not change this
triple. Thus, we know for each item in the $k$-th bin at index $i$ that the reduction pointer $red$,
that we follow while constructing a single parse tree, is strictly smaller than $i$. To summarize:
if the algorithm encounters a null pointer it terminates immediately, for predecessor pointers it
calls itself recursively in a bin with a strictly smaller index, and for reduction pointers it calls
itself in the same bin but for a strictly smaller index. The proofs for the monotonicity of the first
reduction pointer for functions @{term bin_upd}, @{term bin_upds}, @{term bins_upd}, @{term Earley_bin_list'},
@{term Earley_bin_list}, @{term Earley_list}, and @{term \<E>arley_list} are completely analogous to
the soundness proof of the pointers. We omit them.
\<close>

definition mono_red_ptr :: "'a bins \<Rightarrow> bool" where
  "mono_red_ptr bs \<equiv> \<forall>k < |bs|. \<forall>i < |bs!k|.
    \<forall>k' pre red ps. pointer (bs!k!i) = PreRed (k', pre, red) ps \<longrightarrow> red < i"

text\<open>
Similarly to Chapter \ref{chapter:3} we define a suitable measure and a notion of well-formedness
for the input of the function @{term build_tree'} and proof an induction schema, in
the following referred to as \textit{tree induction}, by complete induction on the measure.
For the input quadruple @{term "(bs, \<omega>, k, i)"} the measure corresponds to the number of entries
in the first $k-1$ bins plus $i$. The call the input well-formed it must satisfy the following
conditions: sound and monotonic pointers, index $k$ does not exceed the length of the bins, and
index $i$ is within the bounds of the $k$-th bin.
\<close>

fun build_tree'_measure :: "('a bins \<times> 'a sentential \<times> nat \<times> nat) \<Rightarrow> nat" where
  "build_tree'_measure (bs, \<omega>, k, i) = foldl (+) 0 (map length (take k bs)) + i"

definition wf_tree_input :: "('a bins \<times> 'a sentential \<times> nat \<times> nat) set" where
  "wf_tree_input = { (bs, \<omega>, k, i) | bs \<omega> k i.
      sound_ptrs \<omega> bs \<and> mono_red_ptr bs \<and> k < |bs| \<and> i < |bs!k| }"

text\<open>
To conclude this subsection, we then prove termination of the function @{term build_tree'}, or for
well-formed input it always terminates with some branch, by \textit{tree induction}.
\<close>

lemma build_tree'_termination:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  shows "\<exists>N ts. build_tree' bs \<omega> k i = Some (Branch N ts)"
(*<*)
  sorry
(*>*)

subsection \<open>Correctness\<close>

lemma wf_item_tree_build_tree': \<comment>\<open>Detailed\<close>
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "k < |bs|"
  assumes "i < |bs!k|"
  assumes "build_tree' bs \<omega> k i = Some t"
  shows "wf_item_tree \<G> (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_yield_tree_build_tree': \<comment>\<open>Detailed\<close>
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "k < |bs|"
  assumes "k \<le> |\<omega>|"
  assumes "i < |bs!k|"
  assumes "build_tree' bs \<omega> k i = Some t"
  shows "wf_yield_tree \<omega> (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

text\<open>\<close>

theorem wf_rule_root_yield_tree_build_tree: \<comment>\<open>Detailed\<close>
  assumes "wf_bins \<G> \<omega> bs"
  assumes "sound_ptrs \<omega> bs"
  assumes "mono_red_ptr bs"
  assumes "|bs| = |\<omega>| + 1"
  assumes "build_tree \<G> \<omega> bs = Some t"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

corollary wf_rule_root_yield_tree_build_tree_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  assumes "build_tree \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some t"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

theorem correctness_build_tree_\<E>arley_list: \<comment>\<open>Detailed\<close>
  assumes "wf_\<G> \<G>"
  assumes "is_sentence \<G> \<omega>"
  assumes "nonempty_derives \<G>"
  shows "(\<exists>t. build_tree \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some t) \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry
(*>*)

text\<open>
To conclude this section, We give an informal argument for the running time of $\mathcal{O}(n^4)$.
We assume that the bins (or argument @{term bs}) are valid according to Chapter \ref{chapter:3} and
contain only sound and monotonic pointers. The algorithm @{term build_tree'} calls itself at most
once for each entry in the bins.
\<close>


section \<open>A Parse Forest \label{sec:parse-forest}\<close>

text\<open>
why not simply generate all parse trees integrated top down? yes for single parse tree, no for
all since exponential blow up
\<close>

datatype 'a forest =
  FLeaf 'a
  | FBranch 'a "'a forest list list"

fun combinations :: "'a list list \<Rightarrow> 'a list list" where
  "combinations [] = [[]]"
| "combinations (xs#xss) = [ x#cs . x <- xs, cs <- combinations xss ]"

fun trees :: "'a forest \<Rightarrow> 'a tree list" where
  "trees (FLeaf a) = [Leaf a]"
| "trees (FBranch N fss) = (
    let tss = (map (\<lambda>fs. concat (map (\<lambda>f. trees f) fs)) fss) in
    map (\<lambda>ts. Branch N ts) (combinations tss)
  )"


subsection \<open>The Parse Forest Algorithm\<close>

fun insert_group :: "('a \<Rightarrow> 'k) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a \<Rightarrow> ('k \<times> 'v list) list \<Rightarrow> ('k \<times> 'v list) list" where
  "insert_group K V a [] = [(K a, [V a])]"
| "insert_group K V a ((k, vs)#xs) = (
    if K a = k then (k, V a # vs) # xs
    else (k, vs) # insert_group K V a xs  
  )"

fun group_by :: "('a \<Rightarrow> 'k) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a list \<Rightarrow> ('k \<times> 'v list) list" where
  "group_by K V [] = []"
| "group_by K V (x#xs) = insert_group K V x (group_by K V xs)"

(*<*)
lemma [partial_function_mono]:
  "monotone option.le_fun option_ord
    (\<lambda>f. map_option concat (those (map (\<lambda>((k', pre), reds).
      f ((((r, s), k'), pre), {pre}) \<bind>
        (\<lambda>pres. those (map (\<lambda>red. f ((((r, s), t), red), b \<union> {red})) reds) \<bind>
          (\<lambda>rss. those (map (\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss])) | _ \<Rightarrow> None) pres))))
    xs)))"
  sorry
(*>*)

partial_function (option) build_trees' :: "'a bins \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> 'a forest list option" where
  "build_trees' bs \<omega> k i I = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some ([FBranch (item_rule_head (item e)) []])
    | Pre pre \<Rightarrow> (
        do {
          pres \<leftarrow> build_trees' bs \<omega> (k-1) pre {pre};
          those (map (\<lambda>f.
            case f of
              FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]]))
            | _ \<Rightarrow> None
          ) pres)
        })
    | PreRed p ps \<Rightarrow> (
        let ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps) in
        let gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps' in
        map_option concat (those (map (\<lambda>((k', pre), reds).
          do {
            pres \<leftarrow> build_trees' bs \<omega> k' pre {pre};
            rss \<leftarrow> those (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds);
            those (map (\<lambda>f.
              case f of
                FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss]))
              | _ \<Rightarrow> None
            ) pres)
          }
        ) gs))
      )
  ))"

definition build_trees :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> 'a forest list option" where
  "build_trees \<G> \<omega> bs \<equiv>
    let k = |bs| - 1 in
    let finished = filter_with_index (\<lambda>x. is_finished \<G> \<omega> x) (items (bs!k)) in
    map_option concat (those (map (\<lambda>(_, i). build_trees' bs \<omega> k i {i}) finished))"


subsection \<open>Termination\<close>

fun build_forest'_measure :: "('a bins \<times> 'a sentential \<times> nat \<times> nat \<times> nat set) \<Rightarrow> nat" where
  "build_forest'_measure (bs, \<omega>, k, i, I) = foldl (+) 0 (map length (take (k+1) bs)) - card I"

definition wf_trees_input :: "('a bins \<times> 'a sentential \<times> nat \<times> nat \<times> nat set) set" where
  "wf_trees_input = { (bs, \<omega>, k, i, I) | bs \<omega> k i I.
      sound_ptrs \<omega> bs \<and> k < |bs| \<and> i < |bs!k| \<and> I \<subseteq> {0..<|bs!k|} \<and> i \<in> I }"

lemma build_trees'_termination:
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  shows "\<exists>fs. build_trees' bs \<omega> k i I = Some fs \<and> (\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

theorem termination_build_tree_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  assumes "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
  shows "\<exists>fs. build_trees \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some fs"
(*<*)
  sorry
(*>*)


subsection \<open>Soundness\<close>

lemma wf_item_tree_build_trees':
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "k < |bs|"
  assumes "i < |bs!k|"
  assumes "build_trees' bs \<omega> k i I = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_item_tree \<G> (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_yield_tree_build_trees':
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "k < |bs|"
  assumes "k \<le> |\<omega>|"
  assumes "i < |bs!k|"
  assumes "build_trees' bs \<omega> k i I = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_yield_tree \<omega> (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

text\<open>\<close>

theorem wf_rule_root_yield_tree_build_trees:
  assumes "wf_bins \<G> \<omega> bs"
  assumes "sound_ptrs \<omega> bs"
  assumes "|bs| = |\<omega>| + 1"
  assumes "build_trees \<G> \<omega> bs = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

corollary wf_rule_root_yield_tree_build_trees_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  assumes "build_trees \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

theorem soundness_build_trees_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "is_sentence \<G> \<omega>"
  assumes "nonempty_derives \<G>"
  assumes "build_trees \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "derives \<G> [\<SS> \<G>] \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>


section \<open>A Word on Performance and Completeness \label{sec:word}\<close>

text\<open>
SNIPPET:

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

(*<*)
end
(*>*)
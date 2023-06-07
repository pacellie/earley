(*<*)
theory "05_Earley_Parser"
  imports
    "04_Earley_Recognizer"
    "HOL-Library.Monad_Syntax"
begin
(*>*)

chapter\<open>Earley Parser Implementation \label{chap:05}\<close>

text\<open>
Although a recognizer is a useful tool, for most practical applications we would like to, not only,
know if the language specified by the grammar accepts the input, but we also want to obtain additional information
of how the input can be derived in the form of parse trees. In particular, for our running example, the
grammar $S ::= S + S \,\, | \,\, x$ and the input $\omega = x + x + x$, we want to obtain the two possible parse
trees illustrated in Figures \ref{fig:tree1} and \ref{fig:tree2}. But constructing all possible parse trees at once is no
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

Earley @{cite "Earley:1970"} extends his recognizer to a parser by adding the following
pointers. If the algorithm performs a completion and constructs an item $B \rightarrow \, \alpha A \bullet \beta, i, k$,
it adds a pointer from the \textit{instance of the non-terminal} $A$ to the complete item
$A \rightarrow \, \gamma \bullet, j, k$. If there exists more than one possible way to complete the non-terminal
$A$ and obtain the item $B \rightarrow \, \alpha A \bullet \beta, i, k$, then multiple pointers originate
from the instance of the non-terminal $A$. Annotating every non-terminal of the right-hand side of the item
$A \rightarrow \, \gamma \bullet, j, k$ recursively with pointers thus represents the derivation trees for
the non-terminal $A$. Finally, after termination of the algorithm, the non-terminal that represents the start symbol
contains pointers representing all possible derivation trees.

Note that Earley's pointers connect instances of non-terminals, but Tomita @{cite "Tomita:1985"} showed
that this approach is incorrect and may lead to spurious derivations in certain cases. Scott @{cite "Scott:2008"}
presents an example for the grammar $S ::= SS \, | \, x$ and the input $\omega = xxx$. Earley's parser
correctly constructs the parse trees for the input but additionally returns erroneous parse trees representing
derivations of $xx$ and $xxxx$. The problem lies in the fact that left- and rightmost derivations are
intertwined when they should not be, since pointers originate from instances of non-terminals and don't
connect Earley items.

In this chapter we develop an efficient functional algorithm constructing a single parse
tree in Section \ref{sec:parse-tree} and prove its correctness. In Section \ref{sec:parse-forest}
we generalize this approach, introducing a data structure representing all possible parse trees
as a parse forest, adjusting the parse tree algorithm to compute such a forest, prove termination
and soundness of the algorithm, and informally sketch a completeness proof. Finally, in Section \ref{sec:word}
we discuss different data representations and implementation approaches for parse forests, comparing our approach
to the algorithms of Scott @{cite "Scott:2008"}.
\<close>

section \<open>A Single Parse Tree \label{sec:parse-tree}\<close> 

text\<open>
The data structure @{term tree} represents parse trees as shown in Figures \ref{fig:tree1} and \ref{fig:tree2}.
A @{term Leaf} always contains a single symbol (either terminal or non-terminal for partial derivation trees), a @{term Branch} consists of one non-terminal
symbol and a list of subtrees. The function @{term root_tree} returns the symbol of the root of the
parse tree. The yield of a leaf is its single symbol; to compute the yield for a branch with
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
  \item @{term wf_rule_tree}: A parse tree must represent a valid derivation tree according the the grammar @{term \<G>}.
    A leaf of a parse tree is always well-formed by construction. For each branch @{term "Branch N ts"}
    there has to exists a production rule $N \rightarrow \, $ @{term "map root_tree ts"} corresponding to the grammar @{term \<G>} and each subtree @{term "t \<in> set ts"} has to be well-formed.
  \item @{term wf_item_tree}: Each branch @{term "Branch N ts"} corresponds to an Earley item
    $N \rightarrow \, \alpha \bullet \beta, i, j$ such that the roots of the subtrees @{term ts} and
    @{term \<alpha>} coincide. Note that a branch is only well-formed according to the grammar if
    the roots of the subtrees form a \textit{complete} right-hand side of a production rule of the grammar.
    In contrast, a branch is well-formed according to an item if the roots of the subtrees are equal
    to @{term \<alpha>}, or, since we assume that Earley items are themselves well-formed, a \textit{prefix}
    of a right-hand side of a production rule.
  \item @{term wf_yield_tree}: For an item $N \rightarrow \, \alpha \bullet \beta, i, j$ the yield
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
the semantics of these pointers nor prove anything about their construction. In the following we
define and proof soundness of the pointers.

\begin{itemize}
  \item A null pointer @{term Null} of an entry is sound if it @{term predicts} the item $x$ of
    the entry, or the bullet of $x$ is at the beginning of the right-hand side of its production rule
    and we have not yet scanned any substring of the input, or item end and origin are identical.
  \item A predecessor pointer @{term "Pre pre"} of an entry $e$ is sound for the input @{term \<omega>}, bins @{term bs},
    and the index of the current bin $k$ if $k > 0$, the predecessor index does not exceed the length
    of the predecessor bin at index $k-1$, and the predecessor item in bin $k-1$ at index $pre$ @{term scans}
    the item of the entry $e$. An item $x'$ @{term scans} item $x$ for index $k$ if the next symbol of
    $x'$ coincides with the terminal symbol at index $k-1$ in the input @{term \<omega>} and the item $x$ can be obtained
    by @{term "inc_item x' k"}. 
  \item Finally, we define the soundness of a pointer @{term "PreRed p ps"} of an entry $e$ for each predecessor/reduction
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
We then prove the semantics of the pointers. The structure of the proofs is as usual: we first
proof pointer soundness for the basic operations @{term bin_upd}, @{term bin_upds}, and @{term bins_upd}.
Followed by the corresponding proofs for the computation of a single bin or functions @{term Earley_bin_list'}
and @{term Earley_bin_list}. Finally, we prove that the initial bins are sound, and functions @{term Earley_list}
and @{term \<E>arley_list} maintain this property. Although it should be intuitively clear that the
semantics of pointers hold, the proofs are surprisingly not trivial at all, especially the soundness
proofs for functions @{term bin_upd} and @{term Earley_bin_list'}. The complexity mostly stems from
the predecessor/reduction case that requires a quite significant amount of case splitting due to the indexing and dependence
on the type of the pointers of the newly inserted items. Nonetheless, since the proofs do not reveal anything new in structure
but are very technical, we only state them and omit going into detail.
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

lemma sound_ptrs_bin_upds:
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

lemma sound_ptrs_Earley_bin_list':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "nonempty_derives \<G>"
  assumes "sound_items \<G> \<omega> (bins bs)"
  assumes "sound_ptrs \<omega> bs" 
  shows "sound_ptrs \<omega> (Earley_bin_list' k \<G> \<omega> bs i)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_ptrs_Earley_bin_list:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "nonempty_derives \<G>"
  assumes "sound_items \<G> \<omega> (bins bs)"
  assumes "sound_ptrs \<omega> bs"
  shows "sound_ptrs \<omega> (Earley_bin_list k \<G> \<omega> bs)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_ptrs_Init_list:
  shows "sound_ptrs \<omega> (Init_list \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_ptrs_Earley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  assumes "k \<le> |\<omega>|"
  shows "sound_ptrs \<omega> (Earley_list k \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_ptrs_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  shows "sound_ptrs \<omega> (\<E>arley_list \<G> \<omega>)"
(*<*)
  sorry
(*>*)


subsection \<open>A Parse Tree Algorithm\<close>

text\<open>
After execution of the @{term \<E>arley_list} algorithm we obtain bins representing the complete set
of Earley items. The null, predecessor, and predecessor/reduction pointers provide a way to navigate
between items or through these bins, and, since they are sound, a way to construct derivation trees.
The function @{term build_tree'} constructs a \textit{single} parse tree corresponding to the item $x$ of entry $e$ at index $i$ of the $k$-th bin according to the
well-formedness definitions from the beginning of this section.

If the pointer of entry $e$ is a null pointer, the algorithm starts building the tree rooted at
the left-hand side non-terminal $N$ of the production rule of the item $x$ by constructing an initially
empty branch containing the non-terminal $N$ and an empty list of subtrees. If the algorithm encounters
a predecessor pointer @{term "Pre pre"}, it first recursively calls itself, for bin $B_{k-1}$ and the
predecessor index @{term pre}, obtaining a partial parse tree @{term "Branch N ts"}. Since the predecessor pointer is sound,
in particular the @{term scans} predicate holds, we append a Leaf containing the terminal symbol at index
$k-1$ of the input @{term \<omega>} to the list of substrees @{term ts}. In the case that
the pointer contains predecessor/reduction triples the algorithm only considers the first triple
@{term "(k', pre, red)"} due to the fact that we are only constructing a single derivation tree. As for the predecessor
case, it recursively calls itself obtaining a partial derivation tree @{term "Branch N ts"} for the predecessor index @{term pre}
and bin $k'$, followed by yet another recursive call for the reduction item at the reduction index @{term red}
in the current bin $k$, constructing a complete derivation tree $t$. This time the @{term completes}
predicate holds, thus the next symbol of the predecessor item coincides with the item rule head of
the reduction item, or we are allowed to append the complete tree $t$ to the list of substrees @{term ts}.

Some minor implementation details to note are: the function @{term build_tree'} is a partial function,
and not tail recursive, hence it has to return an optional value, as explained in Section \ref{sec:04-wellformedness}.
Furthermore, we are using the monadic do-notation commonly found in functional programming languages for the option
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
The function @{term build_tree} computes a complete derivation tree if there exists one. It searches the last bin for any finished items or items of the form
$S \rightarrow \gamma \bullet, 0, n$ where $S$ is the start symbol of the grammar @{term \<G>} and $n$ denotes
the length of the input @{term \<omega>}. If there exists such an item, it calls function @{term build_tree'}
obtaining some parse tree representing the derivation @{term "\<G> \<turnstile> S \<Rightarrow>\<^sup>* \<omega>"} (we will have to proof that it never returns @{term None}),
otherwise it returns @{term None} since there cannot exist a valid parse tree due to the correctness
proof for the Earley bins of Chapter \ref{chapter:3} if the argument @{term bs} was constructed by the
@{term \<E>arley_list} function.
\<close>

definition build_tree :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> 'a tree option" where
  "build_tree \<G> \<omega> bs \<equiv>
    let k = |bs| - 1 in (
    case filter_with_index (\<lambda>x. is_finished \<G> \<omega> x) (items (bs!k)) of
      [] \<Rightarrow> None
    | (_, i)#_ \<Rightarrow> build_tree' bs \<omega> k i)"


subsection \<open>Termination \label{q}\<close>

text\<open>
The function @{term build_tree'} uses the null, predecessor and predecessor/reduction pointers to
navigate through the given bins by calling itself recursively. Sound pointers ensure that we are not
indexing outside of the bins, but this does not imply that the algorithm terminates. In the following
we outline the cases for which it always terminates with some parse tree. Let's assume the
function starts its computation at index $i$ of the $k$-th bin. If it encounters a null pointer, it
terminates immediately. If the pointer is a simple predecessor pointer, it calls itself recursively
for the previous bin. Due to the soundness of the predecessor pointer the index $k-1$ of this bin
is strictly smaller than $k$. A similar argument holds for the first recursive call if the pointer
is a predecessor/reduction pointer for the predecessor case (@{term "k' < k"}). Or, we are following
the pointers \textit{strictly} back to the origin bin $B_0$ and thus must terminate at some point. But for
the reduction pointer we run into a problem: the recursive call for the item at index $i$ is in the same
bin $k$ but for the reduction index $red$, which in turn might contain again reduction triples and so on.
Hence, it is possible that we end up in a cycle of reductions and never terminate. Take for example the
grammer $A ::= x \, | \, B, \, B ::= A$ and the input $\omega = x$. Table \ref{tab:cyclic-pointers}
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
the reduction triple. Furthermore, the implementation of the function @{term bin_upd} also makes sure to not change this
first triple. Thus, we know for any item at index $i$ in the $k$-th bin that its first reduction pointer $red$,
that we follow while constructing a single parse tree, is strictly smaller than $i$.

To summarize:
if the algorithm encounters a null pointer it terminates immediately, for predecessor pointers it
calls itself recursively in a bin with a strictly smaller index, and for reduction pointers it calls
itself in the same bin but for a strictly smaller index. The proofs for the monotonicity of the first
reduction pointer for functions @{term bin_upd}, @{term bin_upds}, @{term bins_upd}, @{term Earley_bin_list'},
@{term Earley_bin_list}, @{term Earley_list}, and @{term \<E>arley_list} are completely analogous to
the soundness proof of the pointers. We omit them.
\<close>

definition mono_red_ptrs :: "'a bins \<Rightarrow> bool" where
  "mono_red_ptrs bs \<equiv> \<forall>k < |bs|. \<forall>i < |bs!k|.
    \<forall>k' pre red ps. pointer (bs!k!i) = PreRed (k', pre, red) ps \<longrightarrow> red < i"

text\<open>
Similarly to Chapter \ref{chapter:3} we define a suitable measure and a notion of well-formedness
for the input of the function @{term build_tree'} and proof an induction schema, in
the following referred to as \textit{tree induction}, by complete induction on the measure.
For the input quadruple @{term "(bs, \<omega>, k, i)"} the measure corresponds to the number of entries
in the first $k-1$ bins plus $i$. We call the input well-formed if it satisfies the following
conditions: sound and monotonic pointers, the bin index $k$ does not exceed the length of the bins, and the item
index $i$ is within the bounds of the $k$-th bin.
\<close>

fun build_tree'_measure :: "('a bins \<times> 'a sentential \<times> nat \<times> nat) \<Rightarrow> nat" where
  "build_tree'_measure (bs, \<omega>, k, i) = foldl (+) 0 (map length (take k bs)) + i"

definition wf_tree_input :: "('a bins \<times> 'a sentential \<times> nat \<times> nat) set" where
  "wf_tree_input = { (bs, \<omega>, k, i) | bs \<omega> k i.
      sound_ptrs \<omega> bs \<and> mono_red_ptrs bs \<and> k < |bs| \<and> i < |bs!k| }"

text\<open>
To conclude this subsection, we prove termination of the function @{term build_tree'}, or for
well-formed input it always terminates with some branch, by \textit{tree induction}.
\<close>

lemma build_tree'_termination:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  shows "\<exists>N ts. build_tree' bs \<omega> k i = Some (Branch N ts)"
(*<*)
  sorry
(*>*)

subsection \<open>Correctness\<close>

text\<open>
From the previous lemma, We know that for well-formed input a call of the form @{term "build_tree' bs \<omega> k i"} always terminates
and yields some parse tree $t$. The following lemma proves that, for well-formed bins @{term bs},
$t$ represents a parse tree according to the semantics of the Earley item $N \rightarrow \, \alpha \bullet \beta, j, k$
at index $i$ in the $k$-th bin. The parse tree is rooted at the item rule head $N$, each of its subtrees is a complete derivation
tree following the rules of the grammar, and the list of roots of the subtrees themselves coincide with
@{term \<alpha>}. Moreover, the yield of $t$ matches the subsequence from $j$ to $k$ of the input @{term \<omega>}. 
\<close>

lemma wf_item_yield_build_tree':
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "build_tree' bs \<omega> k i = Some t"
  shows "wf_item_tree \<G> (item (bs!k!i)) t \<and> wf_yield_tree \<omega> (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

text\<open>
\begin{proof}

The proof is by \textit{tree induction} and we split it into three cases according to the kind
of pointer the algorithm encounters. Let $e$ denote the entry at index $i$ in bin $k$, and $x$
be the item of $e$, or $x = N \rightarrow \, \alpha \bullet \beta, j, k$.

\begin{itemize}

  \item @{term "pointer e = Null"}: 
    We have @{term "t = Branch (item_rule_head x) []"}. The root of $t$ coincides
    with the item rule head of $x$ by construction. Since the list of subtrees is empty, each of
    the subtrees is trivially well-formed according to the grammar. Moreover, we know @{term "predicts x"},
    due to the null pointer, or the bullet of $x$ is at position $0$. Thus, we have @{term "\<alpha> = []"} and
    the list of subtrees @{term "[]"} matches. In summary, we have @{term "wf_item_tree \<G> x t"}.
    From @{term "predicts x"}, we also know that @{term "j = k"}, or @{term "\<omega>[j..k\<rangle> = []"} by definition
    of the @{term slice} function. Since the yield of $t$ is empty, we have @{term "wf_yield_tree \<omega> x t"}
    and conclude the proof for the null pointer.

  \item @{term "pointer e = Pre pre"}:
    Let $x'$ denote the predecessor @{term "item (bs!(k-1)!pre)"} of the recursive function call for
    bin $k-1$ and index @{term pre}. The function always terminates with some branch for well-formed input.
    Hence, there exists a tree @{term "Branch N ts"} corresponding to the predecessor item $x'$, and we have:
    $$@{term "t = Branch N (ts @ [Leaf (inp!(k-1))])"}$$

    We also have @{term "(bs, \<omega>, k-1, pre) \<in> wf_tree_input"} by assumption since the predecessor pointer
    is sound and the the algorithm does not change the bins. Thus we can use the induction hypothesis and obtain:
    
    \begin{equation*}
      \begin{alignedat}{2}
        & @{term "wf_item_tree \<G> x' (Branch N ts)"} \qquad & (@{term "IH1"}) \\
        & @{term "wf_yield_tree \<omega> x' (Branch N ts)"} \qquad & (@{term "IH2"}) 
      \end{alignedat}
    \end{equation*}

    Since the pointer is a simple predecessor pointer, the predicate @{term "scans \<omega> k x' x"} holds and we also know that $x$ as well
    as $x'$ are well-formed bin items. Consequently, we obtain the following facts:

    \begin{equation*}
      \begin{alignedat}{2}
        & @{term "item_rule_head x' = item_rule_head x"} \qquad & (a) \\
        & @{term "item_rule_body x' = item_rule_body x"} \qquad & (b) \\
        & @{term "item_bullet x' + 1 = item_bullet x"} \qquad & (c) \\
        & @{term "next_symbol x' = Some (\<omega>!(k-1))"} \qquad & (d) \\
        & @{term "item_origin x' = item_origin x"} \qquad & (e) \\
        & @{term "item_end x = k"} \qquad & (f) \\
        & @{term "item_end x' = k-1"} \qquad & (g)
      \end{alignedat}
    \end{equation*}

    We first proof @{term "wf_item_tree \<G> x t"}:

    \begin{equation*}
      \begin{alignedat}{2}
        & @{term "map root_tree (ts @ [Leaf (\<omega>!(k-1))])"} & \\
        & \qquad = @{term "map root_tree ts @ [\<omega>!(k-1)]"} \qquad & (1) \\
        & \qquad = @{term "take (item_bullet x') (item_rule_body x') @ [\<omega>!(k-1)]"} \qquad & (2) \\
        & \qquad = @{term "take (item_bullet x') (item_rule_body x) @ [\<omega>!(k-1)]"} \qquad & (3) \\
        & \qquad = @{term "take (item_bullet x) (item_rule_body x)"} \qquad & (4)
      \end{alignedat}
    \end{equation*}

    (1) by definition.
    (2) by (@{term "IH1"}).
    (3) by (b).
    (4) by (b,c,d).
    The statement @{term "wf_item_tree \<G> x t"} follows by (a), using once more (@{term "IH1"}) to
    prove that all subtrees are complete according to the grammar by definition of @{term wf_item_tree}.

    To conclude the proof for the simple predecessor pointer, we prove the statement @{term "mbox0 (wf_yield_tree \<omega> x t)"}:

    \begin{equation*}
      \begin{alignedat}{2}
        & @{term "yield_tree (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"} & \\
        & \qquad = @{term "concat (map yield_tree ts) @ [\<omega>!(k-1)]"} \qquad & (1) \\
        & \qquad = @{term "\<omega>[item_origin x'..item_end x'\<rangle> @ [\<omega>!(k-1)]"} \qquad & (2) \\
        & \qquad = @{term "\<omega>[item_origin x'..item_end x' + 1\<rangle>"} \qquad & (3) \\
        & \qquad = @{term "\<omega>[item_origin x..item_end x' + 1\<rangle>"}  \qquad & (4) \\
        & \qquad = @{term "\<omega>[item_origin x..item_end x\<rangle>"} \qquad & (5)
      \end{alignedat}
    \end{equation*}

    (1) by definition.
    (2) by (@{term "IH2"}). 
    (3) by (g) and the definition of @{term slice}.
    (4) by (e).
    (5) by (f,g).

  \item @{term "pointer e = PreRed (k', pre, red) ps"}:
    The proof is similar in structure to the proof of the simple predecessor case. We only highlight
    the main differences. In contrast to only one recursive call for the predecessor item $x'$, we
    have another recursive call for the complete reduction item $y$. But we have also have an additional
    induction hypothesis. The proofs of @{term "wf_item_tree \<G> x t"} and @{term "wf_yield_tree \<omega> x t"}
    are analogous to the case above replacing @{term "Leaf (\<omega>!(k-1))"} with the branch obtained from
    the second recursive call. Statements similar to (a-g) hold since all items are well-formed and
    the predicate @{term "completes k x' x y"} is true.

\end{itemize}

\end{proof}
\<close>

text\<open>
Next we prove that, if the function @{term build_tree} returns a parse tree, it is a complete and
well-formed tree according to the grammar, the root of the tree is the start symbol of the grammar,
and the yield of the tree corresponds to the input. The subsequent corollary then proves that the theorem
in particular holds if we generate the bins using the algorithm of Chapter \ref{chap:04} if we adjust
the assumptions accordingly.
\<close>

theorem wf_rule_root_yield_build_tree:
  assumes "wf_bins \<G> \<omega> bs"
  assumes "sound_ptrs \<omega> bs"
  assumes "mono_red_ptrs bs"
  assumes "|bs| = |\<omega>| + 1"
  assumes "build_tree \<G> \<omega> bs = Some t"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry
(*>*)

text\<open>
\begin{proof}

The function @{term build_tree} searches the last bin for any finished items. Since it returns
a tree by assumption it is successful, or finds a finished item $x$ at index $i$, and calls
the function @{term "build_tree' bs \<omega> ( |bs| - 1) i"}. By assumption the input and the bins are
well-formed, we can discharge the assumptions of the previous two lemmas, obtain a tree @{term "t = Branch N ts"} and have:

$$@{term "wf_item_tree \<G> x t \<and> wf_yield_tree \<omega> x t"}$$

The item $x$ is finished or its rule head is the start symbol of the grammar, it is complete, and
its origin and end respectively are $0$ and @{term "|\<omega>|"}. Due to the completeness and well-formedness
of the item @{term "wf_item_tree \<G> x t"} implies @{term "wf_rule_tree \<G> t"} and @{term "root_tree t = \<SS> \<G>"}.
From @{term "wf_yield_tree \<omega> x t"} we have @{term "yield_tree t = \<omega>[item_origin x..item_end x\<rangle>"} by definition,
and consequently @{term "yield_tree t = \<omega>"}.

\end{proof}
\<close>

corollary wf_rule_root_yield_build_tree_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  assumes "build_tree \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some t"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry
(*>*)

text\<open>
We conclude this section with the final theorem stating that the function @{term build_tree}
returns some parse tree if and only if there exists a derivation of the input from the start symbol
of the grammar, provided we generated the bins with the algorithm of Chapter \ref{chap:04} and grammar
and input are well-formed.
\<close>

theorem correctness_build_tree_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "is_sentence \<G> \<omega>"
  assumes "nonempty_derives \<G>"
  shows "(\<exists>t. build_tree \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some t) \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry
(*>*)

text\<open>
\begin{proof}

The function @{term build_tree} searches the last bin for a finished item $x$.
It finds such an item and returns a parse tree if and only if the bins generated
by @{term "\<E>arley_list \<G> \<omega>"} are @{term recognizing} which in turn holds if and only if
there exists a derivation of the input from the start symbol of the grammar by
lemma @{thm[source] correctness_\<E>arley_list} using our assumptions.

\end{proof}
\<close>

section \<open>All Parse Trees \label{sec:parse-forest}\<close>

text\<open>
Computing a single parse tree is sufficient for unambiguous grammars. But an Earley parser - in its most general form -
can handle all context-free grammars. And for ambiguous grammars there might exist multiple
parse trees for a specific input, there might even be exponentially many. One example of a highly ambiguous
grammar that produces exponentially many parse trees is our running example. To be precise, the number of
parse trees for an input $\omega = x + \dots + x$ is the Catalan number $C_n$ where $n-1$ is the
number of times the terminal $x$ occurs in @{term \<omega>}. It is well known that the $n$-th Catalan number can be expressed as
$C_n = \frac{1}{n+1} \binom{2n}{n}$ and thus grows asympotically at least exponentially. For example, the number of parse trees for an input @{term \<omega>} containing
$12$ times the terminal $x$ is already $C_{11} = 58786$. Thus, it is infeasible to compute all possible
parse trees in a naive fashion.

In the following we generalize the algorithm for a single parse tree to compute a representation of
all parse trees, or a parse forest. The key idea is to find a data structure that allows as much structural
sharing as possible between different parse trees. As an initial step, we make the following observation:
for two reduction triples $@{term "(k'\<^sub>A, pre\<^sub>A, red\<^sub>A)"}$ and $@{term "(k'\<^sub>B, pre\<^sub>B, red\<^sub>B)"}$ of an Earley item
we know that @{term "red\<^sub>A \<noteq> red\<^sub>B"}, but it might be the case that @{term "k'\<^sub>A = k'\<^sub>B"} (which implies
@{term "pre\<^sub>A = pre\<^sub>B"} due to the set semantics of the bins). In other words, for different reduction
items, we might have the same predecessor item and thus can share the subtree representing the predecessor.

We define a data type @{term forest} capturing this idea and representing parse forest. Consider an arbitrary production rule
$S \rightarrow \, AaB$ for non-terminals $S, A, B$ and terminal $a$. A branch of a single tree
contains a list of length $3$ containing the three subtrees $t_A$, $t_a$, and $t_B$ corresponding to
the three symbols $A$, $a$, and $B$. For a parse forest we still have a list of length $3$, but each element is now
again a list of forests sharing subtrees derived from the same non-terminal. For example, a branch
might look like @{term "[[f\<^sub>A\<^sub>1, f\<^sub>A\<^sub>2], [f\<^sub>a], [f\<^sub>B]]"} if there are two possible parse forests derived from
the non-terminal $A$. Note that if the subforest is a forest leaf than the list contains just this
single leaf, or there never occurs a situation like @{term "[[f\<^sub>A], [f\<^sub>a\<^sub>1, f\<^sub>a\<^sub>2], [f\<^sub>B]]"}.
\<close>

datatype 'a forest =
  FLeaf 'a
| FBranch 'a "'a forest list list"

text\<open>
We define an abstraction function @{term trees} recovering all possible parse trees for a parse forest.
For a forest leaf this is trivial, for a forest branch @{term "FBranch N fss"} we first apply the function
@{term trees} recursively for all subforests @{term fss}, concatenating the results for each subforest. E.g. for
@{term "[[f\<^sub>A\<^sub>1, f\<^sub>A\<^sub>2], [f\<^sub>a], [f\<^sub>B]]"} we might obtain @{term "[[t\<^sub>A\<^sub>1\<^sub>1, t\<^sub>A\<^sub>1\<^sub>2, t\<^sub>A\<^sub>2], [t\<^sub>a], [t\<^sub>B]]"} if the
forest @{term "f\<^sub>A\<^sub>1"} yields two parse trees @{term "t\<^sub>A\<^sub>1\<^sub>1"} and @{term "t\<^sub>A\<^sub>1\<^sub>2"} and every other forest yields only
a single tree. The three possible subtrees for the non-terminal $N$ are then: @{term "[t\<^sub>A\<^sub>1\<^sub>1, t\<^sub>a, t\<^sub>B]"}, @{term "[t\<^sub>A\<^sub>1\<^sub>2, t\<^sub>a, t\<^sub>B]"},
and @{term "[t\<^sub>A\<^sub>2, t\<^sub>a, t\<^sub>B]"}.
\<close>

fun combinations :: "'a list list \<Rightarrow> 'a list list" where
  "combinations [] = [[]]"
| "combinations (xs#xss) = [ x#cs . x <- xs, cs <- combinations xss ]"

fun trees :: "'a forest \<Rightarrow> 'a tree list" where
  "trees (FLeaf a) = [Leaf a]"
| "trees (FBranch N fss) = (
    let tss = (map (\<lambda>fs. concat (map (\<lambda>f. trees f) fs)) fss) in
    map (\<lambda>ts. Branch N ts) (combinations tss)
  )"


subsection \<open>A Parse Forest Algorithm\<close>

text\<open>
We define two auxiliary functions @{term group_by} and @{term insert_group} grouping a list of values @{term xs} according to a key-mapping $K$
and a value-mapping $V$ by key. E.g. for the list of tuples @{term "xs = [(1::nat, a), (2, b), (1, c)]"} and
mappings @{term "K = fst"} and @{term "V = snd"} we obtain the association list @{term "[(1::nat, [a, c]), (2, [b])]"}.
\<close>

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

text\<open>
Next we define the function @{term "build_forests'"}. It takes as arguments the bins @{term bs}, the indices of the bin and
item, $k$ respectively $i$, and a set of natural numbers $I$, and returns an optional list of parse forests.
There are two things to note here: the return type and the argument $I$. One might expect that we can return
a single parse forest and not a list of forests. This is not the case. Although we are sharing subforests for two distinct reduction triples
@{term "(k'\<^sub>A, pre\<^sub>A, red\<^sub>A)"} and @{term "(k'\<^sub>B, pre\<^sub>B, red\<^sub>B)"} if @{term "(k'\<^sub>A, pre\<^sub>A) = (k'\<^sub>B, pre\<^sub>B)"}, we
can not share the subforests if the predecessor items are distinct, and hence need to return two distinct forests in this case. Furthermore, the algorithm returns an
optional value since the function might not terminate if the pointers are not sound as it was the case
for function @{term "build_tree'"}. But unfortunately, this time around the situation is even worse:
even for sound pointers the function @{term build_forests'} might not terminate.
As explained in Subsection \ref{q}, the bins computed by the algorithm @{term \<E>arley_list} contain
cyclic reduction pointers for cyclic grammars and thus naively following all reduction pointers might lead
to non-termination. To ensure the termination of the algorithm we keep track of the items the algorithm
already visited in a single bin by means of the additional argument $I$ representing the indices
of the previous function calls in the same bin. The algorithm proceeds as follows:

Let $e$ denote the $i$-th item in the $k$-th bin.. If the pointer of $e$ is
a null pointer the forest algorithm proceeds analogously to the tree algorithm, constructing an initially
empty forest branch. For the simple predecessor case it calls itself recursively for the previous bin
$k-1$, predecessor index @{term pre}, and initializes the set of visited indices for bin $B_{k-1}$ with
the index @{term pre}, obtaining a list of optional predecessor forests. It then appends
to the list of subforests of each of these predecessor forests a new forest leaf containing the terminal symbol at
index $k-1$ of the input. Note the monadic do-notation for the option monad, and the use
of the function @{term those} that converts a list of optional values into an optional list of values
if and only if each of each one of the optional values is present or not none. In the case that the algorithm
encounters a predecessor/reduction pointer it first makes sure to not enter a cycle of reductions
by discarding any reduction indices that are contained in $I$ and thus were already processed in earlier
recursive calls. It then groups the reduction triples by predecessor. Subsequently, for each tuple of predecessor
($k'$ and @{term pre}) and reduction (@{term reds}) indices it proceeds as follows. It first calls itself once recursively
for the predecessor, initializing the set $I$ as @{term "{pre}"}, and obtaining a list of predecessor
forests. Then it executes one recursive call for each reduction index @{term "red \<in> set reds"}
in the current bin $k$ making sure to mark the index @{term "red"} as already visited by adding it to $I$.
Finally, it appends to the list of subforests of each predecessor forests the list of reduction forests
computed in the previous step.

The function @{term build_forests} is then defined analogously to the function @{term build_tree}.
\<close>

partial_function (option) build_forests' :: "'a bins \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> 'a forest list option" where
  "build_forests' bs \<omega> k i I = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some ([FBranch (item_rule_head (item e)) []])
    | Pre pre \<Rightarrow> (
        do {
          pres \<leftarrow> build_forests' bs \<omega> (k-1) pre {pre};
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
            pres \<leftarrow> build_forests' bs \<omega> k' pre {pre};
            rss \<leftarrow> those (map (\<lambda>red. build_forests' bs \<omega> k red (I \<union> {red})) reds);
            those (map (\<lambda>f.
              case f of
                FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss]))
              | _ \<Rightarrow> None
            ) pres)
          }
        ) gs))
      )
  ))"

definition build_forests :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> 'a forest list option" where
  "build_forests \<G> \<omega> bs \<equiv>
    let k = |bs| - 1 in
    let finished = filter_with_index (\<lambda>x. is_finished \<G> \<omega> x) (items (bs!k)) in
    map_option concat (those (map (\<lambda>(_, i). build_forests' bs \<omega> k i {i}) finished))"

subsection \<open>Termination\<close>

text\<open>
Analogously to the single tree algorithm we need to define well-formed input and a suitable
measure for the forest algorithm to prove an applicable induction schema (\textit{forest induction}) by
complete induction on the measure. An input quintuplet @{term "(bs, \<omega>, k, i, I)"} is well-formed if
the pointers are sound, the indices $k$ and $i$ are within their respective bounds, and the set of already
visited indices $I$ contains the current index $i$ and only consists of valid indices for the current bin $k$.
As termination measure we count the number of items in the first $k$ bins minus the indices the algorithm
already visited in the $k$-th bin.

We informally sketch the termination proof. If the algorithm encounters a null pointer it terminates immediately.
For predecessor pointers it calls itself recursively in a bin with a strictly smaller index, and for chains of reduction
pointers it visits each index of the current bin at most once.

We then prove by \textit{forest induction} that the function @{term build_forests'} always terminates
with some list of forests containing only forests branches for well-formed input.
\<close>

definition wf_forest_input :: "('a bins \<times> 'a sentential \<times> nat \<times> nat \<times> nat set) set" where
  "wf_forest_input = { (bs, \<omega>, k, i, I) | bs \<omega> k i I.
      sound_ptrs \<omega> bs \<and> k < |bs| \<and> i < |bs!k| \<and> i \<in> I \<and> I \<subseteq> {0..<|bs!k|} }"

fun build_forest'_measure :: "('a bins \<times> 'a sentential \<times> nat \<times> nat \<times> nat set) \<Rightarrow> nat" where
  "build_forest'_measure (bs, \<omega>, k, i, I) = foldl (+) 0 (map length (take (k+1) bs)) - card I"

lemma build_forests'_termination:
  assumes "(bs, \<omega>, k, i, I) \<in> wf_forest_input"
  shows "\<exists>fs. build_forests' bs \<omega> k i I = Some fs \<and> (\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss)"
(*<*)
  sorry
(*>*)

text\<open>
At this point, one might wonder if the argument $I$ is really needed. The problem regarding non-termination
are the cyclic reduction pointers. In theory we could modify the algorithm of Chapter \ref{chap:04} to not
add any cyclic pointers at all to the bins, prove an according lemma, and require non-cyclic pointers
for the well-formedness of the input of the forest algorithm. Subsequently, we could remove the - no longer
needed - argument $I$ from the function @{term build_forests'} and adjust the implementation accordingly.

But a problem of technical nature occurs while trying to prove the \textit{forest induction} schema.
We need to define a suitable measure capturing the termination argument in terms of the input, or a function
of the form $('a \mathit{bins} \times 'a \mathit{sentential} \times \mathit{nat} \times \mathit{nat}) \Rightarrow \, \mathit{nat}$.
But we cannot express the termination argument just in terms of the current input, we need access to
the history of recursive calls to argue that - for non-cyclic pointers - the algorithm calls itself
at most once for each index in the current bin $k$ during chains of reductions. Hence, we need to reintroduce
the argument $I$ of already visited indices or an equivalent argument. Note that this still simplifies
the function @{term build_forests'} slightly due to the fact that we no longer need to filter the list
of reduction pointers, but comes at the cost of computing cycles of reduction pointers in the algorithm
of Chapter \ref{chap:04}. Additionally, the bins only contain cyclic pointers if the grammar itself is
cyclic and hence not adding any cyclic pointers in the first place is incorrect.

In summary, the - already visited indices - argument $I$ serves two purposes: checking for pointer cycles while
constructing parse forests and expressing the termination argument of the algorithm.
\<close>

subsection \<open>Soundness\<close>

text\<open>
The following four lemmas prove soundness of the functions @{term build_forests'} and @{term build_forests}.
The proof are analogous to the corresponding proofs for the functions @{term build_tree'} and @{term build_tree},
replacing \textit{tree induction} with \textit{forest induction}. We might add that although the forest algorithm
is only a slight generalization of the tree algorithm and hence one might suspect that the proof should generalize
easily, this is unfortunately not the case. The proofs are rather unpleasant and cumbersome due to the complexity
that occurs from the interplay of the option monad (and actually list monad), functions @{term those}, @{term map_option},
@{term concat}, and the quite involved definition of the abstraction function @{term trees}. We refrain from
presenting any proofs in detail.
\<close>

lemma wf_item_yield_build_forests':
  assumes "(bs, \<omega>, k, i, I) \<in> wf_forest_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "build_forests' bs \<omega> k i I = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_item_tree \<G> (item (bs!k!i)) t \<and> wf_yield_tree \<omega> (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

text\<open>\<close>

theorem wf_rule_root_yield_build_forests:
  assumes "wf_bins \<G> \<omega> bs"
  assumes "sound_ptrs \<omega> bs"
  assumes "|bs| = |\<omega>| + 1"
  assumes "build_forests \<G> \<omega> bs = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

corollary wf_rule_root_yield_build_forests_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  assumes "build_forests \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

theorem soundness_build_forests_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "is_sentence \<G> \<omega>"
  assumes "nonempty_derives \<G>"
  assumes "build_forests \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

subsection \<open>Completeness\<close>

text\<open>
At this point we would like to prove that the forest algorithm indeed computes all possible parse trees.
But before we can attempt such a proof we first need to define what we mean by completeness. Recall the
cyclic grammer $A ::= x \, | \, B, \, B ::= A$. There exist an infinite amount of parse tree for the
input $\omega = x$. Although there certainly exist parse forests data structures that enable an representation
of an infinite amount of parse trees, our data type @{term forest} is not expressive enough. Note that,
since we assume a finite grammar, there necessarily has to exist a cycle in the grammar if there exist
an infinite amount of parse trees. The algorithm @{term build_forests'} does not complete any cycles and
thus returns only those parse trees up to the depth of the cycle in the grammar, or the parse trees
$A \, \text{--} \, x$ and $A \, \text{--} \, B \, \text{--} \, A \, \text{--} \, x$. In conclusion,
we can only prove the completeness of the algorithm for non-cyclic grammars.

But, as mentioned previously, we decided against formally proving completeness for the parse forest algorithm. The
reasoning is twofold. The completeness proof is far from trivial and exceeded the scope of this thesis.
The algorithm is only of theoretical interest and far from practical due to its poor performance.
The simple sharing of subforests for identical predecessor items is one optimization over the naive approach, but unfortunately
not enough to make the algorithm practical, as some experimentation suggests. We would need to introduce
further performance improvements. One obvious improvement is to use more structural sharing of subtrees.
At the moment the algorithm always appends new lists of subforests. We can avoid copying the current list
of subtrees if we preprend instead of append, and finally reverse the subtrees for complete items. 
Another concern is the number of recursive calls. As implemented, the algorithm might call itself recursively more than
once for the same Earley item or identical bins and item indices. This occurs for example if we have
two different predecessor items but the same reduction item. We could avoid repeated recursive calls using
common memoization techniques. We experimented with both performance improvements. The result was a
highly complex algorithm with still subpar performance. 

We can conclude: the straightforward generalization from the single parse tree algorithm to a parse
forest algorithm is probably correct (at least sound), but some experimentation suggest that due to its
poor performance the approach is not very practical.
\<close>

section \<open>A Word on Parse Forests \label{sec:word}\<close>

text\<open>
We have two main decisions to make while choosing an appropriate data structure and algorithm for implementing
an Earley parser. (1) should the construction of a parse forest be intertwined with the generation of the
Earley items or not, in other words, do we want a single or two phase algorithm. (2) and most importantly,
we need to choose an appropriate data structure to represent a parse forest.

One of the main lessons of Section \ref{sec:parse-forest} is that we should prefer a single phase over a two
phase algorithm. Any two phase algorithm must store some sort of data structure to indicate the origin
of each Earley item during the first phase. In the second phase it then walks this data structure while
constructing a parse forest and encounters the same complications regarding termination as the algorithm
of the previous section. In contrast, a single phase algorithm that constructs a parse forest while
generating the bins, can reuse the termination argument of the algorithm of Chapter \ref{chapter:3}: the
number of Earley items is finite.

The most well-known data structure for representing all possible derivations, a shared packed parse
forest (SPPF), was introduced by Tomita @{cite "Tomita:1985"}. The nodes of a SPPF are labelled by
triples @{term "(N, i, j)"} where @{term "\<omega>[i..j\<rangle>"} is the subsequence matched by the non-terminal $N$.
A SPPF utilizes two types of sharing. Nodes that have the same tree below them are shared. Additionally,
the SPPF might contain so-called packed nodes representing a family of children. Each child stands for
a different derivation of the same subsequence @{term "\<omega>[i..j\<rangle>"} from the same terminal but following an
alternate production rule. Scott @{cite "Scott:2008"} adjust the SPPF data structure of Tomita slightly
and presents two algorithms - one single and one two phase - based on Earley's recognizer that are of
worst case cubic space and time. Both approaches can be implemented on top of our implementation of
the Earley recognizer of Chapter \ref{chapter:3}, although we strongly advise for the single phase algorithm
due to the argument stated above. We did not attempt to formalize the algorithm of Scott since the
implementation is rather complex, we already glossed over some important details of the SPPF data structure
that are necessary to achieve the optimal cubic running time, and hence out of scope for this thesis.
\<close>

(*<*)
end
(*>*)
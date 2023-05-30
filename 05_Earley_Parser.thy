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
trees illustrated in Figure \ref{fig:trees}. But constructing all possible parse trees at once is no
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
        \caption{Parse Tree: $\omega = (x + x) + x$}
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
        \caption{Parse Tree: $\omega = x + (x + x)$}
    \end{minipage}
    \label{fig:trees}
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

datatype 'a tree =
  Leaf 'a
  | Branch 'a "'a tree list"

fun yield_tree :: "'a tree \<Rightarrow> 'a sentential" where
  "yield_tree (Leaf a) = [a]"
| "yield_tree (Branch _ ts) = concat (map yield_tree ts)"

fun root_tree :: "'a tree \<Rightarrow> 'a" where
  "root_tree (Leaf a) = a"
| "root_tree (Branch N _) = N"

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

definition predicts :: "'a item \<Rightarrow> bool" where
  "predicts x \<equiv> item_origin x = item_end x \<and> item_bullet x = 0"

definition scans :: "'a sentential \<Rightarrow> nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "scans \<omega> k x' x \<equiv> x = inc_item x' k \<and> (\<exists>a. next_symbol x' = Some a \<and> \<omega>!(k-1) = a)"

definition completes :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "completes k x' x y \<equiv> x = inc_item x' k \<and>
    is_complete y \<and>
    item_origin y = item_end x' \<and>
    (\<exists>N. next_symbol x' = Some N \<and> N = item_rule_head y)"

definition sound_null_ptr :: "'a entry \<Rightarrow> bool" where
  "sound_null_ptr e \<equiv> pointer e = Null \<longrightarrow> predicts (item e)"

definition sound_pre_ptr :: "'a sentential \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a entry \<Rightarrow> bool" where
  "sound_pre_ptr \<omega> bs k e \<equiv> \<forall>pre. pointer e = Pre pre \<longrightarrow>
    k > 0 \<and> pre < |bs!(k-1)| \<and>
    scans \<omega> k (item (bs!(k-1)!pre)) (item e)"

definition sound_prered_ptr :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a entry \<Rightarrow> bool" where
  "sound_prered_ptr bs k e \<equiv> \<forall>p ps k' pre red. pointer e = PreRed p ps \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow>
    k' < k \<and> pre < |bs!k'| \<and> red < |bs!k| \<and>
    completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"

definition sound_ptrs :: "'a sentential \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "sound_ptrs \<omega> bs \<equiv> \<forall>k < |bs|. \<forall>e \<in> set (bs!k).
    sound_null_ptr e \<and>
    sound_pre_ptr \<omega> bs k e \<and>
    sound_prered_ptr bs k e"

definition mono_red_ptr :: "'a bins \<Rightarrow> bool" where
  "mono_red_ptr bs \<equiv> \<forall>k < |bs|. \<forall>i < |bs!k|.
    \<forall>k' pre red ps. pointer (bs!k!i) = PreRed (k', pre, red) ps \<longrightarrow> red < i"

lemma sound_mono_ptrs_bin_upd:
  assumes "k < |bs|"
  assumes "distinct (items (bs!k))"
  assumes "sound_ptrs \<omega> bs"
  assumes "sound_null_ptr e"
  assumes "sound_pre_ptr \<omega> bs k e"
  assumes "sound_prered_ptr bs k e"
  assumes "mono_red_ptr bs"
  assumes "\<forall>k' pre red ps. pointer e = PreRed (k', pre, red) ps \<longrightarrow> red < |bs!k|"
  shows "sound_ptrs \<omega> (bs[k := bin_upd e (bs!k)])"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_bin_upds:
  assumes "k < |bs|"
  assumes "distinct (items (bs!k))"
  assumes "distinct (items es)"
  assumes "sound_ptrs inp bs"
  assumes "\<forall>e \<in> set es. sound_null_ptr e \<and> sound_pre_ptr inp bs k e \<and> sound_prered_ptr bs k e"
  assumes "mono_red_ptr bs"
  assumes "\<forall>e \<in> set es. \<forall>k' pre red ps. pointer e = PreRed (k', pre, red) ps \<longrightarrow> red < |bs!k|"
  shows "sound_ptrs inp (bs[k := bin_upds es (bs!k)]) \<and> mono_red_ptr (bs[k := bin_upds es (bs!k)])"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_Earley_bin_list':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "nonempty_derives \<G>"
  assumes "sound_items \<G> \<omega> (bins bs)"
  assumes "sound_ptrs \<omega> bs" 
  assumes "mono_red_ptr bs"
  shows "sound_ptrs \<omega> (Earley_bin_list' k \<G> \<omega> bs i) \<and> mono_red_ptr (Earley_bin_list' k \<G> \<omega> bs i)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_Earley_bin_list:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "nonempty_derives \<G>"
  assumes "sound_items \<G> \<omega> (bins bs)"
  assumes "sound_ptrs \<omega> bs"
  assumes "mono_red_ptr bs"
  shows "sound_ptrs \<omega> (Earley_bin_list k \<G> \<omega> bs) \<and> mono_red_ptr (Earley_bin_list k \<G> \<omega> bs)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_Init_list:
  shows "sound_ptrs \<omega> (Init_list \<G> \<omega>) \<and> mono_red_ptr (Init_list \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_Earley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  assumes "k \<le> |\<omega>|"
  shows "sound_ptrs \<omega> (Earley_list k \<G> \<omega>) \<and> mono_red_ptr (Earley_list k \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_mono_ptrs_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "nonempty_derives \<G>"
  shows "sound_ptrs \<omega> (\<E>arley_list \<G> \<omega>) \<and> mono_red_ptr (\<E>arley_list \<G> \<omega>)"
(*<*)
  sorry
(*>*)


subsection \<open>The Parse Tree Algorithm\<close>

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
          | _ \<Rightarrow> None
        })
    | PreRed (k', pre, red) _ \<Rightarrow> (
        do {
          t \<leftarrow> build_tree' bs \<omega> k' pre;
          case t of
            Branch N ts \<Rightarrow>
              do {
                t \<leftarrow> build_tree' bs \<omega> k red;
                Some (Branch N (ts @ [t]))
              }
          | _ \<Rightarrow> None
        })
  ))"

definition build_tree :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> 'a tree option" where
  "build_tree \<G> \<omega> bs \<equiv>
    let k = |bs| - 1 in (
    case filter_with_index (\<lambda>x. is_finished \<G> \<omega> x) (items (bs!k)) of
      [] \<Rightarrow> None
    | (_, i)#_ \<Rightarrow> build_tree' bs \<omega> k i)"


subsection \<open>Termination\<close>

fun build_tree'_measure :: "('a bins \<times> 'a sentential \<times> nat \<times> nat) \<Rightarrow> nat" where
  "build_tree'_measure (bs, \<omega>, k, i) = foldl (+) 0 (map length (take k bs)) + i"

definition wf_tree_input :: "('a bins \<times> 'a sentential \<times> nat \<times> nat) set" where
  "wf_tree_input = {
    (bs, \<omega>, k, i) | bs \<omega> k i.
      sound_ptrs \<omega> bs \<and>
      mono_red_ptr bs \<and>
      k < |bs| \<and>
      i < |bs!k| }"

lemma build_tree'_termination:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  shows "\<exists>N ts. build_tree' bs \<omega> k i = Some (Branch N ts)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

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

theorem wf_rule_root_yield_tree_build_tree:
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

theorem correctness_build_tree_\<E>arley_list:
  assumes "wf_\<G> \<G>"
  assumes "is_sentence \<G> \<omega>"
  assumes "nonempty_derives \<G>"
  shows "(\<exists>t. build_tree \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some t) \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry
(*>*)


section \<open>A Parse Forest \label{sec:parse-forest}\<close>

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
  "wf_trees_input = {
    (bs, \<omega>, k, i, I) | bs \<omega> k i I.
      sound_ptrs \<omega> bs \<and>
      k < |bs| \<and>
      i < |bs!k| \<and>
      I \<subseteq> {0..<|bs!k|} \<and>
      i \<in> I }"

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
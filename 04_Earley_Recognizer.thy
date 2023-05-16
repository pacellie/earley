(*<*)
theory "04_Earley_Recognizer"
  imports
    "03_Fixpoint_Earley_Recognizer"
begin
(*>*)

chapter\<open>Earley Recognizer Implementation \label{chap:04}\<close> 

text\<open>
  \begin{table}[htpb]
    \caption[Earley items with pointers running example]{Earley items with pointers for the grammar @{term \<G>}: $S \rightarrow \, x$, $S \rightarrow \, S + S$}\label{tab:earley-items}
    \centering
    \begin{tabular}{| l | l | l | l |}
          & $B_0$                                       & $B_1$                                           & $B_2$                                     \\
      \midrule
        0 & $S \rightarrow \, \bullet x, 0, 0;$     & $S \rightarrow \, x \bullet, 0, 1; 0$           & $S \rightarrow \, S + \bullet S, 0, 2; 1$ \\
        1 & $S \rightarrow \, \bullet S + S, 0, 0;$ & $S \rightarrow \, S \bullet + S, 0, 1; (0,1,0)$ & $S \rightarrow \, \bullet x, 2, 2;$       \\
        2 &                                         &                                                 & $S \rightarrow \, \bullet S + S, 2, 2;$   \\

      \midrule

          & $B_3$                                               & $B_4$                                     & $B_5$                                                    \\
      \midrule
        0 & $S \rightarrow \, x \bullet, 2, 3; 1$           & $S \rightarrow \, S + \bullet S, 2, 4; 2$ & $S \rightarrow \, x \bullet, 4, 5; 2$                    \\
        1 & $S \rightarrow \, S + S \bullet, 0, 3; (2,0,0)$ & $S \rightarrow \, S + \bullet S, 0, 4; 3$ & $S \rightarrow \, S + S \bullet, 2, 5; (4,0,0)$          \\
        2 & $S \rightarrow \, S \bullet + S, 2, 3; (2,2,0)$ & $S \rightarrow \, \bullet x, 4, 4;$       & $S \rightarrow \, S + S \bullet, 0, 5; (4,1,0), (2,0,1)$ \\
        3 & $S \rightarrow \, S \bullet + S, 0, 3; (0,1,1)$ & $S \rightarrow \, \bullet S + S, 4, 4;$   & $S \rightarrow \, S \bullet + S, 4, 5; (4,3,0)$          \\
        4 &                                                 &                                           & $S \rightarrow \, S \bullet + S, 2, 5; (2,2,1)$          \\
        5 &                                                 &                                           & $S \rightarrow \, S \bullet + S, 0, 5; (0,1,2)$          \\
    \end{tabular}
  \end{table}
\<close>

section\<open>Definitions\<close>

datatype pointer =
  Null
  | Pre nat
  | PreRed "nat \<times> nat \<times> nat" "(nat \<times> nat \<times> nat) list"

datatype 'a entry =
  Entry         
  (item : "'a item")
  (pointer : pointer)

type_synonym 'a bin = "'a entry list"
type_synonym 'a bins = "'a bin list"

definition items :: "'a bin \<Rightarrow> 'a item list" where
  "items b = map item b"

definition pointers :: "'a bin \<Rightarrow> pointer list" where
  "pointers b = map pointer b"

definition bins_items :: "'a bins \<Rightarrow> 'a items" where
  "bins_items bs = \<Union> { set (items (bs!k)) | k. k < length bs }"

definition bin_items_upto :: "'a bin \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin_items_upto b i = { items b ! j | j. j < i \<and> j < length (items b) }"

definition bins_items_upto :: "'a bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bins_items_upto bs k i = \<Union> { set (items (bs!l)) | l. l < k } \<union> bin_items_upto (bs!k) i"

definition wf_bin_items :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> 'a item list \<Rightarrow> bool" where
  "wf_bin_items cfg \<omega> k xs \<equiv> \<forall>x \<in> set xs. wf_item cfg \<omega> x \<and> item_end x = k"

definition wf_bin :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> 'a bin \<Rightarrow> bool" where
  "wf_bin cfg \<omega> k b \<equiv> distinct (items b) \<and> wf_bin_items cfg \<omega> k (items b)"

definition wf_bins :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "wf_bins cfg \<omega> bs \<equiv> \<forall>k < length bs. wf_bin cfg \<omega> k (bs!k)"

definition nonempty_derives :: "'a cfg \<Rightarrow> bool" where
  "nonempty_derives cfg \<equiv> \<forall>N. N \<in> set (\<NN> cfg) \<longrightarrow> \<not> derives cfg [N] []"

definition Init_list :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins" where
  "Init_list cfg \<omega> \<equiv> 
    let rs = filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg) in
    let b0 = map (\<lambda>r. (Entry (init_item r 0) Null)) rs in
    let bs = replicate (length \<omega> + 1) ([]) in
    bs[0 := b0]"

definition Scan_list :: "nat \<Rightarrow> 'a sentential \<Rightarrow> 'a  \<Rightarrow> 'a item \<Rightarrow> nat \<Rightarrow> 'a entry list" where
  "Scan_list k \<omega> a x pre \<equiv>
    if \<omega>!k = a then
      let x' = inc_item x (k+1) in
      [Entry x' (Pre pre)]
    else []"

definition Predict_list :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a \<Rightarrow> 'a entry list" where
  "Predict_list k cfg X \<equiv>
    let rs = filter (\<lambda>r. rule_head r = X) (\<RR> cfg) in
    map (\<lambda>r. (Entry (init_item r k) Null)) rs"

fun filter_with_index' :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index' _ _ [] = []"
| "filter_with_index' i P (x#xs) = (
    if P x then (x,i) # filter_with_index' (i+1) P xs
    else filter_with_index' (i+1) P xs)"

definition filter_with_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index P xs = filter_with_index' 0 P xs"

definition Complete_list :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a entry list" where
  "Complete_list k y bs red \<equiv>
    let orig = bs ! (item_origin y) in
    let is = filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items orig) in
    map (\<lambda>(x, pre). (Entry (inc_item x k) (PreRed (item_origin y, pre, red) []))) is"

fun bin_upd :: "'a entry \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "bin_upd e' [] = [e']"
| "bin_upd e' (e#es) = (
    case (e', e) of
      (Entry x (PreRed px xs), Entry y (PreRed py ys)) \<Rightarrow> 
        if x = y then Entry x (PreRed py (px#xs@ys)) # es
        else e # bin_upd e' es
      | _ \<Rightarrow> 
        if item e' = item e then e # es
        else e # bin_upd e' es)"

fun bin_upds :: "'a entry list \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "bin_upds [] b = b"
| "bin_upds (e#es) b = bin_upds es (bin_upd e b)"

definition bins_upd :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a entry list \<Rightarrow> 'a bins" where
  "bins_upd bs k es = bs[k := bin_upds es (bs!k)]"

partial_function (tailrec) Earley_bin_list' :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a bins" where
  "Earley_bin_list' k cfg \<omega> bs i = (
    if i \<ge> length (items (bs!k)) then bs
    else
      let x = items (bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow>
            if is_terminal cfg a then
              if k < length \<omega> then bins_upd bs (k+1) (Scan_list k \<omega> a x i)
              else bs
            else bins_upd bs k (Predict_list k cfg a)
        | None \<Rightarrow> bins_upd bs k (Complete_list k x bs i)
      in Earley_bin_list' k cfg \<omega> bs' (i+1))"

definition Earley_bin_list :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> 'a bins" where
  "Earley_bin_list k cfg \<omega> bs = Earley_bin_list' k cfg \<omega> bs 0"

fun Earley_list :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins" where
  "Earley_list 0 cfg \<omega> = Earley_bin_list 0 cfg \<omega> (Init_list cfg \<omega>)"
| "Earley_list (Suc n) cfg \<omega> = Earley_bin_list (Suc n) cfg \<omega> (Earley_list n cfg \<omega>)"

definition \<E>arley_list :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins" where
  "\<E>arley_list cfg \<omega> = Earley_list (length \<omega>) cfg \<omega>"

section \<open>Sets or Bins as list\<close>

lemma set_items_bin_upd:
  "set (items (bin_upd e b)) = set (items b) \<union> {item e}"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma set_items_bin_upds:
  "set (items (bin_upds es b)) = set (items b) \<union> set (items es)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma bins_items_bins_upd:
  assumes "k < length bs"
  shows "bins_items (bins_upd bs k es) = bins_items bs \<union> set (items es)"
(*<*)
  sorry
(*>*)

text\<open>Similar lemmas about @{term bins_items_upto}\<close>

section \<open>Well-formedness\<close>

text\<open>Just note that @{term bin_upd}, @{term bin_upds}, @{term bins_upd}, @{term Init_list},
@{term Scan_list}, @{term Predict_list}, @{term Complete_list} only generate @{term wf_bin} or
@{term wf_bins}\<close>

text\<open>Explain termination, how it is proved in Isabelle and custom induction schema.\<close>

fun earley_measure :: "nat \<times> 'a cfg \<times> 'a sentential \<times> 'a bins \<Rightarrow> nat \<Rightarrow> nat" where
  "earley_measure (k, cfg, \<omega>, bs) i = card { x | x. wf_item cfg \<omega> x \<and> item_end x = k } - i"

definition wf_earley_input :: "(nat \<times> 'a cfg \<times> 'a sentential \<times> 'a bins) set" where
  "wf_earley_input = { 
    (k, cfg, \<omega>, bs) | k cfg \<omega> bs.
      k \<le> length \<omega> \<and>
      length bs = length \<omega> + 1 \<and>
      wf_cfg cfg \<and>
      wf_bins cfg \<omega> bs
  }"

lemma wf_earley_input_Earley_bin_list':
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input" 
  shows "(k, cfg, \<omega>, Earley_bin_list' k cfg \<omega> bs i) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_earley_input_Earley_bin_list:
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input" 
  shows "(k, cfg, \<omega>, Earley_bin_list k cfg \<omega> bs) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_earley_input_Earley_list:
  assumes "wf_cfg cfg"
  assumes "k \<le> length \<omega>"
  shows "(k, cfg, \<omega>, Earley_list k cfg \<omega>) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_earley_input_\<E>arley_list:
  assumes "wf_cfg cfg"
  assumes "k \<le> length \<omega>"
  shows "(k, cfg, \<omega>, \<E>arley_list cfg \<omega>) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

section \<open>Soundness\<close>

lemma Init_list_eq_Init:
  shows "bins_items (Init_list cfg \<omega>) = Init cfg"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Scan_list_sub_Scan:
  assumes "wf_bins cfg \<omega> bs"
  assumes "bins_items bs \<subseteq> I"
  assumes "k < length bs"
  assumes "k < length \<omega>"
  assumes "x \<in> set (items (bs!k))"
  assumes "next_symbol x = Some a"
  shows "set (items (Scan_list k \<omega> a x pre)) \<subseteq> Scan k \<omega> I"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Predict_list_sub_Predict:
  assumes "wf_bins cfg \<omega> bs"
  assumes "bins_items bs \<subseteq> I"
  assumes "k < length bs"
  assumes "x \<in> set (items (bs!k))"
  assumes "next_symbol x = Some X"
  shows "set (items (Predict_list k cfg X)) \<subseteq> Predict k cfg I"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Complete_list_sub_Complete:
  assumes "wf_bins cfg \<omega> bs"
  assumes "bins_items bs \<subseteq> I"
  assumes "k < length bs"
  assumes "x \<in> set (items (bs!k))"
  assumes "next_symbol x = None"
  shows "set (items (Complete_list k x bs red)) \<subseteq> Complete k I"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_bin_list'_sub_Earley_bin:
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input"
  assumes "bins_items bs \<subseteq> I"
  shows "bins_items (Earley_bin_list' k cfg \<omega> bs i) \<subseteq> Earley_bin k cfg \<omega> I"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_bin_list_sub_Earley_bin:
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input"
  assumes "bins_items bs \<subseteq> I"
  shows "bins_items (Earley_bin_list k cfg \<omega> bs) \<subseteq> Earley_bin k cfg \<omega> I"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_list_sub_\<E>:
  assumes "wf_cfg cfg"
  assumes "k \<le> length \<omega>"
  shows "bins_items (Earley_list k cfg \<omega>) \<subseteq> Earley k cfg \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma \<E>arley_list_sub_\<E>arley:
  assumes "wf_cfg cfg" 
  shows "bins_items (\<E>arley_list cfg \<omega>) \<subseteq> \<E>arley cfg \<omega>"
(*<*)
  sorry
(*>*)

section \<open>Completeness\<close>

lemma impossible_complete_item: \<comment>\<open>Detailed\<close>
  assumes "wf_cfg cfg"
  assumes "nonempty_derives cfg"
  assumes "wf_item cfg \<omega> x"
  assumes "sound_item cfg \<omega> x"
  assumes "is_complete x" 
  assumes "item_origin x = k"
  assumes "item_end x = k"
  shows False
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Complete_Un_eq_terminal: \<comment>\<open>Detailed?\<close>
  assumes "wf_cfg cfg"
  assumes "wf_items cfg \<omega> I"
  assumes "wf_item cfg \<omega> x"
  assumes "next_symbol z = Some a"
  assumes "is_terminal cfg a"
  shows "Complete k (I \<union> {x}) = Complete k I"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Complete_Un_eq_nonterminal: \<comment>\<open>Detailed?\<close>
  assumes "wf_cfg cfg"
  assumes "wf_items cfg \<omega> I"
  assumes "sound_items cfg \<omega> I"
  assumes "nonempty_derives cfg"
  assumes "wf_item cfg \<omega> x"
  assumes "item_end x = k"
  assumes "next_symbol z = Some a"
  assumes "is_nonterminal cfg a"
  shows "Complete k (I \<union> {x}) = Complete k I"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Complete_sub_bins_Un_Complete_list: \<comment>\<open>Detailed?\<close>
  assumes "wf_bins cfg \<omega> bs"
  assumes "wf_item cfg \<omega> x"
  assumes "is_complete z"
  assumes "Complete k I \<subseteq> bins_items bs"
  assumes "I \<subseteq> bins_items bs"
  shows "Complete k (I \<union> {x}) \<subseteq> bins_items bs \<union> set (items (Complete_list k x bs red))"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_bin_list'_mono: \<comment>\<open>Omit?\<close>
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input"
  shows "bins_items bs \<subseteq> bins_items (Earley_bin_list' k cfg \<omega> bs i)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_step_sub_Earley_bin_list': \<comment>\<open>Detailed: START WITH THIS\<close>
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_items cfg \<omega> (bins_items bs)"
  assumes "is_sentence cfg \<omega>"
  assumes "nonempty_derives cfg"
  assumes "Earley_step k cfg \<omega> (bins_items_upto bs k i) \<subseteq> bins_items bs"
  shows "Earley_step k cfg \<omega> (bins_items bs) \<subseteq> bins_items (Earley_bin_list' k cfg \<omega> bs i)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_step_sub_Earley_bin_list:
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_items cfg \<omega> (bins_items bs)"
  assumes "is_sentence cfg \<omega>"
  assumes "nonempty_derives cfg"
  assumes "Earley_step k cfg \<omega> (bins_items_upto bs k 0) \<subseteq> bins_items bs"
  shows "Earley_step k cfg \<omega> (bins_items bs) \<subseteq> bins_items (Earley_bin_list k cfg \<omega> bs)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_bin_list'_idem: \<comment>\<open>Detailed: SECOND IS THIS\<close>
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_items cfg \<omega> (bins_items bs)"
  assumes "nonempty_derives cfg"
  assumes "i \<le> j"
  shows "bins_items (Earley_bin_list' k cfg \<omega> (Earley_bin_list' k cfg \<omega> bs i) j) = bins_items (Earley_bin_list' k cfg \<omega> bs i)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_bin_list_idem:
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_items cfg \<omega> (bins_items bs)"
  assumes "nonempty_derives cfg"
  shows "bins_items (Earley_bin_list k cfg \<omega> (Earley_bin_list k cfg \<omega> bs)) = bins_items (Earley_bin_list k cfg \<omega> bs)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_bin_sub_Earley_bin_list:
  assumes "(k, cfg, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_items cfg \<omega> (bins_items bs)"
  assumes "is_sentence cfg \<omega>"
  assumes "nonempty_derives cfg"
  assumes "Earley_step k cfg \<omega> (bins_items_upto bs k 0) \<subseteq> bins_items bs"
  shows "Earley_bin k cfg \<omega> (bins_items bs) \<subseteq> bins_items (Earley_bin_list k cfg \<omega> bs)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_sub_Earley_list:
  assumes "wf_cfg cfg"
  assumes "is_sentence cfg \<omega>"
  assumes "nonempty_derives cfg"
  assumes "k \<le> length \<omega>"
  shows "Earley k cfg \<omega> \<subseteq> bins_items (Earley_list k cfg \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma \<E>arley_sub_\<E>arley_list:
  assumes "wf_cfg cfg"
  assumes "is_sentence cfg \<omega>"
  assumes "nonempty_derives cfg"
  shows "\<E>arley cfg \<omega> \<subseteq> bins_items (\<E>arley_list cfg \<omega>)"
(*<*)
  sorry
(*>*)

section \<open>Main Theorems\<close>

definition recognizing_list :: "'a bins \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "recognizing_list I cfg \<omega> \<equiv> \<exists>x \<in> set (items (I ! length \<omega>)). is_finished cfg \<omega> x"

theorem recognizing_list_iff_recognizing:
  assumes "wf_cfg cfg"
  assumes "is_sentence cfg \<omega>"
  assumes "nonempty_derives cfg"
  shows "recognizing_list (\<E>arley_list cfg \<omega>) cfg \<omega> \<longleftrightarrow> recognizing (\<E>arley cfg \<omega>) cfg \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

corollary correctness_list:
  assumes "wf_cfg cfg"
  assumes "is_sentence cfg \<omega>"
  assumes "nonempty_derives cfg"
  shows "recognizing_list (\<E>arley_list cfg \<omega>) cfg \<omega> \<longleftrightarrow> derives cfg [\<SS> cfg] \<omega>"
(*<*)
  sorry
(*>*)

text\<open>
SNIPPET:

It is this latter possibility, adding items to $S_i$ while representing sets as lists, which causes grief with epsilon-rules.
When Completer processes an item A -> dot, j which corresponds to the epsilon-rule A -> epsiolon, it must
look through $S_j$ for items with the dot before an A. Unfortunately, for epsilon-rule items, j is always
equal to i. Completer is thus looking through the partially constructed set $S_i$. Since implementations
process items in $S_i$ in order, if an item B -> alpha dot A beta, k is added to $S_i$ after Completer
has processed A -> dot, j, Completer will never add B -> \alpha A dot \beta, k to $S_i$. In turn, items
resulting directly and indirectly from B -> \alpha A dot \beta, k will be omitted too. This effectively
prunes protential derivation paths which might cause correct input to be rejected. (EXAMPLE)
Aho \textit{et al} \cite{Aho:1972} propose the stay clam and keep running the Predictor and Completer
in turn until neither has anything more to add. Earley himself suggest to have the Completer note that
the dot needed to be moved over A, then looking for this whenever future items were added to $S_i$.
For efficiency's sake the collection of on-terminals to watch for should be stored in a data structure
which allows fast access. Neither approach is very satisfactory. A third solution \cite{Aycoack:2002}
is a simple modification of the Predictor based on the idea of nullability. A non-terminal A is said to be
nullable if A derives star epsilon. Terminal symbols of course can never be nullable. The nullability of
non-terminals in a grammar may be precomputed using well-known techniques \cite{Appel:2003} \cite{Fischer:2009}
Using this notion the Predictor can be stated as follows: if A -> \alpha dot B \beta, j is in $S_i$,
add B -> dot \gamma, i to $S_i$ for all rules B -> \gamma. If B is nullable, also add A -> \alpha B dot \beta, j
to $S_i$. Explanation why I decided against it. Involves every grammar can be rewritten to not contain epsilon
productions. In other words we eagerly move the dot over a nonterminal if that non-terminal can derive epsilon
and effectivley disappear. The source implements this precomputation by constructing a variant of 
a LR(0) deterministic finite automata (DFA). But for an earley parser we must keep track of which parent
pointers and LR(0) items belong together which leads to complex and inelegant implementations \cite{McLean:1996}.
The source resolves this problem by constructing split epsilon DFAs, but still need to adjust the classical
earley algorithm by adding not only predecessor links but also causal links, and to construct the split
epsilon DFAs not the original grammar but a slightly adjusted equivalent grammar is used that encodes
explicitly information that is crucial to reconstructing derivations, called a grammar in nihilist normal form (NNF)
which might increase the size of the grammar whereas the authors note empirical results that the increase
is quite modest (a factor of 2 at most).

Example:
S -> AAAA, A -> a, A -> E, E -> epsilon, input a
$S_0$ S -> dot AAAA,0, A -> dot a, 0, A -> dot E, 0, E -> dot, 0, A -> E dot, 0, S -> A dot AAA, 0
$S_1$ A -> a dot, 0, S -> A dot AAA, 0, S -> AA dot AA, 0, A -> dot a, 1, A -> dot E, 1, E -> dot, 1, A -> E dot, 1, S -> AAA dot A, 0
\<close>

(*<*)
end
(*>*)
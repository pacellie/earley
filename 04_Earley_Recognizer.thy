(*<*)
theory "04_Earley_Recognizer"
  imports
    "03_Fixpoint_Earley_Recognizer"
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter \<open>Draft\<close>

text\<open>
  \begin{itemize}
    \item introduce auxiliary definitions: filter\_with\_index, pointer, entry in more detail
      most everything else in text \\
    \item overview over earley implementation with linked list and pointers and the mapping into a
      functional setting \\
    \item introduce Init\_it, Scan\_it, Predict\_it and Complete\_it, compare them with the set notation
      and discuss performance improvements (Grammar in more specific form) Why do they all return a list?! \\
    \item discus bin(s)\_upd(s) functions. Why bin\_upds like this -> easier than fold for proofs! \\
    \item discuss pi\_it and why it is a partial function -> only terminates for valid input and foreshadow
      how this is done in isabelle \\
    \item introduce remaining definitions (analog to sets) \\
    \item discuss wf proofs quickly and go into detail about isabelle specifics about termination and
      the custom induction scheme using finiteness \\
    \item outline the approach to proof correctness aka subsumption in both directions \\
    \item discuss list to set proofs
    \item discuss soundness proofs (maybe omit since obvious)
    \item discuss completeness proof focusing on the complete case shortly explaining scan and predict
      which don't change via iteration and order does not matter \\
    \item highlight main theorems
  \end{itemize}
\<close>

chapter\<open>Earley Recognizer Implementation\<close>

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

fun filter_with_index' :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index' _ _ [] = []"
| "filter_with_index' i P (x#xs) = (
    if P x then (x,i) # filter_with_index' (i+1) P xs
    else filter_with_index' (i+1) P xs)"

definition filter_with_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index P xs = filter_with_index' 0 P xs"

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

definition bins_eq_items :: "'a bins \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "bins_eq_items bs0 bs1 \<longleftrightarrow> map items bs0 = map items bs1"

definition bins_items :: "'a bins \<Rightarrow> 'a items" where
  "bins_items bs = \<Union> { set (items (bs ! k)) | k. k < length bs }"

definition bin_items_upto :: "'a bin \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin_items_upto b i = { items b ! j | j. j < i \<and> j < length (items b) }"

definition bins_items_upto :: "'a bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bins_items_upto bs k i = \<Union> { set (items (bs ! l)) | l. l < k } \<union> bin_items_upto (bs ! k) i"

definition wf_bin_items :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> 'a item list \<Rightarrow> bool" where
  "wf_bin_items cfg inp k xs \<equiv> \<forall>x \<in> set xs. wf_item cfg inp x \<and> item_end x = k"

definition wf_bin :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> 'a bin \<Rightarrow> bool" where
  "wf_bin cfg inp k b \<equiv> distinct (items b) \<and> wf_bin_items cfg inp k (items b)"

definition wf_bins :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "wf_bins cfg inp bs \<equiv> \<forall>k < length bs. wf_bin cfg inp k (bs ! k)"

definition nonempty_derives :: "'a cfg \<Rightarrow> bool" where
  "nonempty_derives cfg \<equiv> \<forall>N. N \<in> set (\<NN> cfg) \<longrightarrow> \<not> derives cfg [N] []"

definition Init_list :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins" where
  "Init_list cfg inp \<equiv> 
    let rs = filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg) in
    let b0 = map (\<lambda>r. (Entry (init_item r 0) Null)) rs in
    let bs = replicate (length inp + 1) ([]) in
    bs[0 := b0]"

definition Scan_list :: "nat \<Rightarrow> 'a sentential \<Rightarrow> 'a  \<Rightarrow> 'a item \<Rightarrow> nat \<Rightarrow> 'a entry list" where
  "Scan_list k inp a x pre \<equiv>
    if inp!k = a then
      let x' = inc_item x (k+1) in
      [Entry x' (Pre pre)]
    else []"

definition Predict_list :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a \<Rightarrow> 'a entry list" where
  "Predict_list k cfg X \<equiv>
    let rs = filter (\<lambda>r. rule_head r = X) (\<RR> cfg) in
    map (\<lambda>r. (Entry (init_item r k) Null)) rs"

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

partial_function (tailrec) E_list' :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a bins" where
  "E_list' k cfg inp bs i = (
    if i \<ge> length (items (bs ! k)) then bs
    else
      let x = items (bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow>
            if is_terminal cfg a then
              if k < length inp then bins_upd bs (k+1) (Scan_list k inp a x i)
              else bs
            else bins_upd bs k (Predict_list k cfg a)
        | None \<Rightarrow> bins_upd bs k (Complete_list k x bs i)
      in E_list' k cfg inp bs' (i+1))"

definition E_list :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins \<Rightarrow> 'a bins" where
  "E_list k cfg inp bs = E_list' k cfg inp bs 0"

fun \<E>_list :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins" where
  "\<E>_list 0 cfg inp = E_list 0 cfg inp (Init_list cfg inp)"
| "\<E>_list (Suc n) cfg inp = E_list (Suc n) cfg inp (\<E>_list n cfg inp)"

definition earley_list :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a bins" where
  "earley_list cfg inp = \<E>_list (length inp) cfg inp"

section \<open>Wellformedness\<close>

lemma wf_bin_bin_upd:
  assumes "wf_bin cfg inp k b" "wf_item cfg inp (item e)" "item_end (item e) = k"
  shows "wf_bin cfg inp k (bin_upd e b)"
(*<*)
  sorry
(*>*)

lemma wf_bin_bin_upds:
  assumes "wf_bin cfg inp k b" "distinct (items es)"
  assumes "\<forall>x \<in> set (items es). wf_item cfg inp x \<and> item_end x = k"
  shows "wf_bin cfg inp k (bin_upds es b)"
(*<*)
  sorry
(*>*)

lemma wf_bins_bins_upd:
  assumes "wf_bins cfg inp bs" "distinct (items es)"
  assumes "\<forall>x \<in> set (items es). wf_item cfg inp x \<and> item_end x = k"
  shows "wf_bins cfg inp (bins_upd bs k es)"
(*<*)
  sorry
(*>*)

lemma wf_bins_Init_list:
  assumes "wf_cfg cfg"
  shows "wf_bins cfg inp (Init_list cfg inp)"
(*<*)
  sorry
(*>*)

lemma wf_bins_Scan_list:
  assumes "wf_bins cfg inp bs" "k < length bs" "x \<in> set (items (bs!k))" "k < length inp" "next_symbol x \<noteq> None"
  shows "\<forall>y \<in> set (items (Scan_list k inp a x pre)). wf_item cfg inp y \<and> item_end y = k+1"
(*<*)
  sorry
(*>*)

lemma wf_bins_Predict_list:
  assumes "wf_bins cfg inp bs" "k < length bs" "k \<le> length inp" "wf_cfg cfg"
  shows "\<forall>y \<in> set (items (Predict_list k cfg X)). wf_item cfg inp y \<and> item_end y = k"
(*<*)
  sorry
(*>*)

lemma wf_bins_Complete_list:
  assumes "wf_bins cfg inp bs" "k < length bs" "y \<in> set (items (bs!k))"
  shows "\<forall>x \<in> set (items (Complete_list k y bs red)). wf_item cfg inp x \<and> item_end x = k"
(*<*)
  sorry
(*>*)

fun earley_measure :: "nat \<times> 'a cfg \<times> 'a sentential \<times> 'a bins \<Rightarrow> nat \<Rightarrow> nat" where
  "earley_measure (k, cfg, inp, bs) i = card { x | x. wf_item cfg inp x \<and> item_end x = k } - i"

definition wf_earley_input :: "(nat \<times> 'a cfg \<times> 'a sentential \<times> 'a bins) set" where
  "wf_earley_input = { 
    (k, cfg, inp, bs) | k cfg inp bs.
      k \<le> length inp \<and>
      length bs = length inp + 1 \<and>
      wf_cfg cfg \<and>
      wf_bins cfg inp bs
  }"

lemma wf_earley_input_Init_list:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, Init_list cfg inp) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

lemma wf_earley_input_Complete_list:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input" "\<not> length (items (bs!k)) \<le> i"
  assumes "x = items (bs!k)!i" "next_symbol x = None"
  shows "(k, cfg, inp, bins_upd bs k (Complete_list k x bs red)) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

lemma wf_earley_input_Scan_list:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input" "\<not> length (items (bs!k)) \<le> i"
  assumes "x = items (bs!k)!i" "next_symbol x = Some a"
  assumes "is_terminal cfg a" "k < length inp"
  shows "(k, cfg, inp, bins_upd bs (k+1) (Scan_list k inp a x pre)) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

lemma wf_earley_input_Predict_list:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input" "\<not> length (items (bs!k)) \<le> i"
  assumes "x = items (bs!k)!i" "next_symbol x = Some a" "\<not> is_terminal cfg a"
  shows "(k, cfg, inp, bins_upd bs k (Predict_list k cfg a)) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

lemma wf_earley_input_E_list':
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input" 
  shows "(k, cfg, inp, E_list' k cfg inp bs i) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

lemma wf_earley_input_E_list:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input" 
  shows "(k, cfg, inp, E_list k cfg inp bs) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

lemma wf_earley_input_\<E>_list:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, \<E>_list k cfg inp) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

lemma wf_earley_input_earley_list:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, earley_list cfg inp) \<in> wf_earley_input"
(*<*)
  sorry
(*>*)

lemma wf_bins_E_list':
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input" 
  shows "wf_bins cfg inp (E_list' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma wf_bins_E_list:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input" 
  shows "wf_bins cfg inp (E_list k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma wf_bins_\<E>_list:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "wf_bins cfg inp (\<E>_list k cfg inp)"
(*<*)
  sorry
(*>*)

lemma wf_bins_earley_list:
  assumes "wf_cfg cfg" 
  shows "wf_bins cfg inp (earley_list cfg inp)"
(*<*)
  sorry
(*>*)

section \<open>Soundness\<close>

lemma Init_list_eq_Init:
  shows "bins_items (Init_list cfg inp) = Init cfg"
(*<*)
  sorry
(*>*)

lemma Scan_list_sub_Scan:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))"
  assumes "k < length bs" "k < length inp" "next_symbol x = Some a"
  shows "set (items (Scan_list k inp a x pre)) \<subseteq> Scan k inp I"
(*<*)
  sorry
(*>*)

lemma Predict_list_sub_Predict:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol x = Some X"
  shows "set (items (Predict_list k cfg X)) \<subseteq> Predict k cfg I"
(*<*)
  sorry
(*>*)

lemma Complete_list_sub_Complete:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "y \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol y = None"
  shows "set (items (Complete_list k y bs red)) \<subseteq> Complete k I"
(*<*)
  sorry
(*>*)

lemma E_list'_sub_E:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  assumes "bins_items bs \<subseteq> I"
  shows "bins_items (E_list' k cfg inp bs i) \<subseteq> E k cfg inp I"
(*<*)
  sorry
(*>*)

lemma E_list_sub_E:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  assumes "bins_items bs \<subseteq> I"
  shows "bins_items (E_list k cfg inp bs) \<subseteq> E k cfg inp I"
(*<*)
  sorry
(*>*)

lemma \<E>_list_sub_\<E>:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "bins_items (\<E>_list k cfg inp) \<subseteq> \<E> k cfg inp"
(*<*)
  sorry
(*>*)

lemma earley_list_sub_earley:
  assumes "wf_cfg cfg" 
  shows "bins_items (earley_list cfg inp) \<subseteq> earley cfg inp"
(*<*)
  sorry
(*>*)

section \<open>Completeness\<close>

lemma impossible_complete_item:
  assumes "wf_cfg cfg" "wf_item cfg inp x" "sound_item cfg inp x"
  assumes "is_complete x"  "item_origin x = k" "item_end x = k" "nonempty_derives cfg"
  shows False
(*<*)
  sorry
(*>*)

lemma Complete_Un_eq_terminal:
  assumes "next_symbol z = Some a" "is_terminal cfg a" "wf_items cfg inp I" "wf_item cfg inp z" "wf_cfg cfg"
  shows "Complete k (I \<union> {z}) = Complete k I"
(*<*)
  sorry
(*>*)

lemma Complete_Un_eq_nonterminal:
  assumes "next_symbol z = Some a" "is_nonterminal cfg a" "sound_items cfg inp I" "item_end z = k"
  assumes "wf_items cfg inp I" "wf_item cfg inp z" "wf_cfg cfg" "nonempty_derives cfg"
  shows "Complete k (I \<union> {z}) = Complete k I"
(*<*)
  sorry
(*>*)

lemma Complete_sub_bins_Un_Complete_list:
  assumes "Complete k I \<subseteq> bins_items bs" "I \<subseteq> bins_items bs" "is_complete z" "wf_bins cfg inp bs" "wf_item cfg inp z"
  shows "Complete k (I \<union> {z}) \<subseteq> bins_items bs \<union> set (items (Complete_list k z bs red))"
(*<*)
  sorry
(*>*)

lemma E_list'_mono:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  shows "bins_items bs \<subseteq> bins_items (E_list' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma E_step_sub_E_list':
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  assumes "E_step k cfg inp (bins_items_upto bs k i) \<subseteq> bins_items bs"
  assumes "sound_items cfg inp (bins_items bs)" "is_sentence cfg inp" "nonempty_derives cfg"
  shows "E_step k cfg inp (bins_items bs) \<subseteq> bins_items (E_list' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma E_step_sub_E_list:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  assumes "E_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs"
  assumes "sound_items cfg inp (bins_items bs)" "is_sentence cfg inp" "nonempty_derives cfg"
  shows "E_step k cfg inp (bins_items bs) \<subseteq> bins_items (E_list k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma E_list'_bins_items_eq:
  assumes "(k, cfg, inp, as) \<in> wf_earley_input"
  assumes "bins_eq_items as bs" "wf_bins cfg inp as"
  shows "bins_eq_items (E_list' k cfg inp as i) (E_list' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma E_list'_idem:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  assumes "i \<le> j" "sound_items cfg inp (bins_items bs)" "nonempty_derives cfg"
  shows "bins_items (E_list' k cfg inp (E_list' k cfg inp bs i) j) = bins_items (E_list' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma E_list_idem:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  assumes "sound_items cfg inp (bins_items bs)" "nonempty_derives cfg"
  shows "bins_items (E_list k cfg inp (E_list k cfg inp bs)) = bins_items (E_list k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma funpower_E_step_sub_E_list:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  assumes "E_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs" "sound_items cfg inp (bins_items bs)"
  assumes "is_sentence cfg inp" "nonempty_derives cfg"
  shows "funpower (E_step k cfg inp) n (bins_items bs) \<subseteq> bins_items (E_list k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma E_sub_E_list:
  assumes "(k, cfg, inp, bs) \<in> wf_earley_input"
  assumes "E_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs" "sound_items cfg inp (bins_items bs)"
  assumes "is_sentence cfg inp" "nonempty_derives cfg"
  shows "E k cfg inp (bins_items bs) \<subseteq> bins_items (E_list k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma \<E>_sub_\<E>_list:
  assumes "k \<le> length inp" "wf_cfg cfg"
  assumes "is_sentence cfg inp" "nonempty_derives cfg"
  shows "\<E> k cfg inp \<subseteq> bins_items (\<E>_list k cfg inp)"
(*<*)
  sorry
(*>*)

lemma earley_sub_earley_list:
  assumes "wf_cfg cfg" "is_sentence cfg inp" "nonempty_derives cfg"
  shows "earley cfg inp \<subseteq> bins_items (earley_list cfg inp)"
(*<*)
  sorry
(*>*)

section \<open>Main Theorem\<close>

definition recognizing_list :: "'a bins \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "recognizing_list I cfg inp \<equiv> \<exists>x \<in> set (items (I ! length inp)). is_finished cfg inp x"

theorem recognizing_list_iff_earley_recognized:
  assumes "wf_cfg cfg" "is_sentence cfg inp" "nonempty_derives cfg"
  shows "recognizing_list (earley_list cfg inp) cfg inp \<longleftrightarrow> recognizing (earley cfg inp) cfg inp"
(*<*)
  sorry
(*>*)

corollary correctness_list:
  assumes "wf_cfg cfg" "is_sentence cfg inp" "nonempty_derives cfg"
  shows "recognizing_list (earley_list cfg inp) cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
(*<*)
  sorry
(*>*)

(*<*)
end
(*>*)
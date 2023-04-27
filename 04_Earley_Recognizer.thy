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

definition wf_bin_items :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a item list \<Rightarrow> bool" where
  "wf_bin_items cfg inp k xs = (\<forall>x \<in> set xs. wf_item cfg inp x \<and> item_end x = k)"

definition wf_bin :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a bin \<Rightarrow> bool" where
  "wf_bin cfg inp k b \<longleftrightarrow> distinct (items b) \<and> wf_bin_items cfg inp k (items b)"

definition wf_bins :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "wf_bins cfg inp bs \<longleftrightarrow> (\<forall>k < length bs. wf_bin cfg inp k (bs ! k))"

definition nonempty_derives :: "'a cfg \<Rightarrow> bool" where
  "nonempty_derives cfg = (\<forall>N. N \<in> set (\<NN> cfg) \<longrightarrow> \<not> derives cfg [N] [])"

definition Init_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "Init_it cfg inp = (
    let rs = filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg) in
    let b0 = map (\<lambda>r. (Entry (init_item r 0) Null)) rs in
    let bs = replicate (length inp + 1) ([]) in
    bs[0 := b0])"

definition Scan_it :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a  \<Rightarrow> 'a item \<Rightarrow> nat \<Rightarrow> 'a entry list" where
  "Scan_it k inp a x pre = (
    if inp!k = a then
      let x' = inc_item x (k+1) in
      [Entry x' (Pre pre)]
    else [])"

definition Predict_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a \<Rightarrow> 'a entry list" where
  "Predict_it k cfg X = (
    let rs = filter (\<lambda>r. rule_head r = X) (\<RR> cfg) in
    map (\<lambda>r. (Entry (init_item r k) Null)) rs)"

definition Complete_it :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a entry list" where
  "Complete_it k y bs red = (
    let orig = bs ! (item_origin y) in
    let is = filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items orig) in
    map (\<lambda>(x, pre). (Entry (inc_item x k) (PreRed (item_origin y, pre, red) []))) is)"

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

partial_function (tailrec) \<pi>_it' :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a bins" where
  "\<pi>_it' k cfg inp bs i = (
    if i \<ge> length (items (bs ! k)) then bs
    else
      let x = items (bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow>
            if is_terminal cfg a then
              if k < length inp then bins_upd bs (k+1) (Scan_it k inp a x i)
              else bs
            else bins_upd bs k (Predict_it k cfg a)
        | None \<Rightarrow> bins_upd bs k (Complete_it k x bs i)
      in \<pi>_it' k cfg inp bs' (i+1))"

definition \<pi>_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a bins" where
  "\<pi>_it k cfg inp bs = \<pi>_it' k cfg inp bs 0"

fun \<I>_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "\<I>_it 0 cfg inp = \<pi>_it 0 cfg inp (Init_it cfg inp)"
| "\<I>_it (Suc n) cfg inp = \<pi>_it (Suc n) cfg inp (\<I>_it n cfg inp)"

definition \<II>_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "\<II>_it cfg inp = \<I>_it (length inp) cfg inp"

section \<open>Wellformedness\<close>

lemma distinct_bin_upd:
  "distinct (items b) \<Longrightarrow> distinct (items (bin_upd e b))"
(*<*)
  sorry
(*>*)

lemma distinct_bin_upds:
  "distinct (items b)  \<Longrightarrow> distinct (items (bin_upds es b))"
(*<*)
  sorry
(*>*)

lemma distinct_bins_upd:
  "distinct (items (bs ! k)) \<Longrightarrow> distinct (items (bins_upd bs k ips ! k))"
(*<*)
  sorry
(*>*)

lemma distinct_Scan_it:
  "distinct (items (Scan_it k inp a x pre))"
  sorry

lemma distinct_Predict_it:
  "wf_cfg cfg \<Longrightarrow> distinct (items (Predict_it k cfg X))"
(*<*)
  sorry
(*>*)

lemma distinct_Complete_it:
  assumes "wf_bins cfg inp bs" "item_origin y < length bs"
  shows "distinct (items (Complete_it k y bs red))"
(*<*)
  sorry
(*>*)

lemma wf_bin_bin_upd:
  assumes "wf_bin cfg inp k b" "wf_item cfg inp (item e) \<and> item_end (item e) = k"
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

lemma wf_bins_Init_it:
  assumes "wf_cfg cfg"
  shows "wf_bins cfg inp (Init_it cfg inp)"
(*<*)
  sorry
(*>*)

lemma wf_bins_Scan_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "x \<in> set (items (bs ! k))" "k < length inp" "next_symbol x \<noteq> None"
  shows "\<forall>y \<in> set (items (Scan_it k inp a x pre)). wf_item cfg inp y \<and> item_end y = (k+1)"
(*<*)
  sorry
(*>*)

lemma wf_bins_Predict_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "k \<le> length inp" "wf_cfg cfg"
  shows "\<forall>y \<in> set (items (Predict_it k cfg X)). wf_item cfg inp y \<and> item_end y = k"
(*<*)
  sorry
(*>*)

lemma wf_bins_Complete_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "y \<in> set (items (bs ! k))"
  shows "\<forall>x \<in> set (items (Complete_it k y bs red)). wf_item cfg inp x \<and> item_end x = k"
(*<*)
  sorry
(*>*)


definition wellformed_bins :: "(nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins) set" where
  "wellformed_bins = { 
    (k, cfg, inp, bs) | k cfg inp bs.
      k \<le> length inp \<and>
      length bs = length inp + 1 \<and>
      wf_cfg cfg \<and>
      wf_bins cfg inp bs
  }"

typedef 'a wf_bins = "wellformed_bins::(nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins) set"
 (*<*)
  sorry
 (*>*)

lemma wellformed_bins_Init_it:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, Init_it cfg inp) \<in> wellformed_bins"
(*<*)
  sorry
(*>*)

lemma wellformed_bins_Complete_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = None"
  shows "(k, cfg, inp, bins_upd bs k (Complete_it k x bs red)) \<in> wellformed_bins"
(*<*)
  sorry
(*>*)

lemma wellformed_bins_Scan_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = Some a"
  assumes "is_terminal cfg a" "k < length inp"
  shows "(k, cfg, inp, bins_upd bs (k+1) (Scan_it k inp a x pre)) \<in> wellformed_bins"
(*<*)
  sorry
(*>*)

lemma wellformed_bins_Predict_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = Some a" "\<not> is_terminal cfg a"
  shows "(k, cfg, inp, bins_upd bs k (Predict_it k cfg a)) \<in> wellformed_bins"
(*<*)
  sorry
(*>*)

fun earley_measure :: "nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins \<Rightarrow> nat \<Rightarrow> nat" where
  "earley_measure (k, cfg, inp, bs) i = card { x | x. wf_item cfg inp x \<and> item_end x = k } - i"

lemma \<pi>_it'_induct:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes base: "\<And>k cfg inp bs i. i \<ge> length (items (bs ! k)) \<Longrightarrow> P k cfg inp bs i"
  assumes complete: "\<And>k cfg inp bs i x. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = None \<Longrightarrow> P k cfg inp (bins_upd bs k (Complete_it k x bs i)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes scan: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal cfg a \<Longrightarrow> k < length inp \<Longrightarrow> 
            P k cfg inp (bins_upd bs (k+1) (Scan_it k inp a x i)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes pass: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal cfg a \<Longrightarrow> \<not> k < length inp \<Longrightarrow>
            P k cfg inp bs (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes predict: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> \<not> is_terminal cfg a \<Longrightarrow> 
            P k cfg inp (bins_upd bs k (Predict_it k cfg a)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  shows "P k cfg inp bs i"
(*<*)
  sorry
(*>*)

lemma wellformed_bins_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "(k, cfg, inp, \<pi>_it' k cfg inp bs i) \<in> wellformed_bins"
(*<*)
  sorry
(*>*)

lemma wellformed_bins_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "(k, cfg, inp, \<pi>_it k cfg inp bs) \<in> wellformed_bins"
(*<*)
  sorry
(*>*)

lemma wellformed_bins_\<I>_it:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
(*<*)
  sorry
(*>*)

lemma wellformed_bins_\<II>_it:
  "k \<le> length inp \<Longrightarrow> wf_cfg cfg \<Longrightarrow> (k, cfg, inp, \<II>_it cfg inp) \<in> wellformed_bins"
(*<*)
  sorry
(*>*)

lemma wf_bins_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "wf_bins cfg inp (\<pi>_it' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma wf_bins_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "wf_bins cfg inp (\<pi>_it k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma wf_bins_\<I>_it:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "wf_bins cfg inp (\<I>_it k cfg inp)"
(*<*)
  sorry
(*>*)

lemma wf_bins_\<II>_it:
  "wf_cfg cfg \<Longrightarrow> wf_bins cfg inp (\<II>_it cfg inp)"
(*<*)
  sorry
(*>*)

section \<open>List to set\<close>

lemma Init_it_eq_Init:
  "bins_items (Init_it cfg inp) = Init cfg"
(*<*)
  sorry
(*>*)

lemma Scan_it_sub_Scan:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))"
  assumes "k < length bs" "k < length inp"
  assumes "next_symbol x = Some a"
  shows "set (items (Scan_it k inp a x pre)) \<subseteq> Scan k inp I"
(*<*)
  sorry
(*>*)

lemma Predict_it_sub_Predict:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol x = Some X"
  shows "set (items (Predict_it k cfg X)) \<subseteq> Predict k cfg I"
(*<*)
  sorry
(*>*)

lemma Complete_it_sub_Complete:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "y \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol y = None"
  shows "set (items (Complete_it k y bs red)) \<subseteq> Complete k I"
(*<*)
  sorry
(*>*)

lemma \<pi>_it'_sub_\<pi>:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "bins_items bs \<subseteq> I"
  shows "bins_items (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp I"
(*<*)
  sorry
(*>*)

lemma \<pi>_it_sub_\<pi>:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "bins_items bs \<subseteq> I"
  shows "bins_items (\<pi>_it k cfg inp bs) \<subseteq> \<pi> k cfg inp I"
(*<*)
  sorry
(*>*)

lemma \<I>_it_sub_\<I>:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "bins_items (\<I>_it k cfg inp) \<subseteq> \<I> k cfg inp"
(*<*)
  sorry
(*>*)

lemma \<II>_it_sub_\<II>:
  "wf_cfg cfg \<Longrightarrow> bins_items (\<II>_it cfg inp) \<subseteq> \<II> cfg inp"
(*<*)
  sorry
(*>*)

section \<open>Soundness\<close>

lemma sound_Scan_it:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs" "k < length inp"
  assumes "next_symbol x = Some a" "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (items (Scan_it k inp a x i)))"
(*<*)
  sorry
(*>*)

lemma sound_Predict_it:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol x = Some X" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (items (Predict_it k cfg X)))"
(*<*)
  sorry
(*>*)

lemma sound_Complete_it:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "y \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol y = None" "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (items (Complete_it k y bs i)))"
(*<*)
  sorry
(*>*)

lemma sound_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins_items bs)"
  shows "sound_items cfg inp (bins_items (\<pi>_it' k cfg inp bs i))"
(*<*)
  sorry
(*>*)

lemma sound_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins_items bs)"
  shows "sound_items cfg inp (bins_items (\<pi>_it k cfg inp bs))"
(*<*)
  sorry
(*>*)

section \<open>Set to list\<close>

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

lemma Complete_sub_bins_Un_Complete_it:
  assumes "Complete k I \<subseteq> bins_items bs" "I \<subseteq> bins_items bs" "is_complete z" "wf_bins cfg inp bs" "wf_item cfg inp z"
  shows "Complete k (I \<union> {z}) \<subseteq> bins_items bs \<union> set (items (Complete_it k z bs red))"
(*<*)
  sorry
(*>*)

lemma \<pi>_it'_mono:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "bins_items bs \<subseteq> bins_items (\<pi>_it' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma \<pi>_step_sub_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_items_upto bs k i) \<subseteq> bins_items bs"
  assumes "sound_items cfg inp (bins_items bs)" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi>_step k cfg inp (bins_items bs) \<subseteq> bins_items (\<pi>_it' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma \<pi>_step_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs"
  assumes "sound_items cfg inp (bins_items bs)" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi>_step k cfg inp (bins_items bs) \<subseteq> bins_items (\<pi>_it k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma \<pi>_it'_bins_items_eq:
  assumes "(k, cfg, inp, as) \<in> wellformed_bins"
  assumes "bins_eq_items as bs" "wf_bins cfg inp as"
  shows "bins_eq_items (\<pi>_it' k cfg inp as i) (\<pi>_it' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma \<pi>_it'_idem:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "i \<le> j" "sound_items cfg inp (bins_items bs)" "nonempty_derives cfg"
  shows "bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j) = bins_items (\<pi>_it' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma \<pi>_it_idem:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins_items bs)" "nonempty_derives cfg"
  shows "bins_items (\<pi>_it k cfg inp (\<pi>_it k cfg inp bs)) = bins_items (\<pi>_it k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma funpower_\<pi>_step_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs" "sound_items cfg inp (bins_items bs)"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "funpower (\<pi>_step k cfg inp) n (bins_items bs) \<subseteq> bins_items (\<pi>_it k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma \<pi>_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs" "sound_items cfg inp (bins_items bs)"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi> k cfg inp (bins_items bs) \<subseteq> bins_items (\<pi>_it k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma \<I>_sub_\<I>_it:
  assumes "k \<le> length inp" "wf_cfg cfg"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "\<I> k cfg inp \<subseteq> bins_items (\<I>_it k cfg inp)"
(*<*)
  sorry
(*>*)

lemma \<II>_sub_\<II>_it:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<II> cfg inp \<subseteq> bins_items (\<II>_it cfg inp)"
(*<*)
  sorry
(*>*)

section \<open>Main Theorem\<close>

definition earley_recognized_it :: "'a bins \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "earley_recognized_it I cfg inp = (\<exists>x \<in> set (items (I ! length inp)). is_finished cfg inp x)"

theorem earley_recognized_it_iff_earley_recognized:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "earley_recognized_it (\<II>_it cfg inp) cfg inp \<longleftrightarrow> earley_recognized (\<II> cfg inp) cfg inp"
(*<*)
  sorry
(*>*)

corollary correctness_list:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "earley_recognized_it (\<II>_it cfg inp) cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
(*<*)
  sorry
(*>*)

(*<*)
end
(*>*)
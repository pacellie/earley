theory Earley
  imports
    "HOL-Library.While_Combinator"
    LocalLexing.ListTools \<comment>\<open>Use\<close>
    LocalLexing.InductRules \<comment>\<open>Use\<close>
    LocalLexing.CFG \<comment>\<open>Use\<close>
    LocalLexing.Derivations \<comment>\<open>Use\<close>
    LocalLexing.LocalLexing \<comment>\<open>Done\<close>
    LocalLexing.LLEarleyParsing \<comment>\<open>Done\<close>
    LocalLexing.Validity \<comment>\<open>Done\<close>
    LocalLexing.TheoremD2 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD4 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD5 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD6 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD7 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD8 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD9 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.Ladder \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD10 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD11 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD12 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD13 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD14 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.PathLemmas \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.MainTheorems \<comment>\<open>TODO: Extract relevant lemmas?\<close>
begin

declare [[names_short]]

\<comment>\<open>TODO: Cleanup\<close>

section \<open>Auxiliary lemmas\<close>

lemma (in CFG) is_sentence_simp:
  "is_sentence s \<longleftrightarrow> (\<forall>x \<in> set s. is_symbol x)"
  unfolding is_sentence_def by (simp add: list_all_iff)

lemma (in CFG) is_word_simp:
  "is_word s \<longleftrightarrow> (\<forall>x \<in> set s. is_terminal x)"
  unfolding is_word_def by (simp add: list_all_iff)

section \<open>List slices\<close>

\<comment>\<open>slice a b xs: a is inclusive, b is exclusive\<close>
fun slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slice _ _ [] = []"
| "slice _ 0 (x#xs) = []"
| "slice 0 (Suc b) (x#xs) = x # slice 0 b xs"
| "slice (Suc a) (Suc b) (x#xs) = slice a b xs"

lemma slice_drop_take:
  "slice a b xs = drop a (take b xs)"
  by (induction a b xs rule: slice.induct) auto

lemma slice_append_aux:
  "Suc b \<le> c \<Longrightarrow> slice (Suc b) c (x # xs) = slice b (c-1) xs"
  using Suc_le_D by fastforce

lemma slice_append:
  "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> slice a b xs @ slice b c xs = slice a c xs"
  apply (induction a b xs arbitrary: c rule: slice.induct)
  apply (auto simp: slice_append_aux)
  using Suc_le_D by fastforce

lemma slice_append_nth:
  "a \<le> b \<Longrightarrow> b < length xs \<Longrightarrow> slice a b xs @ [xs!b] = slice a (b+1) xs"
  by (auto simp: slice_drop_take take_Suc_conv_app_nth)

lemma slice_empty:
  "b \<le> a \<Longrightarrow> slice a b xs = []"
  by (simp add: slice_drop_take)

lemma slice_id[simp]:
  "slice 0 (length xs) xs = xs"
  by (simp add: slice_drop_take)

lemma slice_subset:
  "set (slice a b xs) \<subseteq> set xs"
  using slice_drop_take by (metis in_set_dropD in_set_takeD subsetI)

section \<open>Earley recognizer\<close>

subsection \<open>Earley items, bin(s), state\<close>

definition rule_head :: "rule \<Rightarrow> symbol" where
  "rule_head = fst"

definition rule_body :: "rule \<Rightarrow> symbol list" where
  "rule_body = snd"

datatype item = 
  Item 
    (item_rule: rule) 
    (item_dot : nat) 
    (item_origin : nat)

type_synonym items = "item list"

definition item_rule_head :: "item \<Rightarrow> symbol" where
  "item_rule_head x = rule_head (item_rule x)"

definition item_rule_body :: "item \<Rightarrow> sentence" where
  "item_rule_body x = rule_body (item_rule x)"

definition item_\<alpha> :: "item \<Rightarrow> sentence" where
  "item_\<alpha> x = take (item_dot x) (item_rule_body x)"

definition item_\<beta> :: "item \<Rightarrow> sentence" where 
  "item_\<beta> x = drop (item_dot x) (item_rule_body x)"

definition init_item :: "rule \<Rightarrow> nat \<Rightarrow> item" where
  "init_item r k = Item r 0 k"

definition is_complete :: "item \<Rightarrow> bool" where
  "is_complete x = (item_dot x \<ge> length (item_rule_body x))"

definition (in CFG) is_finished :: "item \<Rightarrow> bool" where
  "is_finished x = (item_rule_head x = \<SS> \<and> item_origin x = 0 \<and> is_complete x)"

definition next_symbol :: "item \<Rightarrow> symbol option" where
  "next_symbol x = (if is_complete x then None else Some ((item_rule_body x) ! (item_dot x)))"

definition inc_item :: "item \<Rightarrow> item" where
  "inc_item x = Item (item_rule x) (item_dot x + 1) (item_origin x)"

lemmas item_defs = item_rule_head_def item_rule_body_def item_\<alpha>_def item_\<beta>_def rule_head_def rule_body_def

datatype bin =
  Bin
    (items: items)

definition bin_size :: "bin \<Rightarrow> nat" where
  "bin_size b = length (items b)"

definition bin_append :: "bin \<Rightarrow> item list \<Rightarrow> bin" where
  "bin_append b is = Bin (items b @ (filter (\<lambda>i. i \<notin> set (items b)) is))"

type_synonym bins = "bin list"

definition bins_append :: "bins \<Rightarrow> nat \<Rightarrow> item list \<Rightarrow> bins" where
  "bins_append bs k is = bs[k := bin_append (bs!k) is]"

lemmas bin_defs = bins_append_def bin_append_def bin_size_def

datatype state =
  State
    (bins: bins)
    (bin: nat) \<comment>\<open>active bin index\<close>
    (index: nat) \<comment>\<open>active item index\<close>

subsection \<open>Earley algorithm\<close>

locale Earley = CFG +
  fixes doc :: "symbol list"
  fixes rules :: "rule list"
  assumes valid_doc: "set doc \<subseteq> \<TT>"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
begin

definition scan :: "symbol \<Rightarrow> item \<Rightarrow> bins \<Rightarrow> nat \<Rightarrow> bins" where
  "scan x item bs k = (
    if k < length doc \<and> doc!k = x then
      let item' = inc_item item in
      bins_append bs (k+1) [item']
    else bs)"

definition predict :: "symbol \<Rightarrow> bins \<Rightarrow> nat \<Rightarrow> bins" where
  "predict X bs k = (
    let rules' = filter (\<lambda>rule. rule_head rule = X) rules in
    let items = map (\<lambda>rule. init_item rule k) rules' in
    bins_append bs k items)"

definition complete :: "item \<Rightarrow> bins \<Rightarrow> nat \<Rightarrow> bins" where
  "complete item bs k = (
    let origin_bin = bs!(item_origin item) in
    let items = filter (\<lambda>item'. next_symbol item' = Some (item_rule_head item)) (items origin_bin) in
    bins_append bs k (map (\<lambda>item. inc_item item) items))"

definition earley_step :: "state \<Rightarrow> state" where
  "earley_step s = (
    if index s = bin_size ((bins s)!(bin s)) then
      (State (bins s) (bin s + 1) 0)
    else
      let item = (items ((bins s)!(bin s)))!index s in
      let bins = 
        case next_symbol item of
          Some x \<Rightarrow>
            if is_terminal x then scan x item (bins s) (bin s)
            else predict x (bins s) (bin s)
        | None \<Rightarrow> complete item (bins s) (bin s)
      in State bins (bin s) (index s + 1))"


(*
while_option :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option"
while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
REMARK: state option \<Rightarrow> state option
*)
function earley :: "state \<Rightarrow> state" where \<comment>\<open>TODO: Termination, REMARK: use while combinator\<close>
  "earley s = (
    if bin s < length (bins s) then
      earley (earley_step s)
    else
      s)"
  by pat_completeness simp
termination
  sorry

definition init_rules :: "rule list" where
  "init_rules = filter (\<lambda>rule. rule_head rule = \<SS>) rules"

definition init_items :: "item list" where
  "init_items = map (\<lambda>rule. init_item rule 0) init_rules"

definition init_bins :: "bins" where
  "init_bins = bins_append (replicate (length doc + 1) (Bin [])) 0 init_items"

definition init_state :: "state" where
  "init_state = State init_bins 0 0"

definition earley_recognized :: "bool" where
  "earley_recognized \<longleftrightarrow> (
    let last_bin = bins (earley init_state) ! length doc in
    \<exists>item \<in> set (items last_bin). is_finished item)"
    
subsection \<open>Termination\<close>

lemma earley_step_fixpoint':
  "earley_step (earley_step s) = s \<Longrightarrow> earley_step s = s"
  unfolding earley_step_def
  apply (auto simp: Let_def split!: option.splits if_splits)
  apply (metis Suc_n_not_le_n n_not_Suc_n nat_le_linear le_SucI le_refl state.sel(2,3))+
  done

lemma earley_step_fixpoint:
  "(earley_step s = s) \<longleftrightarrow> earley_step (earley_step s) = s"
  using earley_step_fixpoint' by auto

subsection \<open>Wellformedness\<close>

definition wf_item :: "item \<Rightarrow> bool" where 
  "wf_item item \<longleftrightarrow>
    item_rule item \<in> \<RR> \<and>
    item_origin item \<le> length doc \<and>
    item_dot item \<le> length (item_rule_body item)"

definition wf_bin :: "nat \<Rightarrow> bin \<Rightarrow> bool" where
  "wf_bin k b \<longleftrightarrow>
    distinct (items b) \<and>
    (\<forall>x \<in> set (items b). wf_item x \<and> item_origin x \<le> k)"

definition wf_bins :: "bins \<Rightarrow> bool" where
  "wf_bins bs \<longleftrightarrow> (\<forall>k < length bs. wf_bin k (bs!k))"

definition wf_state :: "state \<Rightarrow> bool" where
  "wf_state s \<longleftrightarrow>
    wf_bins (bins s) \<and>
    (bin s) \<le> length (bins s) \<and>
    length (bins s) = length doc + 1 \<and>
    (index s) \<le> bin_size ((bins s)!(bin s))"

lemmas wf_defs = wf_state_def wf_bins_def wf_bin_def wf_item_def

subsubsection \<open>Auxiliary lemmas\<close>

lemma wf_bin_bin_append:
  "wf_bin k b \<Longrightarrow> (\<forall>x \<in> set is. wf_item x \<and> item_origin x \<le> k) \<Longrightarrow> distinct is \<Longrightarrow> wf_bin k (bin_append b is)"
  unfolding wf_defs(3) bin_defs(2) using UnE by auto

lemma bin_size_bin_append:
  "bin_size (bin_append b is) \<ge> bin_size b"
  unfolding bin_defs(2,3) by auto

lemma wf_bins_bins_append:
  "wf_bins bs \<Longrightarrow> (\<forall>x \<in> set is. wf_item x \<and> item_origin x \<le> k) \<Longrightarrow> distinct is \<Longrightarrow> wf_bins (bins_append bs k is)"
  unfolding wf_defs(1,2) bin_defs(1) using wf_bin_bin_append
  by (metis length_list_update nth_list_update_eq nth_list_update_neq)

lemma length_bins_append[simp]:
  "length (bins_append bs k is) = length bs"
  unfolding bin_defs(1) by simp

lemma bin_size_bins_append:
  "bin_size ((bins_append bs k is)!k) \<ge> bin_size (bs!k)"
  unfolding bin_defs(1) using bin_size_bin_append
  by (metis le_less_linear less_irrefl list_update_beyond nth_list_update_eq)

lemma wf_empty_bin: 
  "wf_bin k (Bin [])"
  unfolding wf_defs(3) by simp

lemma wf_empty_bins:
  "wf_bins (replicate (length doc + 1) (Bin []))"
  unfolding wf_defs(2) using wf_empty_bin by (metis length_replicate nth_replicate)

lemma wf_item_inc_item:
  "wf_item item \<Longrightarrow> item_dot item < length (item_rule_body item) \<Longrightarrow> wf_item (inc_item item)"
  unfolding wf_defs(4) inc_item_def by (simp add: item_defs)

lemma item_origin_inc_item[simp]:
  "item_origin (inc_item item) = item_origin item"
  unfolding inc_item_def by simp

lemma inj_on_inc_item:
  "distinct is \<Longrightarrow> inj_on inc_item (set is)"
  unfolding inc_item_def by (meson item.expand item.inject add_right_imp_eq inj_onI)

subsubsection \<open>Initially wellformed\<close>

lemma wf_init_items:
  "distinct init_items \<and> (\<forall>x \<in> set init_items. wf_item x \<and> item_origin x = 0)"
  by (auto simp: init_items_def distinct_map init_item_def inj_on_def wf_item_def init_rules_def valid_rules)

lemma wf_init_bins:
  "wf_bins init_bins"
  using init_bins_def wf_bins_bins_append wf_empty_bins wf_init_items by auto

lemma wf_init_state:
  "wf_state init_state"
  apply (simp add: init_state_def wf_init_bins wf_state_def)
  by (simp add: bins_append_def init_bins_def)

subsubsection \<open>Earley step wellformed\<close>

lemma wf_bins_scan:
  assumes "wf_bins bs"
  assumes "item \<in> set (items (bs!k))" "k < length bs"
  assumes "item_dot item < length (item_rule_body item)"
  shows "wf_bins (scan x item bs k)"
proof -
  define item' where [simp]: "item' = inc_item item"
  have "wf_item item'"
    using assms wf_defs wf_item_inc_item by simp
  moreover have "item_origin item' \<le> k"
    using assms wf_defs item_origin_inc_item by simp
  ultimately show ?thesis
    unfolding scan_def using assms(1) wf_bins_bins_append by simp
qed

lemma length_scan[simp]:
  "length (scan x item bs k) = length bs"
  unfolding scan_def by simp

lemma bin_size_scan:
  "bin_size ((scan x item bs k)!k) \<ge> bin_size (bs!k)"
  unfolding scan_def using bin_size_bins_append by (simp add: bins_append_def)

lemma wf_bins_predict:
  assumes "wf_bins bs" "k \<le> length doc"
  shows "wf_bins (predict X bs k)"
proof -
  define rules' where [simp]: "rules' = filter (\<lambda>rule. rule_head rule = X) rules"
  define items where [simp]: "items = map (\<lambda>rule. init_item rule k) rules'"
  have "distinct items"
    using items_def rules'_def valid_rules inj_on_def init_item_def by (auto simp: distinct_map)
  moreover have "\<forall>x \<in> set items. wf_item x \<and> item_origin x \<le> k"
    by (auto simp: assms(2) init_item_def valid_rules wf_item_def)
  ultimately show ?thesis
    unfolding predict_def using assms(1) wf_bins_bins_append by simp
qed

lemma length_predict[simp]:
  "length (predict X bs k) = length bs"
  unfolding predict_def by simp

lemma bin_size_predict:
  "bin_size ((predict X bs k)!k) \<ge> bin_size (bs!k)"
  unfolding predict_def using bin_size_bins_append by (simp add: bins_append_def)

lemma wf_bins_complete:
  assumes "wf_bins bs"
  assumes "item \<in> set (items (bs!k))" "k < length bs"
  shows "wf_bins (complete item bs k)"
proof -
  define origin_bin where "origin_bin = bs!(item_origin item)"
  define itms where "itms = filter (\<lambda>item'. next_symbol item' = Some (item_rule_head item)) (items origin_bin)"
  define itms' where "itms' = map (\<lambda>item. inc_item item) itms"

  have "distinct itms"
    unfolding itms_def origin_bin_def using wf_defs valid_rules assms less_Suc_eq_le
    by (meson Orderings.order_class.dual_order.strict_trans2 distinct_filter)
  hence 0: "distinct itms'"
    unfolding itms'_def using valid_rules inj_on_inc_item by (auto simp: distinct_map)

  have "\<forall>x \<in> set itms. wf_item x \<and> item_origin x \<le> k"
    unfolding itms_def origin_bin_def using assms wf_defs
    by (metis Orderings.order_class.dual_order.trans filter_is_subset not_less origin_bin_def subset_code(1))
  moreover have "\<forall>x \<in> set itms. item_dot x < length (item_rule_body x)"
    using next_symbol_def by (simp add: is_complete_def itms_def)
  ultimately have 1: "\<forall>x \<in> set itms'. wf_item x \<and> item_origin x \<le> k"
    unfolding itms'_def by (simp add: wf_item_inc_item)

  show ?thesis
    using 0 1 origin_bin_def itms_def itms'_def complete_def wf_bins_bins_append assms(1) by auto
qed

lemma length_complete[simp]:
  "length (complete item bs k) = length bs"
  unfolding complete_def by simp

lemma bin_size_complete:
  "bin_size ((complete item bs k)!k) \<ge> bin_size (bs!k)"
  unfolding complete_def using bin_size_bins_append by (simp add: bins_append_def)

lemma wf_state_earley_step:
  assumes "wf_state s" "bin s < length (bins s)"
  shows "wf_state (earley_step s)"
proof (cases "\<not> index s = bin_size ((bins s)!(bin s))")
  case True
  define item where [simp]: "item = (items ((bins s)!(bin s)))!index s"
  define bs where [simp]: "bs = (
        case next_symbol item of
          Some x \<Rightarrow>
            if is_terminal x then scan x item (bins s) (bin s)
            else predict x (bins s) (bin s)
        | None \<Rightarrow> complete item (bins s) (bin s))"
  define s' where [simp]: "s' = State bs (bin s) (index s + 1)"

  have "item \<in> set (items ((bins s) ! (bin s)))"
    using True item_def by (metis assms bin_size_def wf_state_def le_less list_update_id set_update_memI)
  moreover have "bin s \<le> length doc"
    using True assms wf_state_def by (metis Suc_eq_plus1 less_Suc_eq_le)
  moreover have "\<exists>x. next_symbol item = Some x \<Longrightarrow> item_dot item < length (item_rule_body item)"
    unfolding next_symbol_def by (auto simp: is_complete_def split: if_splits)
  ultimately have 0: "wf_bins bs"
    using assms wf_state_def wf_bins_scan wf_bins_predict wf_bins_complete by (auto split: option.split)

  have 1: "bin s' \<le> length (bins s')" "length (bins s') = length doc + 1"
    using assms wf_state_def by (auto split: option.split)

  have "index s < bin_size ((bins s)!(bin s))"
    by (meson True assms less_le wf_state_def)
  hence "index s + 1 \<le> bin_size (bs!(bin s))"
    using bin_size_scan bin_size_predict bin_size_complete bs_def
    apply (auto split: option.split)
    by (meson Suc_leI le_trans)+
  hence 2: "index s' \<le> bin_size ((bins s')!(bin s'))"
    by simp

  show ?thesis
    unfolding wf_state_def earley_step_def using True 0 1 2 by (auto split: option.splits)
next
  case False
  thus ?thesis
    using assms earley_step_def wf_state_def by force
qed

subsubsection "Earley wellformed"

lemma wf_state_earley:
  "wf_state s \<Longrightarrow> wf_state (earley s)"
  by (induction s rule: earley.induct) (auto simp: Let_def wf_state_earley_step)

subsection \<open>Soundness\<close>

definition sound_item :: "nat \<Rightarrow> item \<Rightarrow> bool" where
  "sound_item k item = derives [item_rule_head item] (slice (item_origin item) k doc @ item_\<beta> item)"

definition sound_bin :: "nat \<Rightarrow> bin \<Rightarrow> bool" where
  "sound_bin k b = (\<forall>item \<in> set (items b). sound_item k item)"

definition sound_bins :: "bins \<Rightarrow> bool" where
  "sound_bins bs = (\<forall>k < length bs. sound_bin k (bs!k))"

definition sound_state :: "state \<Rightarrow> bool" where
  "sound_state s = sound_bins (bins s)"

lemmas sound_defs = sound_state_def sound_bins_def sound_bin_def sound_item_def

subsubsection \<open>Auxiliary lemmas\<close>

lemma sound_bin_append:
  "sound_bin k b \<Longrightarrow> \<forall>x \<in> set is. sound_item k x \<Longrightarrow> sound_bin k (bin_append b is)"
  unfolding bin_append_def sound_bin_def by auto

lemma sound_bins_append:
  "sound_bins bs \<Longrightarrow> \<forall>x \<in> set is. sound_item k x \<Longrightarrow> sound_bins (bins_append bs k is)"
  unfolding sound_bins_def bins_append_def using sound_bin_append
  by (metis length_list_update nth_list_update_eq nth_list_update_neq)

lemma sound_item_inc_item:
  assumes "sound_item k item"
  assumes "next_symbol item = Some x"
  assumes "k < length doc" "doc!k = x" "item_origin item \<le> k"
  shows "sound_item (k+1) (inc_item item)"
proof -
  define item' where [simp]: "item' = inc_item item"
  obtain item_\<beta>' where *: "item_\<beta> item = x # item_\<beta>'"
    using assms(2) unfolding next_symbol_def
    apply (auto split: if_splits simp: is_complete_def item_\<beta>_def)
    by (metis Cons_nth_drop_Suc leI)
  have "slice (item_origin item) k doc @ item_\<beta> item = slice (item_origin item) k doc @ [x] @ item_\<beta>'"
    using * by simp
  also have "... = slice (item_origin item) (k+1) doc @ item_\<beta>'"
    using assms(3-5) slice_append_nth by auto
  also have "... = slice (item_origin item') (k+1) doc @ item_\<beta>'"
    by simp
  also have "... = slice (item_origin item') (k+1) doc @ item_\<beta> item'"
    using * apply (auto simp: inc_item_def item_\<beta>_def item_rule_body_def)
    by (metis List.list.sel(3) drop_Suc tl_drop)
  finally have "slice (item_origin item) k doc @ item_\<beta> item = slice (item_origin item') (k+1) doc @ item_\<beta> item'" .
  moreover have "derives [item_rule_head item] (slice (item_origin item) k doc @ item_\<beta> item)"
    using assms(1) sound_item_def by blast
  ultimately have "derives [item_rule_head item'] (slice (item_origin item') (k+1) doc @ item_\<beta> item')"
    by (simp add: inc_item_def item_rule_head_def)
  thus ?thesis
    using item'_def sound_item_def by blast
qed

lemma Derives1_prepend:
  assumes "Derives1 u i r v" "is_sentence w"
  shows "Derives1 (w@u) (i + length w) r (w@v)"
proof -
  obtain x y N \<alpha> where *: "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
                          "is_sentence x" "is_sentence y"
                          "(N, \<alpha>) \<in> \<RR>" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by blast

  hence "w@u = w @ x @ [N] @ y" "w@v = w @ x @ \<alpha> @ y" "is_sentence (w@x)"
    using assms(2) is_sentence_concat by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="w@x"])
    apply (rule_tac exI[where x="y"])
    by simp
qed

lemma Derivation_prepend:
  "Derivation b D b' \<Longrightarrow> is_sentence a \<Longrightarrow> Derivation (a@b) (map (\<lambda>(i, r). (i + length a, r)) D) (a@b')"
  using Derives1_prepend by (induction D arbitrary: b b') (auto, blast)

lemma Derives1_append:
  assumes "Derives1 u i r v" "is_sentence w"
  shows "Derives1 (u@w) i r (v@w)"
proof -
  obtain x y N \<alpha> where *: "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
                          "is_sentence x" "is_sentence y"
                          "(N, \<alpha>) \<in> \<RR>" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by blast

  hence "u@w = x @ [N] @ y @ w" "v@w = x @ \<alpha> @ y @ w" "is_sentence (y@w)"
    using assms(2) is_sentence_concat by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="x"])
    apply (rule_tac exI[where x="y@w"])
    by blast
qed

lemma Derivation_append:
  "Derivation a D a' \<Longrightarrow> is_sentence b \<Longrightarrow> Derivation (a@b) D (a'@b)"
  using Derives1_append by (induction D arbitrary: a a') (auto, blast)

lemma Derivation_append_rewrite:
  assumes "is_sentence b" "is_sentence d"
  assumes "Derivation a D (b @ c @ d) " "Derivation c E c'"
  shows "\<exists>F. Derivation a F (b @ c' @ d)"
  using assms Derivation_append Derivation_prepend Derivation_implies_append by fast

lemma derives1_if_valid_rule:
  "(N, \<alpha>) \<in> \<RR> \<Longrightarrow> derives1 [N] \<alpha>"
  unfolding derives1_def
  apply (rule_tac exI[where x="[]"])
  apply (rule_tac exI[where x="[]"])
  by simp

lemma derives_if_valid_rule:
  "(N, \<alpha>) \<in> \<RR> \<Longrightarrow> derives [N] \<alpha>"
  using derives1_if_valid_rule by simp

subsubsection \<open>Initial soundness\<close>

lemma sound_init_items:
  "\<forall>item \<in> set init_items. sound_item 0 item"
proof standard
  fix item
  assume *: "item \<in> set init_items"
  hence "item_dot item = 0"
    using init_item_def init_items_def by auto
  hence "(item_rule_head item, item_\<beta> item) \<in> \<RR>"
    unfolding item_rule_head_def rule_head_def item_\<beta>_def item_rule_body_def rule_body_def
    using * wf_init_items wf_item_def by simp
  thus "sound_item 0 item"
    using derives_if_valid_rule by (simp add: slice_empty sound_item_def)
qed

lemma sound_init_bins:
  "sound_bins init_bins"
  using sound_defs init_bins_def sound_init_items sound_bins_append
  by (metis Earley.bin.sel List.list.set(1) empty_iff length_replicate nth_replicate)

lemma sound_init_state:
  "sound_state init_state"
  using sound_init_bins sound_state_def init_state_def by simp

subsubsection \<open>Earley step soundness\<close>

lemma sound_bins_scan:
  assumes "wf_bins bs" "sound_bins bs"
  assumes "item \<in> set (items (bs!k))" "k < length bs"
  assumes "next_symbol item = Some x"
  shows "sound_bins (scan x item bs k)"
proof -
  define item' where [simp]: "item' = inc_item item"
  have 0: "sound_item k item"
    using assms(2-4) sound_bin_def sound_bins_def by blast
  have 1: "item_origin item \<le> k"
    using assms(1,3,4) wf_bin_def wf_bins_def by blast
  {
    assume *: "k < length doc" "doc!k = x"
    have "sound_item (k+1) item'"
      using * assms(5) 0 1 sound_item_inc_item by simp
    hence "sound_bins (bins_append bs (k+1) [item'])"
      by (simp add: assms(2) sound_bins_append)
  }
  thus ?thesis
    unfolding scan_def using assms(2) by simp
qed

lemma sound_bins_predict:
  assumes "sound_bins bs" "k \<le> length doc"
  shows "sound_bins (predict X bs k)"
proof -
  define rules' where [simp]: "rules' = filter (\<lambda>rule. rule_head rule = X) rules"
  define itms where [simp]: "itms = map (\<lambda>rule. init_item rule k) rules'"
  {
    fix item
    assume *: "item \<in> set itms"
    hence 0: "item_origin item = k" "item_dot item = 0"
      by (auto simp: init_item_def)
    have "wf_item item"
      using * by (auto simp: assms(2) init_item_def valid_rules wf_item_def)
    hence "(item_rule_head item, item_rule_body item) \<in> \<RR>"
      by (simp add: item_defs wf_item_def)
    hence "derives1 [item_rule_head item] (item_rule_body item)"
      unfolding derives1_def
      apply (rule_tac exI[where x="[]"])
      apply (rule_tac exI[where x="[]"])
      by simp
    hence "derives1 [item_rule_head item] (slice (item_origin item) k doc @ item_\<beta> item)"
      using 0 by (auto simp: slice_empty item_\<beta>_def item_rule_body_def)
    hence "derives [item_rule_head item] (slice (item_origin item) k doc @ item_\<beta> item)"
      by simp
  }
  thus ?thesis
    unfolding predict_def using assms(1) sound_bins_append sound_item_def by simp
qed

lemma sound_bins_complete:
  assumes "wf_bins bs" "sound_bins bs"
  assumes "item \<in> set (items (bs!k))" "k < length bs"
  assumes "next_symbol item = None"
  shows "sound_bins (complete item bs k)"
proof -
  define origin_bin where "origin_bin = bs!(item_origin item)"
  define itms where "itms = filter (\<lambda>item'. next_symbol item' = Some (item_rule_head item)) (items origin_bin)"
  define itms' where "itms' = map (\<lambda>item. inc_item item) itms"

  have "derives [item_rule_head item] (slice (item_origin item) k doc @ item_\<beta> item)"
    using sound_defs assms(2-4) by blast
  hence "derives [item_rule_head item] (slice (item_origin item) k doc)"
    using assms(5) unfolding next_symbol_def by (auto split: if_splits simp: is_complete_def item_\<beta>_def)
  then obtain E where E_def: "Derivation [item_rule_head item] E (slice (item_origin item) k doc)"
    using derives_implies_Derivation by blast

  {
    fix itm
    assume *: "itm \<in> set itms"

    have "next_symbol itm = Some (item_rule_head item)"
      using \<open>itm \<in> set itms\<close> itms_def by fastforce
    hence 0: "item_\<beta> itm = (item_rule_head item) # (tl (item_\<beta> itm))"
      unfolding next_symbol_def apply (auto split: if_splits simp: is_complete_def item_\<beta>_def)
      by (metis List.list.collapse drop_all_iff hd_drop_conv_nth leI)

    have 1: "itm \<in> set (items (bs!(item_origin item)))"
      using * itms_def origin_bin_def by force
    moreover have 2: "item_origin item \<le> k"
      using assms(1,3,4) wf_bin_def wf_bins_def by blast
    ultimately have "derives [item_rule_head itm] (slice (item_origin itm) (item_origin item) doc @ item_\<beta> itm)"
      using sound_defs assms(2-4) by simp
    then obtain D where "Derivation [item_rule_head itm] D (slice (item_origin itm) (item_origin item) doc @ item_\<beta> itm)"
      using derives_implies_Derivation by blast
    hence D_def: "Derivation [item_rule_head itm] D (slice (item_origin itm) (item_origin item) doc @ [item_rule_head item] @ (tl (item_\<beta> itm)))"
      using 0 by simp

    have 3: "item_origin itm \<le> item_origin item"
      using 1 2 assms(1,4) wf_bins_def wf_bin_def by simp

    have "wf_item itm"
      by (meson 1 2 Orderings.order_class.dual_order.strict_trans2 assms(1) assms(4) wf_bin_def wf_bins_def)
    hence "is_sentence (tl (item_\<beta> itm))"
      unfolding item_\<beta>_def item_rule_body_def rule_body_def is_sentence_simp
      by (metis Product_Type.prod.collapse drop_Suc in_set_dropD is_sentence_simp rule_\<alpha>_type tl_drop wf_item_def)
    moreover have "is_sentence (slice (item_origin itm) (item_origin item) doc)"
      using is_sentence_simp valid_doc unfolding is_symbol_def is_terminal_def by (meson slice_subset subsetD)
    ultimately obtain G where "Derivation [item_rule_head itm] G (slice (item_origin itm) (item_origin item) doc @ slice (item_origin item) k doc @ (tl (item_\<beta> itm)))"
      using D_def E_def Derivation_append_rewrite by blast
    hence "Derivation [item_rule_head itm] G (slice (item_origin itm) k doc @ (tl (item_\<beta> itm)))"
      using slice_append 2 3 append_assoc by metis
    hence "derives [item_rule_head itm] (slice (item_origin itm) k doc @ (tl (item_\<beta> itm)))"
      using Derivation_implies_derives by blast
  }
  hence 4: "\<forall>itm \<in> set itms. derives [item_rule_head itm] (slice (item_origin itm) k doc @ (tl (item_\<beta> itm)))"
    by blast

  {
    fix itm'
    assume *: "itm' \<in> set itms'"
    then obtain itm where "itm' = inc_item itm" "itm \<in> set itms"
      using itms'_def by auto
    have "item_rule_head itm' = item_rule_head itm"
      by (simp add: \<open>itm' = inc_item itm\<close> inc_item_def item_rule_head_def)
    have "\<not> is_complete itm"
      using \<open>itm \<in> set itms\<close> itms_def next_symbol_def by force
    hence "item_\<beta> itm' = tl (item_\<beta> itm)"
      using \<open>itm' = inc_item itm\<close> unfolding inc_item_def by (simp add: drop_Suc item_\<beta>_def item_rule_body_def tl_drop)
    hence "derives [item_rule_head itm'] (slice (item_origin itm') k doc @ item_\<beta> itm')"
      unfolding itms'_def inc_item_def using 4
      using \<open>item_rule_head itm' = item_rule_head itm\<close> \<open>itm \<in> set itms\<close> \<open>itm' = inc_item itm\<close> by fastforce 
  }

  thus ?thesis
    unfolding complete_def using sound_bins_append assms(2) itms'_def itms_def origin_bin_def sound_item_def by simp
qed

lemma sound_state_earley_step:
  assumes "wf_state s" "sound_state s" "bin s < length (bins s)"
  shows "sound_state (earley_step s)"
proof (cases "\<not> index s = bin_size ((bins s)!(bin s))")
  case True
  define item where [simp]: "item = (items ((bins s)!(bin s)))!index s"
  define bs where [simp]: "bs = (
        case next_symbol item of
          Some x \<Rightarrow>
            if is_terminal x then scan x item (bins s) (bin s)
            else predict x (bins s) (bin s)
        | None \<Rightarrow> complete item (bins s) (bin s))"
  define s' where [simp]: "s' = State bs (bin s) (index s + 1)"

  have "item \<in> set (items ((bins s) ! (bin s)))"
    using True item_def by (metis assms(1) bin_size_def wf_state_def le_less list_update_id set_update_memI)
  moreover have "bin s \<le> length doc"
    using True assms wf_state_def by fastforce
  moreover have "\<exists>x. next_symbol item = Some x \<Longrightarrow> item_dot item < length (item_rule_body item)"
    unfolding next_symbol_def by (auto simp: is_complete_def split: if_splits)
  ultimately have "sound_bins bs"
    using assms wf_state_def sound_state_def sound_bins_scan sound_bins_predict sound_bins_complete by (auto split: option.split)
  thus ?thesis
    unfolding sound_state_def earley_step_def using True by (auto split: option.splits)
next
  case False
  thus ?thesis
    using assms earley_step_def wf_state_def sound_state_def by force
qed

subsubsection "Earley soundness"

lemma sound_state_earley:
  "wf_state s \<Longrightarrow> sound_state s \<Longrightarrow> sound_state (earley s)"
  by (induction s rule: earley.induct) (auto simp: Let_def wf_state_earley_step sound_state_earley_step)

theorem soundness:
  assumes "earley_recognized"
  shows "derives [\<SS>] doc"
proof -
  obtain item where *: "item \<in> set (items ((bins (earley init_state))!length doc))" "is_finished item"
    using assms unfolding earley_recognized_def by meson
  have "sound_state (earley init_state)"
    using sound_init_state sound_state_earley wf_init_state by blast
  moreover have "length doc < length (bins (earley init_state))"
    using wf_state_earley wf_init_state wf_state_def by simp
  ultimately have "derives [item_rule_head item] (slice (item_origin item) (length doc) doc @ item_\<beta> item)"
    unfolding sound_state_def sound_bins_def sound_bin_def sound_item_def using *(1) by blast
  thus ?thesis
    using *(2) is_finished_def is_complete_def item_\<beta>_def by auto
qed

subsection \<open>Completeness\<close>

definition partially_scanned :: "state \<Rightarrow> bool" where
  "partially_scanned s = (
    \<forall>m n r k i x.
      m+1 < length (bins s) \<and>
      n < length (items (bins s ! m)) \<and>
      Item r k i = items (bins s ! m) ! n \<and>
      next_symbol (Item r k i) = Some x \<and>
      doc!m = x \<and>
      (m < bin s \<or> (m = bin s \<and> n < index s)) \<longrightarrow>
    Item r (k+1) i \<in> set (items (bins s ! (m+1)))
  )"

definition complete_state :: "state \<Rightarrow> bool" where
  "complete_state s = (
    \<forall>m n r k i j x D.
      m < length (bins s) \<and>
      j \<le> m \<and>
      n < length (items (bins s ! j)) \<and>
      Item r k i = items (bins s ! j) ! n \<and>
      next_symbol (Item r k i) = Some x \<and>
      Derivation [x] D (slice j m doc) \<and>
      (m < bin s \<or> (m = bin s \<and> n < index s)) \<longrightarrow>
    Item r (k+1) i \<in> set (items (bins s ! m)) \<comment>\<open>Need to distinguish between x being nonterminal -> (m+1) and terminal -> m ...\<close>
  )"

subsubsection \<open>Auxiliary lemmas\<close>

lemma m_lt_bin_bins_id:
  assumes "m < bin s"
  shows "bins s ! m = bins (earley_step s) ! m"
  using assms unfolding earley_step_def
  by (auto simp: Let_def bins_append_def scan_def predict_def complete_def split: option.split)

lemma bin_append_monotonic:
  "set (items b) \<subseteq> set (items (bin_append b is))"
  unfolding bin_append_def by simp

lemma bins_append_monotonic:
  "i < length bs \<Longrightarrow> set (items (bs!i)) \<subseteq> set (items (bins_append bs k is ! i))"
  unfolding bins_append_def using bin_append_monotonic
  by (metis nth_list_update_eq nth_list_update_neq order_refl)

lemma bin_append_union:
  "set (items (bin_append b is)) = set (items b) \<union> set is"
  unfolding bin_append_def by auto

lemma bins_append_union:
  "k < length bs \<Longrightarrow> set (items (bins_append bs k is ! k)) = set (items (bs ! k)) \<union> set is"
  unfolding bins_append_def using bin_append_union by simp

lemma bin_items_monotonic:
  "m < length (bins s) \<Longrightarrow> set (items (bins s ! m)) \<subseteq> set (items (bins (earley_step s) ! m))"
  unfolding earley_step_def using bins_append_monotonic
  by (auto simp: scan_def predict_def complete_def bins_append_def Let_def split: option.split)

lemma length_step_id:
  "length (bins s) = length (bins (earley_step s))"
  unfolding earley_step_def by (auto simp: Let_def split: option.split)

lemma bins_append_indexing_id:
  "m < length bs \<Longrightarrow> n < length (items (bs!m)) \<Longrightarrow> items (bins_append bs k is ! m) ! n = items (bs ! m) ! n"
  unfolding bins_append_def bin_append_def
  by (metis Earley.bin.sel append_same_eq list_update_append1 list_update_id nth_list_update nth_list_update_neq)

lemma m_eq_bin_bins_id:
  assumes "m = bin s" "n < length (items (bins s ! m))"
  shows "(items (bins s ! m)) ! n = (items (bins (earley_step s) ! m)) ! n"
  using assms unfolding earley_step_def
  apply (auto simp: Let_def split: option.splits)
  apply (metis bins_append_def bins_append_indexing_id complete_def list_update_beyond not_le)
   apply (simp add: bins_append_def scan_def)
  by (metis bins_append_def bins_append_indexing_id list_update_beyond not_le_imp_less predict_def)

lemma partially_scanned_earley_step:
  assumes "partially_scanned s" "wf_state s"
  shows "partially_scanned (earley_step s)"
  unfolding partially_scanned_def
proof (standard, standard, standard, standard, standard, standard, standard)
  fix m n r i k x
  assume *: "m+1 < length (bins (earley_step s)) \<and>
             n < length (items (bins (earley_step s) ! m)) \<and>
             Item r k i = items (bins (earley_step s) ! m) ! n \<and>
             next_symbol (Item r k i) = Some x \<and>
             doc!m = x \<and>
             (m < bin (earley_step s) \<or> (m = bin (earley_step s) \<and> n < index (earley_step s)))"

  hence 0: "m+1 < length (bins s)"
    using length_step_id by auto

  show "Item r (k+1) i \<in> set (items (bins (earley_step s) ! (m+1)))"
  proof cases
    assume "m < bin s"
    thus ?thesis
      using assms(1) * 0 unfolding partially_scanned_def by (smt (z3) bin_items_monotonic m_lt_bin_bins_id subsetD)
  next
    assume "\<not> m < bin s"
    hence "m = bin s"
      by (metis (no_types, lifting) * Earley.state.sel(2) Earley.state.sel(3) Suc_eq_plus1 earley_step_def gr_implies_not0 less_antisym)
    show ?thesis
    proof cases
      assume "n < index s"
      have "n < length (items (bins s ! m))"
        using \<open>m = bin s\<close> \<open>n < index s\<close> assms(2) bin_size_def wf_state_def by auto
      thus ?thesis
        by (smt (verit, ccfv_SIG) "*" "0" \<open>m = bin s\<close> \<open>n < index s\<close> assms(1) bin_items_monotonic less_or_eq_imp_le m_eq_bin_bins_id partially_scanned_def subsetD)
    next 
      assume "\<not> n < index s"
      hence "n \<ge> index s"
        by simp
      show ?thesis
      proof cases
        assume "index s = bin_size ((bins s)!(bin s))"
        show ?thesis
          using "*" \<open>\<not> n < index s\<close> \<open>index s = bin_size (bins s ! bin s)\<close> \<open>m = bin s\<close> bin_size_def earley_step_def by auto
      next
        assume "\<not> index s = bin_size ((bins s)!(bin s))"
        hence "index s < length (items (bins s ! m))"
          using \<open>m = bin s\<close> assms(2) bin_size_def wf_state_def by auto
        have "n = index s"
          by (metis (no_types, lifting) "*" Earley.state.sel(2) Earley.state.sel(3) Suc_eq_plus1 \<open>\<not> m < bin s\<close> \<open>index s \<le> n\<close> \<open>index s \<noteq> bin_size (bins s ! bin s)\<close> earley_step_def le_less_Suc_eq)

        define item where "item = (items ((bins s)!(bin s)))!index s"

        have "n < length (items (bins s ! m))"
          using \<open>index s < length (items (bins s ! m))\<close> \<open>n = index s\<close> by auto
        hence "items (bins s ! m) ! n = items (bins (earley_step s) ! m) ! n"
          using m_eq_bin_bins_id \<open>m = bin s\<close> \<open>n = index s\<close> by blast
        hence "item = Item r k i"
          by (simp add: "*" \<open>m = bin s\<close> \<open>n = index s\<close> item_def)
        have "is_terminal x"
          by (metis "*" add_less_cancel_right assms(2) is_terminal_def length_step_id nth_mem subset_code(1) valid_doc wf_state_def)

        have "bins (earley_step s) = scan x item (bins s) (bin s)"
          unfolding earley_step_def apply (auto simp: Let_def split: option.splits)
          apply (auto simp: \<open>index s \<noteq> bin_size (bins s ! bin s)\<close> item_def)
          apply (metis "*" Option.option.discI \<open>item = Item r k i\<close> item_def)
          using "*" \<open>item = Item r k i\<close> item_def apply force+
          by (metis "*" Option.option.inject \<open>is_terminal x\<close> \<open>item = Item r k i\<close> item_def)

        have "m < length doc"
          by (metis "*" add_le_cancel_right assms(2) length_step_id verit_comp_simplify1(3) wf_state_def)
        hence "scan x item (bins s) m = bins_append (bins s) (m + 1) [inc_item item]"
          unfolding scan_def using * by simp
        have "inc_item item \<in> set (items ((bins_append (bins s) (m+1) [inc_item item]) !(m+1)))"
          using "0" bins_append_union by auto
        moreover have "inc_item item = Item r (k+1) i"
          unfolding inc_item_def by (simp add: \<open>item = Item r k i\<close>)
        ultimately have "Item r (k+1) i \<in> set (items ((scan x item (bins s) m) ! (m+1)))"
          using \<open>scan x item (bins s) m = bins_append (bins s) (m + 1) [inc_item item]\<close> by simp
        thus ?thesis
          by (simp add: \<open>bins (earley_step s) = scan x item (bins s) (bin s)\<close> \<open>m = bin s\<close>)
      qed
    qed
  qed
qed

subsubsection \<open>Initial completeness\<close>

subsubsection \<open>Earley step completeness\<close>

lemma complete_state_earley_step:
  assumes "wf_state s" "sound_state s" "complete_state s" "partially_scanned s"
  shows "complete_state (earley_step s)"
  unfolding complete_state_def
proof (standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix m n r k i j x D
  assume *: "m < length (bins (earley_step s)) \<and>
             j \<le> m \<and>
             n < length (items (bins (earley_step s) ! j)) \<and>
             Item r k i = items (bins (earley_step s) ! j) ! n \<and>
             next_symbol (Item r k i) = Some x \<and>
             Derivation [x] D (slice j m doc) \<and>
             (m < bin (earley_step s) \<or> m = bin (earley_step s) \<and> n < index (earley_step s))"
  show "Item r (k + 1) i \<in> set (items (bins (earley_step s) ! m))" using *
  proof (induction D arbitrary: m n r k i j x)
    case Nil
    show ?case
      sorry
  next
    case (Cons d D)
    show ?case
      sorry
  qed
qed

subsubsection \<open>Earley completeness\<close>

lemma complete_state_earley:
  "wf_state s \<Longrightarrow> sound_state s \<Longrightarrow> complete_state s \<Longrightarrow> partially_scanned s \<Longrightarrow> complete_state (earley s)"
  by (induction s rule: earley.induct) (auto simp: Let_def wf_state_earley_step sound_state_earley_step complete_state_earley_step partially_scanned_earley_step)

lemma
  assumes "derives \<alpha> \<beta>"
  shows "\<exists>I. (\<forall>i < length \<alpha>. derives ([\<alpha>!i]) (slice (I!i) (I!(i+1)) \<beta>)) \<and>
             length I = length \<alpha> + 1 \<and>
             I!0 = 0 \<and>
             I!(length \<alpha>) = length \<beta> \<and>
             sorted I"
  sorry

theorem completeness:
  assumes "derives [\<SS>] doc"
  shows "earley_recognized"
  sorry

end

end
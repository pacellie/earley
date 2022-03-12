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

section \<open>Auxiliary Lemmas\<close>

lemma (in CFG) is_sentence_simp:
  "is_sentence s \<longleftrightarrow> (\<forall>x \<in> set s. is_symbol x)"
  unfolding is_sentence_def by (simp add: list_all_iff)

lemma (in CFG) is_word_simp:
  "is_word s \<longleftrightarrow> (\<forall>x \<in> set s. is_terminal x)"
  unfolding is_word_def by (simp add: list_all_iff)

section \<open>List Auxiliary\<close>

\<comment>\<open>slice a b xs: a is inclusive, b is exclusive\<close>
fun slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slice _ _ [] = []"
| "slice _ 0 (x#xs) = []"
| "slice 0 (Suc b) (x#xs) = x # slice 0 b xs"
| "slice (Suc a) (Suc b) (x#xs) = slice a b xs"

value "slice 1 3 [a,b,c,d,e]"

lemma slice_drop_take:
  "slice a b xs = drop a (take b xs)"
  by (induction a b xs rule: slice.induct) auto

section \<open>Earley Parsing Algorithm\<close>

subsection \<open>Earley Items, Bin(s), State\<close>

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

datatype state =
  State
    (bins: bins)
    (bin: nat) \<comment>\<open>active bin index\<close>
    (index: nat) \<comment>\<open>active item index\<close>

definition state_is_final :: "state \<Rightarrow> bool" where
  "state_is_final s \<longleftrightarrow> bin s = length (bins s)"

definition state_bin_is_finished :: "state \<Rightarrow> bool" where
  "state_bin_is_finished s \<longleftrightarrow> index s = bin_size ((bins s)!(bin s))"

definition state_current_item :: "state \<Rightarrow> item" where
  "state_current_item s = (items ((bins s)!(bin s)))!index s"

subsection \<open>Earley Algorithm\<close>

locale Earley = CFG +
  fixes doc :: "symbol list"
  fixes rules :: "rule list"
  assumes valid_doc: "set doc \<subseteq> \<TT>"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
begin

definition scan :: "symbol \<Rightarrow> item \<Rightarrow> bins \<Rightarrow> nat \<Rightarrow> bins" where
  "scan x item bs k = (
    if doc!k = x then
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
    if state_is_final s then
      s
    else if state_bin_is_finished s then
      (State (bins s) (bin s + 1) 0)
    else
      let item = state_current_item s in
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
    let s' = earley_step s in
    if (bin s = bin s') \<and> (index s = index s') then
      s
    else
      earley s')"
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

definition earley_recognised :: "bool" where
  "earley_recognised \<longleftrightarrow> (\<exists>item \<in> set (items ((bins (earley init_state))!length doc)). is_finished item)"

subsection \<open>Termination\<close>

lemma earley_step_fixpoint':
  "earley_step (earley_step s) = s \<Longrightarrow> earley_step s = s"
  unfolding earley_step_def state_is_final_def
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

subsubsection \<open>Auxiliary Lemmas\<close>

lemma wf_bin_bin_append:
  "wf_bin k b \<Longrightarrow> (\<forall>x \<in> set is. wf_item x \<and> item_origin x \<le> k) \<Longrightarrow> distinct is \<Longrightarrow> wf_bin k (bin_append b is)"
  unfolding wf_bin_def bin_append_def using UnE by auto

lemma bin_size_bin_append:
  "bin_size (bin_append b is) \<ge> bin_size b"
  unfolding bin_append_def bin_size_def by auto

lemma wf_bins_bins_append:
  "wf_bins bs \<Longrightarrow> (\<forall>x \<in> set is. wf_item x \<and> item_origin x \<le> k) \<Longrightarrow> distinct is \<Longrightarrow> wf_bins (bins_append bs k is)"
  unfolding wf_bins_def using wf_bin_bin_append
  by (metis bins_append_def length_list_update nth_list_update_eq nth_list_update_neq)

lemma length_bins_append[simp]:
  "length (bins_append bs k is) = length bs"
  unfolding bins_append_def by simp

lemma bin_size_bins_append:
  "bin_size ((bins_append bs k is)!k) \<ge> bin_size (bs!k)"
  unfolding bins_append_def using bin_size_bin_append
  by (metis le_less_linear less_irrefl list_update_beyond nth_list_update_eq)

lemma wf_empty_bin: 
  "wf_bin k (Bin [])"
  unfolding wf_bin_def by simp

lemma wf_empty_bins:
  "wf_bins (replicate (length doc + 1) (Bin []))"
  unfolding wf_bins_def using wf_empty_bin by (metis length_replicate nth_replicate)

lemma wf_item_inc_item:
  "wf_item item \<Longrightarrow> item_dot item < length (item_rule_body item) \<Longrightarrow> wf_item (inc_item item)"
  unfolding wf_item_def inc_item_def by (simp add: item_rule_body_def)

lemma item_origin_inc_item[simp]:
  "item_origin (inc_item item) = item_origin item"
  unfolding inc_item_def by simp

lemma inj_on_inc_item:
  "distinct is \<Longrightarrow> inj_on inc_item (set is)"
  unfolding inc_item_def by (meson item.expand item.inject add_right_imp_eq inj_onI)

lemma wf_state_earley_step_finished_bin:
  "wf_state s \<Longrightarrow> \<not> state_is_final s \<Longrightarrow> state_bin_is_finished s \<Longrightarrow> wf_state ((State (bins s) (bin s + 1) 0))"
  by (simp add: state_is_final_def wf_state_def)

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
  assumes "wf_bins bs" "\<exists>i < length bs. item \<in> set (items (bs!i)) \<and> i \<le> k"
  assumes "item_dot item < length (item_rule_body item)"
  shows "wf_bins (scan x item bs k)"
proof -
  define item' where [simp]: "item' = inc_item item"
  have "wf_item item'"
    using assms item'_def wf_bin_def wf_bins_def wf_item_inc_item by blast
  moreover have "item_origin item' \<le> k"
    using assms by (metis item'_def item_origin_inc_item le_trans wf_bin_def wf_bins_def)
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
  assumes "wf_bins bs" "\<exists>i < length bs. item \<in> set (items (bs!i)) \<and> i \<le> k"
  shows "wf_bins (complete item bs k)"
proof -
  define origin_bin where "origin_bin = bs!(item_origin item)"
  define itms where "itms = filter (\<lambda>item'. next_symbol item' = Some (item_rule_head item)) (items origin_bin)"
  define itms' where "itms' = map (\<lambda>item. inc_item item) itms"

  have "distinct itms"
    unfolding itms_def origin_bin_def
    using wf_bin_def wf_bins_def wf_item_def valid_rules assms less_Suc_eq_le
    by (meson Orderings.order_class.dual_order.strict_trans2 distinct_filter)
  hence 0: "distinct itms'"
    unfolding itms'_def using valid_rules inj_on_inc_item by (auto simp: distinct_map)

  have "\<forall>x \<in> set itms. wf_item x \<and> item_origin x \<le> k"
    unfolding itms_def origin_bin_def
    using assms wf_bins_def wf_bin_def wf_item_def
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
  assumes "wf_state s"
  shows "wf_state (earley_step s)"
proof (cases "\<not>state_is_final s \<and> \<not>state_bin_is_finished s")
  case True

  define item where [simp]: "item = state_current_item s"
  define bs where [simp]: "bs = (
        case next_symbol item of
          Some x \<Rightarrow>
            if is_terminal x then scan x item (bins s) (bin s)
            else predict x (bins s) (bin s)
        | None \<Rightarrow> complete item (bins s) (bin s))"
  define s' where [simp]: "s' = State bs (bin s) (index s + 1)"

  have "\<exists>i < length (bins s). item \<in> set (items ((bins s) ! i)) \<and> i \<le> (bin s)"
    using True item_def unfolding state_current_item_def state_is_final_def state_bin_is_finished_def
    by (metis assms bin_size_def wf_state_def le_less list_update_id set_update_memI)
  moreover have "bin s \<le> length doc"
    using True assms state_is_final_def wf_state_def by auto
  moreover have "\<exists>x. next_symbol item = Some x \<Longrightarrow> item_dot item < length (item_rule_body item)"
    unfolding next_symbol_def by (auto simp: is_complete_def split: if_splits)
  ultimately have 0: "wf_bins bs"
    using assms wf_state_def wf_bins_scan wf_bins_predict wf_bins_complete by (auto split: option.split)

  have 1: "bin s' \<le> length (bins s')" "length (bins s') = length doc + 1"
    using assms wf_state_def by (auto split: option.split)

  have "index s < bin_size ((bins s)!(bin s))"
    by (meson True assms less_le state_bin_is_finished_def wf_state_def)
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
    using assms earley_step_def wf_state_earley_step_finished_bin by force
qed

subsection \<open>Soundness\<close>

definition sound_item :: "nat \<Rightarrow> item \<Rightarrow> bool" where
  "sound_item k item = derives [item_rule_head item] (slice (item_origin item) k doc @ item_\<beta> item)"

definition sound_bin :: "nat \<Rightarrow> bin \<Rightarrow> bool" where
  "sound_bin k b = (\<forall>item \<in> set (items b). sound_item k item)"

definition sound_bins :: "bins \<Rightarrow> bool" where
  "sound_bins bs = (\<forall>k < length bs. sound_bin k (bs!k))"

definition sound_state :: "state \<Rightarrow> bool" where
  "sound_state s = sound_bins (bins s)"

end

end
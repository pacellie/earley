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
    LocalLexing.TheoremD2 \<comment>\<open>TODO: Rewrite\<close>
    LocalLexing.TheoremD4 \<comment>\<open>TODO: Rewrite\<close>
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

section \<open>Auxiliary Lemmas\<close>

lemma (in CFG) is_sentence_simp:
  "is_sentence s \<longleftrightarrow> (\<forall>x \<in> set s. is_symbol x)"
  unfolding is_sentence_def by (simp add: list_all_iff)

lemma (in CFG) is_word_simp:
  "is_word s \<longleftrightarrow> (\<forall>x \<in> set s. is_terminal x)"
  unfolding is_word_def by (simp add: list_all_iff)

section \<open>List Auxiliary\<close>

fun contains :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "contains _ [] \<longleftrightarrow> False"
| "contains f (x#xs) \<longleftrightarrow> (if f x then True else contains f xs)"

fun slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slice _ _ [] = []"
| "slice _ 0 (x#xs) = []"
| "slice 0 (Suc b) (x#xs) = x # slice 0 b xs"
| "slice (Suc a) (Suc b) (x#xs) = slice a b xs"

lemma "slice a b xs = drop a (take b xs)"
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
  "bin_append b is = Bin (items b @ (filter (\<lambda>i. \<not> contains (\<lambda>i'. i = i') (items b)) is))"

type_synonym bins = "bin list"

definition bins_append :: "bins \<Rightarrow> nat \<Rightarrow> item list \<Rightarrow> bins" where
  "bins_append bs k is = bs[k := bin_append (bs!k) is]"

datatype state =
  State
    (bins: bins)
    (bin: nat) \<comment>\<open>active bin index\<close>
    (index: nat) \<comment>\<open>active item index\<close>

definition state_is_final :: "state \<Rightarrow> bool" where
  "state_is_final s \<longleftrightarrow> bin s \<ge> length (bins s)"

definition state_bin_is_finished :: "state \<Rightarrow> bool" where
  "state_bin_is_finished s \<longleftrightarrow> index s \<ge> bin_size ((bins s)!(bin s))"

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
    bins_append bs k (map inc_item items))"

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
  "earley_recognised \<longleftrightarrow> (
    let state = earley init_state in
    contains is_finished (items ((bins state)!length doc)))"

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
  "wf_item item = (
    item_rule item \<in> \<RR> \<and>
    item_origin item \<le> length doc \<and>
    item_dot item \<le> length (item_rule_body item))"

lemma wf_init_items:
  "\<forall>x \<in> set init_items. wf_item x"
  by (auto simp: init_items_def init_rules_def valid_rules init_item_def wf_item_def)

lemma is_word_subset: "is_word x \<Longrightarrow> set y \<subseteq> set x \<Longrightarrow> is_word y"
  by (metis (mono_tags, hide_lams) in_set_conv_nth is_word_def list_all_length subsetCE)

definition wf_bin :: "nat \<Rightarrow> bin \<Rightarrow> bool" where
  "wf_bin k b \<longleftrightarrow>
    distinct (items b) \<and>
    (\<forall>x \<in> set (items b). wf_item x \<and> item_origin x \<le> k)"

definition wf_bins :: "bins \<Rightarrow> bool" where
  "wf_bins bs \<longleftrightarrow>
    length bs = length doc \<and>
    (\<forall>k < length bs. wf_bin k (bs!k))"

lemma wf_init_bins: \<comment>\<open>TODO\<close>
  "wf_bins init_bins"
  sorry

definition wf_state :: "state \<Rightarrow> bool" where
  "wf_state s \<longleftrightarrow>
    wf_bins (bins s) \<and>
    (bin s) \<le> length doc \<and>
    (index s) \<le> bin_size ((bins s)!(bin s))"

lemma wf_init_state: \<comment>\<open>TODO\<close>
  "wf_state init_state"
  sorry

subsection \<open>Soundness\<close>

(* off by one ;) *)
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
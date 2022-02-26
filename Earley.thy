theory Earley
  imports 
    LocalLexing.CFG
    LocalLexing.Derivations
    LocalLexing.LLEarleyParsing \<comment>\<open>Rewritten\<close>
    LocalLexing.Validity \<comment>\<open>TODO: Rewrite\<close>
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
    LocalLexing.InductRules \<comment>\<open>Needed?\<close>
    LocalLexing.ListTools \<comment>\<open>Needed?\<close>
begin

section \<open>Auxiliary Lemmas\<close>

lemma (in CFG) is_sentence_simp:
  "is_sentence s \<longleftrightarrow> (\<forall>x \<in> set s. is_symbol x)"
  unfolding is_sentence_def by (simp add: list_all_iff)

lemma (in CFG) is_word_simp:
  "is_word s \<longleftrightarrow> (\<forall>x \<in> set s. is_terminal x)"
  unfolding is_word_def by (simp add: list_all_iff)

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

type_synonym items = "item set"

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

type_synonym bin = "item list"

type_synonym bins = "bin list"

datatype state =
  State
    (bins: bins)
    (bin: nat) \<comment>\<open>active bin index\<close>
    (index: nat) \<comment>\<open>active item index\<close>

definition is_finished_state :: "state \<Rightarrow> bool" where
  "is_finished_state s \<longleftrightarrow> bin s \<ge> length (bins s)"

definition is_finished_bin :: "state \<Rightarrow> bool" where
  "is_finished_bin s \<longleftrightarrow> index s \<ge> length ((bins s)!(bin s))"

definition current_item :: "state \<Rightarrow> item" where
  "current_item s = ((bins s)!(bin s))!index s"

fun contains :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "contains _ [] \<longleftrightarrow> False"
| "contains f (x#xs) \<longleftrightarrow> (if f x then True else contains f xs)"
  
definition update_bins :: "bins \<Rightarrow> nat \<Rightarrow> item list \<Rightarrow> bins" where
  "update_bins bs k is = (
    let bin = bs!k in
    let is = filter (\<lambda>i. \<not> contains (\<lambda>j. i = j) bin) is in
    (bs[k := bin @ is])
  )"

subsection \<open>Earley Algorithm\<close>

locale Earley = CFG +
  fixes doc :: "symbol list"
  fixes rules :: "rule list"
  assumes valid_doc: "set Doc \<subseteq> \<TT>"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
begin

definition earley_step :: "state \<Rightarrow> state" where
  "earley_step s = (
    if is_finished_state s then
      s
    else if is_finished_bin s then
      (State (bins s) (bin s + 1) 0)
    else
      let item = current_item s in
      case next_symbol item of
        Some x \<Rightarrow> (
          if doc!(bin s) = x then \<comment>\<open>Scan: x is a terminal\<close>
            let item' = inc_item item in
            State (update_bins (bins s) (bin s + 1) [item']) (bin s) (index s + 1)
          else \<comment>\<open>Predict: x is a non-terminal\<close>
            let rules' = filter (\<lambda>rule. rule_head rule = x) rules in
            let items = map (\<lambda>rule. init_item rule (bin s)) rules' in
            State (update_bins (bins s) (bin s) items) (bin s) (index s + 1)
        )
      | None \<Rightarrow> ( \<comment>\<open>Complete\<close>
          let origin_bin = (bins s)!(item_origin item) in
          let items = filter (\<lambda>item'. next_symbol item' = Some (item_rule_head item)) origin_bin in
          let items' = map inc_item items in
          State (update_bins (bins s) (bin s) items') (bin s) (index s + 1)
        )
  )"

function earley :: "state \<Rightarrow> state" where \<comment>\<open>TODO: Termination, REMARK: use while combinator\<close>
  "earley s = (
    let s' = earley_step s in
    if (bin s = bin s') \<and> (index s = index s') then
      s
    else
      earley s'
  )"
  by pat_completeness simp
termination
  sorry

definition init_earley_state :: "state" where
  "init_earley_state = (
    let init_rules = filter (\<lambda>rule. rule_head rule = \<SS>) rules in
    let init_items = map (\<lambda>rule. init_item rule 0) init_rules in
    let bins = replicate (length doc + 1) [] in
    State (update_bins bins 0 init_items) 0 0
  )"

definition earley_recognised :: "bool" where
  "earley_recognised \<longleftrightarrow> (
    let state = earley init_earley_state in
    contains is_finished ((bins state)!length doc)
  )"

subsection \<open>Proofs\<close>

lemma earley_step_fixpoint':
  "earley_step (earley_step s) = s \<Longrightarrow> earley_step s = s"
  unfolding earley_step_def is_finished_state_def
  apply (auto simp: Let_def split!: option.splits if_splits)
  apply (metis Suc_n_not_le_n n_not_Suc_n nat_le_linear le_SucI le_refl state.sel(2,3))+
  done

lemma earley_step_fixpoint:
  "(earley_step s = s) \<longleftrightarrow> earley_step (earley_step s) = s"
  using earley_step_fixpoint' by auto

end

end
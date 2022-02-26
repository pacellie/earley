theory Earley
  imports 
    LocalLexing.CFG
    LocalLexing.Derivations
    LocalLexing.LLEarleyParsing \<comment>\<open>TODO: Rewrite\<close>
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

subsection \<open>Earley Items, Bin, Bins, State\<close>

datatype item = 
  Item 
    (item_rule: rule) 
    (item_dot : nat) 
    (item_origin : nat)

type_synonym items = "item set"

definition item_nonterminal :: "item \<Rightarrow> symbol" where
  "item_nonterminal x = fst (item_rule x)"

definition item_rhs :: "item \<Rightarrow> sentence" where
  "item_rhs x = snd (item_rule x)"

definition item_\<alpha> :: "item \<Rightarrow> sentence" where
  "item_\<alpha> x = take (item_dot x) (item_rhs x)"

definition item_\<beta> :: "item \<Rightarrow> sentence" where 
  "item_\<beta> x = drop (item_dot x) (item_rhs x)"

definition init_item :: "rule \<Rightarrow> nat \<Rightarrow> item" where
  "init_item r k = Item r 0 k"

definition is_complete :: "item \<Rightarrow> bool" where
  "is_complete x = (item_dot x \<ge> length (item_rhs x))"

definition (in CFG) is_finished :: "item \<Rightarrow> bool" where
  "is_finished x = (item_nonterminal x = \<SS> \<and> item_origin x = 0 \<and> is_complete x)"

definition next_symbol :: "item \<Rightarrow> symbol option" where
  "next_symbol x = (if is_complete x then None else Some ((item_rhs x) ! (item_dot x)))"

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

definition update_bins :: "bins \<Rightarrow> nat \<Rightarrow> item list \<Rightarrow> bins" where
  "update_bins bs k is = (bs[k := bs!k @ is])"

subsection \<open>Earley Algorithm\<close>

locale Earley = CFG +
  fixes doc :: "symbol list"
  fixes rules :: "rule list"
  assumes valid_doc: "set Doc \<subseteq> \<TT>"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
begin

definition earley_step :: "state \<Rightarrow> state" where \<comment>\<open>TODO\<close>
  "earley_step s = (
    if is_finished_state s then
      s
    else if is_finished_bin s then
      (State (bins s) (bin s + 1) 0)
    else
      let item = current_item s in
      case next_symbol item of
        Some x \<Rightarrow> (
          if doc!(bin s) = x then \<comment>\<open>Scan: x must then be a terminal\<close>
            let item' = inc_item item in
            State (update_bins (bins s) (bin s + 1) [item']) (bin s) (index s + 1)
          else \<comment>\<open>Predict\<close>
            undefined
        )
      | None \<Rightarrow> undefined \<comment>\<open>Complete\<close>
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

definition earley_recognised :: "state \<Rightarrow> bool" where \<comment>\<open>TODO: call earley with inital state\<close>
  "earley_recognised s \<longleftrightarrow> find is_finished ((bins s)!length doc) \<noteq> None"

end

context LocalLexing begin

definition Predict :: "nat \<Rightarrow> items \<Rightarrow> items"
where
  "Predict k I = I \<union>  
     { init_item r k | r x. r \<in> \<RR> \<and> x \<in> bin I k \<and> 
       next_symbol x = Some(fst r) }"

definition Complete :: "nat \<Rightarrow> items \<Rightarrow> items"
where
  "Complete k I = I \<union> { inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y) }"
      
definition \<pi> :: "nat \<Rightarrow> token set \<Rightarrow> items \<Rightarrow> items"
where
  "\<pi> k T I = 
     limit (\<lambda> I. Scan T k (Complete k (Predict k I))) I"

fun \<J> :: "nat \<Rightarrow> nat \<Rightarrow> items"
and \<I> :: "nat \<Rightarrow> items"
and \<T> :: "nat \<Rightarrow> nat \<Rightarrow> token set"
where
  "\<J> 0 0 = \<pi> 0 {} Init"
| "\<J> k (Suc u) = \<pi> k (\<T> k (Suc u)) (\<J> k u)"
| "\<J> (Suc k) 0 = \<pi> (Suc k) {} (\<I> k)"
| "\<T> k 0 = {}"
| "\<T> k (Suc u) = Tokens k (\<T> k u) (\<J> k u)"
| "\<I> k = natUnion (\<J> k)"

definition \<II> :: "items"
where
  "\<II> = \<I> (length Doc)"

end


end
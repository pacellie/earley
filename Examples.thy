theory Examples
  imports Earley_List
begin

subsection \<open>Misc Code equations\<close>

fun contains :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "contains _ [] = False"
| "contains f (x#xs) = (if f x then True else contains f xs)"

fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "all _ [] = True"
| "all P (x#xs) \<longleftrightarrow> P x \<and> all P xs"

lemma contains_iff_exists:
  "contains P xs \<longleftrightarrow> (\<exists>x \<in> set xs. P x)"
  by (induction xs) auto

lemma all_iff_forall:
  "all P xs \<longleftrightarrow> (\<forall>x \<in> set xs. P x)"
  by (induction xs) auto

context Earley_List
begin

lemma [code]:
  "is_terminal t = contains (\<lambda>t'. t = t') terminals"
  using contains_iff_exists is_terminal_def valid_terminals by auto

lemma [code]:
  "wf_item x = (contains (\<lambda>r. r = item_rule x) rules \<and>
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and>
    item_end x \<le> length inp)"
  unfolding wf_item_def using contains_iff_exists valid_rules by auto

lemma [code]:
  "wf_bin k b = (distinct (items b) \<and> all (\<lambda>x. wf_item x \<and> item_end x = k) (items b))"
  unfolding wf_bin_def using all_iff_forall by auto

lemma [code]:
  "wf_bins bs = (all (\<lambda>(k, b). wf_bin k b) (zip [0..<length (bins bs)] (bins bs)))"
  unfolding wf_bins_def all_iff_forall sorry

(*
definition wf_item :: "'a item \<Rightarrow> bool" where 
  "wf_item x = (
    item_rule x \<in> \<RR> \<and> 
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length inp)"

definition wf_bin :: "nat \<Rightarrow> 'a bin \<Rightarrow> bool" where
  "wf_bin k b \<longleftrightarrow> distinct (items b) \<and> (\<forall>x \<in> set (items b). wf_item x \<and> item_end x = k)"

definition wf_bins :: "'a bins \<Rightarrow> bool" where
  "wf_bins bs \<longleftrightarrow> (\<forall>k < length (bins bs). wf_bin k (bins bs ! k))"
*)

end

subsection \<open>Example 1\<close>

(*
locale CFG =
  fixes \<NN> :: "symbol set" <-- use "'a set" instead everywhere?
  fixes \<TT> :: "symbol set"
  fixes \<RR> :: "rule set"
  fixes \<SS> :: "symbol"
  assumes disjunct_symbols: "\<NN> \<inter> \<TT> = {}"
  assumes startsymbol_dom: "\<SS> \<in> \<NN>"
  assumes validRules: "\<forall> (N, \<alpha>) \<in> \<RR>. N \<in> \<NN> \<and> (\<forall> s \<in> set \<alpha>. s \<in> \<NN> \<union> \<TT>)"

locale Earley_Set = CFG +
  fixes inp :: "symbol list" <-- HERE
  assumes valid_inp: "set inp \<subseteq> \<TT>"
  assumes finite: "finite \<RR>"

locale Earley_List = Earley_Set +
  fixes rules :: "rule list"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
  assumes nonempty_deriv: "N \<in> \<NN> \<Longrightarrow> \<not> derives [N] []"
*)

datatype t = a | plus
datatype n = S
datatype s = Terminal t | Nonterminal n

definition grammar :: "s rule list" where
  "grammar = [
    (Nonterminal S, [Terminal a]),
    (Nonterminal S, [Nonterminal S, Terminal plus, Nonterminal S])
  ]"

definition terminals :: "s list" where
  "terminals = [Terminal a, Terminal plus]"

definition nonterminals :: "s list" where
  "nonterminals = [Nonterminal S]"

definition inp :: "s list" where
  "inp = [Terminal a]"

global_interpretation earley: Earley_List "set nonterminals" "set terminals" "set grammar" "Nonterminal S" inp grammar terminals
  defines init = earley.Init_it
      and scan = earley.Scan_it
      and predict = earley.Predict_it
      and complete = earley.Complete_it
      and \<pi>' = earley.\<pi>_it'
      and \<pi> = earley.\<pi>_it
      and \<I> = earley.\<I>_it
      and \<II> = earley.\<II>_it
  apply unfold_locales
      apply (auto simp: nonterminals_def terminals_def grammar_def inp_def)
  sorry

value \<II>

end
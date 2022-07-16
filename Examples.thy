theory Examples
  imports Earley_List
begin

subsection \<open>Problem 1\<close>

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

definition terminals :: "s set" where
  "terminals = {Terminal a, Terminal plus}"

definition nonterminals :: "s set" where
  "nonterminals = {Nonterminal S}"

definition inp :: "s list" where
  "inp = [Terminal a]"

global_interpretation earley: Earley_List nonterminals terminals "set grammar" "Nonterminal S" inp grammar
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
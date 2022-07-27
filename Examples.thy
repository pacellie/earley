theory Examples
  imports Earley_List
begin

text\<open>
  \<^item> Customize Parts of LocalLexing:
    typedecl, sets -> lists for code export and less duplication, move around assumptions
  \<^item> Termination Proof: Done.
    Question: Slow code, is it solvable or different approach with typedef?
  \<^item> Grammar Example: Done.
    Question: Howto locales + proof by eval (see below)
  \<^item> Next:
    Monpoly Grammar example
    Parse Trees via 'pointer'/indices
\<close>

subsection \<open>Example 1\<close>

(*
locale CFG =
  fixes \<NN> :: "'a list"
  fixes \<TT> :: "'a list"
  fixes \<RR> :: "'a rule list"
  fixes \<SS> :: "'a"
  assumes disjunct_symbols: "set \<NN> \<inter> set \<TT> = {}"
  assumes univ_symbols: "set \<NN> \<union> set \<TT> = UNIV"
  assumes startsymbol_dom: "\<SS> \<in> set \<NN>"
  assumes valid_rules: "\<forall>(N, \<alpha>) \<in> set \<RR>. N \<in> set \<NN> \<and> (\<forall>s \<in> set \<alpha>. s \<in> set \<NN> \<union> set \<TT>)"

locale Earley_Set = CFG +
  fixes inp :: "'a list"

locale Earley_List = Earley_Set +
  assumes distinct_rules: "distinct \<RR>"
  assumes nonempty_deriv: "N \<in> set \<NN> \<Longrightarrow> \<not> derives [N] []"
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

global_interpretation cfg: CFG nonterminals terminals grammar "Nonterminal S"
  defines is_terminal = cfg.is_terminal
      and \<epsilon>_free = cfg.\<epsilon>_free
  apply unfold_locales
  apply (auto simp: nonterminals_def terminals_def grammar_def)
  using n.exhaust s.exhaust t.exhaust by metis

value \<epsilon>_free
thm CFG.\<epsilon>_free_impl_non_empty_deriv

global_interpretation earley: Earley_List "nonterminals" "terminals" "grammar" "Nonterminal S" for inp
  defines is_finished = earley.is_finished
      and wf_item = earley.wf_item
      and wf_bin = earley.wf_bin
      and wf_bins = earley.wf_bins
      and init = earley.Init_it
      and scan = earley.Scan_it
      and predict = earley.Predict_it
      and complete = earley.Complete_it
      and \<pi>' = earley.\<pi>_it'
      and \<pi> = earley.\<pi>_it
      and \<I> = earley.\<I>_it
      and \<II> = earley.\<II>_it
      and earley_recognized = earley.earley_recognized_it
  apply unfold_locales
  apply (auto simp: nonterminals_def terminals_def grammar_def)[1]
  apply (auto simp: grammar_def)[1]
  subgoal for N
    using CFG.\<epsilon>_free_impl_non_empty_deriv
    sorry
  done

definition inp :: "s list" where
  "inp = [Terminal a, Terminal plus, Terminal a, Terminal plus, Terminal a]"

value "\<II> inp"
value "earley_recognized inp"

export_code earley_recognized in SML

subsection \<open>Monpoly Grammar Example - TODO\<close>

end
theory Examples
  imports Earley_List
begin

subsection \<open>Example 1\<close>

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

global_interpretation earley: Earley_List "nonterminals" "terminals" "grammar" "Nonterminal S" for inp
  defines is_finished = earley.is_finished
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
  subgoal premises prems for N
  proof -
    have "CFG.\<epsilon>_free [(Nonterminal S, [Terminal a]), (Nonterminal S, [Nonterminal S, Terminal plus, Nonterminal S])]"
      by (metis cfg.\<epsilon>_free_def List.list.set(1,2) \<epsilon>_free_def empty_iff grammar_def insert_iff rule_body_def snd_conv)
    thus ?thesis
      by (metis CFG.\<epsilon>_free_impl_non_empty_deriv cfg.CFG_axioms grammar_def prems)
  qed
  done

definition inp :: "s list" where
  "inp = [Terminal a, Terminal plus, Terminal a, Terminal plus, Terminal a]"

value "\<II> inp"
value "earley_recognized inp"

export_code earley_recognized in SML

end
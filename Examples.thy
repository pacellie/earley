theory Examples
  imports Earley_List
begin

subsection \<open>Example 1\<close>

datatype t = a | plus
datatype n = S
datatype s = Terminal t | Nonterminal n

definition nonterminals :: "s list" where
  "nonterminals = [Nonterminal S]"

definition terminals :: "s list" where
  "terminals = [Terminal a, Terminal plus]"

definition rules :: "s rule list" where
  "rules = [
    (Nonterminal S, [Terminal a]),
    (Nonterminal S, [Nonterminal S, Terminal plus, Nonterminal S])
  ]"

definition start_symbol :: s where
  "start_symbol = Nonterminal S"

definition cfg :: "s cfg" where
  "cfg = CFG nonterminals terminals rules start_symbol"

definition inp :: "s list" where
  "inp = [Terminal a, Terminal plus, Terminal a, Terminal plus, Terminal a]"

lemmas cfg_defs = cfg_def nonterminals_def terminals_def rules_def start_symbol_def

lemma wf_cfg:
  "wf_cfg cfg"
  by (auto simp: wf_cfg_defs cfg_defs)

lemma is_word_inp:
  "is_word cfg inp"
  by (auto simp: is_word_def is_terminal_def cfg_defs inp_def)

lemma nonempty_derives:
  "nonempty_derives cfg"
  by (auto simp: \<epsilon>_free_def cfg_defs rule_body_def nonempty_derives_def \<epsilon>_free_impl_non_empty_deriv)

lemma correctness:
  "earley_recognized_it cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
  using correctness_list wf_cfg is_word_inp nonempty_derives by blast

value "\<II>_it cfg inp"
value "earley_recognized_it cfg inp"

export_code earley_recognized_it in SML

end
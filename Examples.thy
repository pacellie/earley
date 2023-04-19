theory Examples
  imports Earley_List
begin

declare [[names_short]]

subsection \<open>Example 1: Addition\<close>

datatype t1 = x | plus
datatype n1 = S
datatype s1 = Terminal t1 | Nonterminal n1

definition nonterminals1 :: "s1 list" where
  "nonterminals1 = [Nonterminal S]"

definition terminals1 :: "s1 list" where
  "terminals1 = [Terminal x, Terminal plus]"

definition rules1 :: "s1 rule list" where
  "rules1 = [
    (Nonterminal S, [Terminal x]),
    (Nonterminal S, [Nonterminal S, Terminal plus, Nonterminal S])
  ]"

definition start_symbol1 :: s1 where
  "start_symbol1 = Nonterminal S"

definition cfg1 :: "s1 cfg" where
  "cfg1 = CFG nonterminals1 terminals1 rules1 start_symbol1"

definition inp1 :: "s1 list" where
  "inp1 = [Terminal x, Terminal plus, Terminal x, Terminal plus, Terminal x]"

lemmas cfg1_defs = cfg1_def nonterminals1_def terminals1_def rules1_def start_symbol1_def

lemma wf_cfg1:
  "wf_cfg cfg1"
  by (auto simp: wf_cfg_defs cfg1_defs)

lemma is_word_inp1:
  "is_word cfg1 inp1"
  by (auto simp: is_word_def is_terminal_def cfg1_defs inp1_def)

lemma nonempty_derives1:
  "nonempty_derives cfg1"
  by (auto simp: \<epsilon>_free_def cfg1_defs rule_body_def nonempty_derives_def \<epsilon>_free_impl_non_empty_deriv)

lemma correctness1:
  "earley_recognized_it (\<II>_it cfg1 inp1) cfg1 inp1 \<longleftrightarrow> derives cfg1 [\<SS> cfg1] inp1"
  using correctness_list wf_cfg1 is_word_inp1 nonempty_derives1 by blast

value "\<II>_it cfg1 inp1"
value "earley_recognized_it (\<II>_it cfg1 inp1) cfg1 inp1"
value "build_trees cfg1 inp1 (\<II>_it cfg1 inp1)"
value "map_option (map trees) (build_trees cfg1 inp1 (\<II>_it cfg1 inp1))"

subsection \<open>Example 2: Addition performance sanity check\<close>

fun size_bins :: "'a bins \<Rightarrow> nat" where
  "size_bins bs = fold (+) (map length bs) 0"

definition inp1' :: "s1 list" where
  "inp1' = [
    Terminal x, Terminal plus, Terminal x, Terminal plus, Terminal x
  ]"

lemma is_word_inp1':
  "is_word cfg1 inp1'"
  by (auto simp: is_word_def is_terminal_def cfg1_defs inp1'_def)

lemma correctness1':
  "earley_recognized_it (\<II>_it cfg1 inp1') cfg1 inp1' \<longleftrightarrow> derives cfg1 [\<SS> cfg1] inp1'"
  using correctness_list wf_cfg1 is_word_inp1' nonempty_derives1 by blast

value "\<II>_it cfg1 inp1'"
value "size_bins (\<II>_it cfg1 inp1')"
value "earley_recognized_it (\<II>_it cfg1 inp1') cfg1 inp1'"
value "build_trees cfg1 inp1' (\<II>_it cfg1 inp1')"
value "map_option (map trees) (build_trees cfg1 inp1' (\<II>_it cfg1 inp1'))"
value "map_option (foldl (+) 0 \<circ> map length) (map_option (map trees) (build_trees cfg1 inp1' (\<II>_it cfg1 inp1')))"

subsection \<open>Example 3: Cyclic reduction pointers\<close>

datatype t2 = x
datatype n2 = A | B
datatype s2 = Terminal t2 | Nonterminal n2

definition nonterminals2 :: "s2 list" where
  "nonterminals2 = [Nonterminal A, Nonterminal B]"

definition terminals2 :: "s2 list" where
  "terminals2 = [Terminal x]"

definition rules2 :: "s2 rule list" where
  "rules2 = [
    (Nonterminal B, [Nonterminal A]),
    (Nonterminal A, [Nonterminal B]),
    (Nonterminal A, [Terminal x])
  ]"

definition start_symbol2 :: s2 where
  "start_symbol2 = Nonterminal A"

definition cfg2 :: "s2 cfg" where
  "cfg2 = CFG nonterminals2 terminals2 rules2 start_symbol2"

definition inp2 :: "s2 list" where
  "inp2 = [Terminal x]"

lemmas cfg2_defs = cfg2_def nonterminals2_def terminals2_def rules2_def start_symbol2_def

lemma wf_cfg2:
  "wf_cfg cfg2"
  by (auto simp: wf_cfg_defs cfg2_defs)

lemma is_word_inp2:
  "is_word cfg2 inp2"
  by (auto simp: is_word_def is_terminal_def cfg2_defs inp2_def)

lemma nonempty_derives2:
  "nonempty_derives cfg2"
  by (auto simp: \<epsilon>_free_def cfg2_defs rule_body_def nonempty_derives_def \<epsilon>_free_impl_non_empty_deriv)

lemma correctness2:
  "earley_recognized_it (\<II>_it cfg2 inp2) cfg2 inp2 \<longleftrightarrow> derives cfg2 [\<SS> cfg2] inp2"
  using correctness_list wf_cfg2 is_word_inp2 nonempty_derives2 by blast

value "\<II>_it cfg2 inp2"
value "earley_recognized_it (\<II>_it cfg2 inp2) cfg2 inp2"
value "build_trees cfg2 inp2 (\<II>_it cfg2 inp2)"
value "map_option (map trees) (build_trees cfg2 inp2 (\<II>_it cfg2 inp2))"

end
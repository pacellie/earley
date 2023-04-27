(*<*)
theory "06_Examples"
  imports
    "../Examples"
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter \<open>Examples\<close>

section \<open>epsilon free CFG\<close>

definition \<epsilon>_free :: "'a cfg \<Rightarrow> bool" where
  "\<epsilon>_free cfg \<longleftrightarrow> (\<forall>r \<in> set (\<RR> cfg). rule_body r \<noteq> [])"

lemma \<epsilon>_free_impl_non_empty_deriv:
  "\<epsilon>_free cfg \<Longrightarrow> N \<in> set (\<NN> cfg) \<Longrightarrow> \<not> derives cfg [N] []"
(*<*)
  sorry  
(*>*)

section \<open>Example 1: Addition\<close>

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

lemma wf_cfg1:
  "wf_cfg cfg1"
(*<*)
  sorry  
(*>*)

lemma is_word_inp1:
  "is_word cfg1 inp1"
(*<*)
  sorry  
(*>*)

lemma nonempty_derives1:
  "nonempty_derives cfg1"
(*<*)
  sorry  
(*>*)

lemma correctness1:
  "earley_recognized_it (\<II>_it cfg1 inp1) cfg1 inp1 \<longleftrightarrow> derives cfg1 [\<SS> cfg1] inp1"
(*<*)
  sorry  
(*>*)

fun size_bins :: "'a bins \<Rightarrow> nat" where
  "size_bins bs = fold (+) (map length bs) 0"

value "\<II>_it cfg1 inp1"
value "size_bins (\<II>_it cfg1 inp1)"
value "earley_recognized_it (\<II>_it cfg1 inp1) cfg1 inp1"
value "build_trees cfg1 inp1 (\<II>_it cfg1 inp1)"
value "map_option (map trees) (build_trees cfg1 inp1 (\<II>_it cfg1 inp1))"
value "map_option (foldl (+) 0 \<circ> map length) (map_option (map trees) (build_trees cfg1 inp1 (\<II>_it cfg1 inp1)))"

subsection \<open>Example 2: Cyclic reduction pointers\<close>

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

lemma wf_cfg2:
  "wf_cfg cfg2"
(*<*)
  sorry  
(*>*)

lemma is_word_inp2:
  "is_word cfg2 inp2"
(*<*)
  sorry  
(*>*)

lemma nonempty_derives2:
  "nonempty_derives cfg2"
(*<*)
  sorry  
(*>*)

lemma correctness2:
  "earley_recognized_it (\<II>_it cfg2 inp2) cfg2 inp2 \<longleftrightarrow> derives cfg2 [\<SS> cfg2] inp2"
(*<*)
  sorry  
(*>*)

value "\<II>_it cfg2 inp2"
value "earley_recognized_it (\<II>_it cfg2 inp2) cfg2 inp2"
value "build_trees cfg2 inp2 (\<II>_it cfg2 inp2)"
value "map_option (map trees) (build_trees cfg2 inp2 (\<II>_it cfg2 inp2))"

(*<*)
end
(*>*)
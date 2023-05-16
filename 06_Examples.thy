(*<*)
theory "06_Examples"
  imports
    "05_Earley_Parser"
begin
(*>*)

chapter \<open>Usage\<close>

definition \<epsilon>_free :: "'a cfg \<Rightarrow> bool" where
  "\<epsilon>_free cfg \<longleftrightarrow> (\<forall>r \<in> set (\<RR> cfg). rule_body r \<noteq> [])"

lemma \<epsilon>_free_impl_non_empty_deriv:
  "\<epsilon>_free cfg \<Longrightarrow> N \<in> set (\<NN> cfg) \<Longrightarrow> \<not> derives cfg [N] []"
(*<*)
  sorry  
(*>*)

datatype t = x | plus
datatype n = S
datatype s = Terminal t | Nonterminal n

definition nonterminals :: "s list" where
  "nonterminals = [Nonterminal S]"

definition terminals :: "s list" where
  "terminals = [Terminal x, Terminal plus]"

definition rules :: "s rule list" where
  "rules = [
    (Nonterminal S, [Terminal x]),
    (Nonterminal S, [Nonterminal S, Terminal plus, Nonterminal S])
  ]"

definition start_symbol :: s where
  "start_symbol = Nonterminal S"

definition cfg :: "s cfg" where
  "cfg = CFG nonterminals terminals rules start_symbol"

definition \<omega> :: "s list" where
  "\<omega> = [Terminal x, Terminal plus, Terminal x, Terminal plus, Terminal x]"

lemma wf_cfg:
  shows "wf_cfg cfg"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma is_sentence_\<omega>:
  shows "is_sentence cfg \<omega>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma nonempty_derives:
  shows "nonempty_derives cfg"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma correctness:
  shows "recognizing_list (\<E>arley_list cfg \<omega>) cfg \<omega> \<longleftrightarrow> derives cfg [\<SS> cfg] \<omega>"
(*<*)
  sorry  
(*>*)

(*<*)
end
(*>*)
(*<*)
theory "06_Examples"
  imports
    "05_Earley_Parser"
begin
(*>*)

chapter \<open>The Running Example\<close>

definition \<epsilon>_free :: "'a cfg \<Rightarrow> bool" where
  "\<epsilon>_free \<G> \<longleftrightarrow> (\<forall>r \<in> set (\<RR> \<G>). rule_body r \<noteq> [])"

lemma \<epsilon>_free_impl_non_empty_deriv:
  "\<epsilon>_free \<G> \<Longrightarrow> N \<in> set (\<NN> \<G>) \<Longrightarrow> \<not> (\<G> \<turnstile> [N] \<Rightarrow>\<^sup>* [])"
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

definition \<G> :: "s cfg" where
  "\<G> = CFG nonterminals terminals rules start_symbol"

definition \<omega> :: "s list" where
  "\<omega> = [Terminal x, Terminal plus, Terminal x, Terminal plus, Terminal x]"

lemma wf_\<G>:
  shows "wf_\<G> \<G>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma is_sentence_\<omega>:
  shows "is_sentence \<G> \<omega>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma nonempty_derives:
  shows "nonempty_derives \<G>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma correctness:
  shows "recognizing_list (\<E>arley_list \<G> \<omega>) \<G> \<omega> \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry  
(*>*)

(*<*)
end
(*>*)
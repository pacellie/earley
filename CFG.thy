theory CFG
  imports Main
begin

section \<open>Adjusted content from AFP/LocalLexing\<close>

datatype ('a, 'b) symbol = T 'a | NT 'b

type_synonym ('a, 'b) rule = "('a, 'b) symbol \<times> ('a, 'b) symbol list"

type_synonym ('a, 'b) sentence = "('a, 'b) symbol list"

datatype ('a, 'b) cfg =
   CFG (\<RR> : "('a, 'b) rule list") (\<SS> : "('a, 'b) symbol")

definition wf_\<G> :: "('a, 'b) cfg \<Rightarrow> bool" where
  "wf_\<G> \<G> \<equiv> distinct (\<RR> \<G>) \<and> (\<forall>N \<alpha>. (N, \<alpha>) \<in> set (\<RR> \<G>) \<longrightarrow> (\<exists>b. N = NT b)) \<and> (\<exists>b. \<SS> \<G> = NT b)"

definition is_terminal :: "('a, 'b) symbol \<Rightarrow> bool" where
  "is_terminal x \<equiv> \<exists>a. x = T a"

definition is_nonterminal :: "('a, 'b) symbol \<Rightarrow> bool" where
  "is_nonterminal x \<equiv> \<exists>b. x = NT b"

lemma is_nonterminal_startsymbol:
  "wf_\<G> \<G> \<Longrightarrow> is_nonterminal (\<SS> \<G>)"
  by (simp add: is_nonterminal_def wf_\<G>_def)

definition is_word :: "('a, 'b) sentence \<Rightarrow> bool" where
  "is_word \<omega> \<equiv> \<forall>x \<in> set \<omega>. is_terminal x"

definition derives1 :: "('a, 'b) cfg \<Rightarrow> ('a, 'b) sentence \<Rightarrow> ('a, 'b) sentence \<Rightarrow> bool" where
  "derives1 \<G> u v \<equiv> \<exists> x y N \<alpha>. 
    u = x @ [N] @ y \<and>
    v = x @ \<alpha> @ y \<and>
    (N, \<alpha>) \<in> set (\<RR> \<G>)"  

definition derivations1 :: "('a, 'b) cfg \<Rightarrow> (('a, 'b) sentence \<times> ('a, 'b) sentence) set" where
  "derivations1 \<G> \<equiv> { (u,v) | u v. derives1 \<G> u v }"

definition derivations :: "('a, 'b) cfg \<Rightarrow> (('a, 'b) sentence \<times> ('a, 'b) sentence) set" where 
  "derivations \<G> \<equiv> (derivations1 \<G>)^*"

definition derives :: "('a, 'b) cfg \<Rightarrow> ('a, 'b) sentence \<Rightarrow> ('a, 'b) sentence \<Rightarrow> bool" where
  "derives \<G> u v \<equiv> ((u, v) \<in> derivations \<G>)"

end
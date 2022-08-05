theory CFG
  imports Main
begin

section \<open>Slightly adjusted content from AFP/LocalLexing\<close>

type_synonym 'a rule = "'a \<times> 'a list"

type_synonym 'a rules = "'a rule list"

type_synonym 'a sentence = "'a list"

locale CFG =
  fixes \<NN> :: "'a list"
  fixes \<TT> :: "'a list"
  fixes \<RR> :: "'a rule list"
  fixes \<SS> :: "'a"
  assumes disjunct_symbols: "set \<NN> \<inter> set \<TT> = {}"
  assumes univ_symbols: "set \<NN> \<union> set \<TT> = UNIV"
  assumes startsymbol_dom: "\<SS> \<in> set \<NN>"
  assumes valid_rules: "\<forall>(N, \<alpha>) \<in> set \<RR>. N \<in> set \<NN> \<and> (\<forall>s \<in> set \<alpha>. s \<in> set \<NN> \<union> set \<TT>)"
begin

definition is_terminal :: "'a \<Rightarrow> bool" where
  "is_terminal s = (s \<in> set \<TT>)"

definition is_nonterminal :: "'a \<Rightarrow> bool" where
  "is_nonterminal s = (s \<in> set \<NN>)"

lemma is_nonterminal_startsymbol: "is_nonterminal \<SS>"
  by (simp add: is_nonterminal_def startsymbol_dom)

definition is_word :: "'a sentence \<Rightarrow> bool" where
  "is_word s = (\<forall>x \<in> set s. is_terminal x)"
   
definition derives1 :: "'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "derives1 u v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> (N, \<alpha>) \<in> set \<RR>)"  

definition derivations1 :: "('a sentence \<times> 'a sentence) set" where
  "derivations1 = { (u,v) | u v. derives1 u v }"

definition derivations :: "('a sentence \<times> 'a sentence) set" where 
  "derivations = derivations1^*"

definition derives :: "'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "derives u v = ((u, v) \<in> derivations)"

definition is_derivation :: "'a sentence \<Rightarrow> bool" where
  "is_derivation u = derives [\<SS>] u"

definition \<L> :: "'a sentence set" where
  "\<L> = { v | v. is_word v \<and> is_derivation v}"

definition "\<L>\<^sub>P"  :: "'a sentence set" where
  "\<L>\<^sub>P = { u | u v. is_word u \<and> is_derivation (u@v) }"

end

end
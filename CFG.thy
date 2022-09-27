theory CFG
  imports Main
begin

section \<open>Slightly adjusted content from AFP/LocalLexing\<close>

type_synonym 'a rule = "'a \<times> 'a list"

type_synonym 'a rules = "'a rule list"

type_synonym 'a sentence = "'a list"

datatype 'a cfg = 
  CFG 
    (\<NN> : "'a list") 
    (\<TT> : "'a list") 
    (\<RR> : "'a rules")
    (\<SS> : "'a")

definition disjunct_symbols :: "'a cfg \<Rightarrow> bool" where
  "disjunct_symbols cfg \<longleftrightarrow> set (\<NN> cfg) \<inter> set (\<TT> cfg) = {}"

definition valid_startsymbol :: "'a cfg \<Rightarrow> bool" where
  "valid_startsymbol cfg \<longleftrightarrow> \<SS> cfg \<in> set (\<NN> cfg)"

definition valid_rules :: "'a cfg \<Rightarrow> bool" where
  "valid_rules cfg \<longleftrightarrow> (\<forall>(N, \<alpha>) \<in> set (\<RR> cfg). N \<in> set (\<NN> cfg) \<and> (\<forall>s \<in> set \<alpha>. s \<in> set (\<NN> cfg) \<union> set (\<TT> cfg)))"

definition distinct_rules :: "'a cfg \<Rightarrow> bool" where
  "distinct_rules cfg = distinct (\<RR> cfg)"

definition wf_cfg :: "'a cfg \<Rightarrow> bool" where
  "wf_cfg cfg \<longleftrightarrow> disjunct_symbols cfg \<and> valid_startsymbol cfg \<and> valid_rules cfg \<and> distinct_rules cfg"

lemmas wf_cfg_defs = wf_cfg_def valid_rules_def valid_startsymbol_def disjunct_symbols_def distinct_rules_def

definition is_terminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_terminal cfg s = (s \<in> set (\<TT> cfg))"

definition is_nonterminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_nonterminal cfg s = (s \<in> set (\<NN> cfg))"

definition is_symbol :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_symbol cfg s \<longleftrightarrow> is_terminal cfg s \<or> is_nonterminal cfg s"

definition wf_sentence :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "wf_sentence cfg s = (\<forall>x \<in> set s. is_symbol cfg x)"

lemma is_nonterminal_startsymbol: "wf_cfg cfg \<Longrightarrow> is_nonterminal cfg (\<SS> cfg)"
  by (simp add: is_nonterminal_def wf_cfg_defs)

definition is_word :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "is_word cfg s = (\<forall>x \<in> set s. is_terminal cfg x)"
   
definition derives1 :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "derives1 cfg u v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> (N, \<alpha>) \<in> set (\<RR> cfg))"  

definition derivations1 :: "'a cfg \<Rightarrow> ('a sentence \<times> 'a sentence) set" where
  "derivations1 cfg = { (u,v) | u v. derives1 cfg u v }"

definition derivations :: "'a cfg \<Rightarrow> ('a sentence \<times> 'a sentence) set" where 
  "derivations cfg = (derivations1 cfg)^*"

definition derives :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "derives cfg u v = ((u, v) \<in> derivations cfg)"

definition is_derivation :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "is_derivation cfg u = derives cfg [\<SS> cfg] u"

definition \<L> :: "'a cfg \<Rightarrow> 'a sentence set" where
  "\<L> cfg = { v | v. is_word cfg v \<and> is_derivation cfg v}"

definition "\<L>\<^sub>P"  :: "'a cfg \<Rightarrow> 'a sentence set" where
  "\<L>\<^sub>P cfg = { u | u v. is_word cfg u \<and> is_derivation cfg (u@v) }"

end
(*<*)
theory "02_Earleys_Algorithm"
  imports
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter\<open>Earley's Algorithm\<close>

text\<open>TODO: Add nicer syntax for derives\<close>

text\<open>
  \begin{itemize}
    \item Introduce background theory about CFG
    \item Introduce the Earley recognizer in the abstract set form with pointer, note the original error in Earley's algorithm \\
    \item Introduce the running example S -> x | S + S for input x + x + x \\
    \item Illustrate the complete bins generated by the example \\
    \item Illustrate Initial S -> .alpha,0,0, Scan A -> alpha.abeta,i,j | A -> alpha.beta,i,j+1,
      Predict A -> alpha.Bbeta,i,j and B -> gamma | B -> .gamma,j,j,
      Complete A -> alpha.Bbeta,i,j and B -> gamma.,j,k | A -> alphaB.beta,i,k \\
    \item Define goal: A -> alpha.beta,i,j iff A =>* s[i..j)beta which implies S -> alpha.,0,n+1 iff S =>* s \\
  \end{itemize}
\<close>

section\<open>Background Theory\<close>

text\<open>use snippets\<close>

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

definition is_terminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_terminal cfg s = (s \<in> set (\<TT> cfg))"

definition is_nonterminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_nonterminal cfg s = (s \<in> set (\<NN> cfg))"

definition is_symbol :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_symbol cfg s \<longleftrightarrow> is_terminal cfg s \<or> is_nonterminal cfg s"

definition wf_sentence :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "wf_sentence cfg s = (\<forall>x \<in> set s. is_symbol cfg x)"

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


section\<open>Earley Recognizer\<close>

(*<*)
end
(*>*)
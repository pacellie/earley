(*<*)
theory "06_Examples"
  imports
    "05_Earley_Parser"
begin
(*>*)

chapter \<open>The Running Example in Isabelle\<close>

text\<open>
This chapter illustrates how the running example is implemented in Isabelle and highlights
the corresponding correctness theorems for functions @{term \<E>arley_list}, @{term build_tree}, and
@{term build_forests}. But first we make a small addition to easily compute if a grammar allows empty
derivations, or if @{term "\<G> \<turnstile> [N] \<Rightarrow>\<^sup>* []"} holds for any non-terminal $N$ of grammar @{term \<G>}. We call
a grammar @{term "\<epsilon>_free"} if there does not exists any production rule of the form $N \rightarrow \, \epsilon$.
For a well-formed grammar, strictly speaking we only require the left-hand side of any production rule
to be a non-terminal, we then prove a lemma stating that a grammar does only allow non-empty derivations
for any non-terminal if and only if it is epsilon-free.
\<close>

definition \<epsilon>_free :: "'a cfg \<Rightarrow> bool" where
  "\<epsilon>_free \<G> \<equiv> \<forall>r \<in> set (\<RR> \<G>). rule_body r \<noteq> []"

lemma nonempty_derives_iff_\<epsilon>_free:
  assumes "wf_\<G> \<G>"
  shows "nonempty_derives \<G> \<longleftrightarrow> \<epsilon>_free \<G>"
(*<*)
  sorry  
(*>*)

text\<open>
Next we define the grammar $S ::= S + S \,\, | \,\, x$ in Isabelle. We introduce data types @{term T}, @{term N}, and @{term symbol}
respectively representing terminal symbols $\{x, +\}$, the non-terminal $S$, and the type of symbols.
Subsequently, we define the grammar as its four constituents: a list of non-terminal symbols, a list of terminal symbols,
the production rules, and the start symbol. Finally, we specify the input $\omega = x + x + x$.
\<close>

datatype T = x | plus
datatype N = S
datatype symbol = Terminal T | Nonterminal N

definition nonterminals :: "symbol list" where
  "nonterminals = [Nonterminal S]"

definition terminals :: "symbol list" where
  "terminals = [Terminal x, Terminal plus]"

definition rules :: "symbol rule list" where
  "rules = [
    (Nonterminal S, [Terminal x]),
    (Nonterminal S, [Nonterminal S, Terminal plus, Nonterminal S])]"

definition start_symbol :: symbol where
  "start_symbol = Nonterminal S"

definition \<G> :: "symbol cfg" where
  "\<G> = CFG nonterminals terminals rules start_symbol"

definition \<omega> :: "symbol list" where
  "\<omega> = [Terminal x, Terminal plus, Terminal x, Terminal plus, Terminal x]"

text\<open>
The following three lemmas state the well-formedness of the grammar and input. The proofs are automatic
by definition with addition of lemma @{thm[source] nonempty_derives_iff_\<epsilon>_free}.
\<close>

lemma wf_\<G>:
  shows "wf_\<G> \<G>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma nonempty_derives_\<G>:
  shows "nonempty_derives \<G>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma is_sentence_\<omega>:
  shows "is_sentence \<G> \<omega>"
(*<*)
  sorry  
(*>*)

text\<open>
This section concludes by illustrating the following main theorems for functions @{term "mbox0 (\<E>arley_list)"}, @{term build_tree}, and
@{term build_forests} for the well-formed grammar @{term \<G>} and input @{term \<omega>} introduced above.
\<close>

lemma correctness_bins:
  shows "recognizing (bins (\<E>arley_list \<G> \<omega>)) \<G> \<omega> \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma wf_tree:
  assumes "build_tree \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some t"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma correctness_tree:
  shows "(\<exists>t. build_tree \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some t) \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma wf_trees:
  assumes "build_forests \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
(*<*)
  sorry  
(*>*)

text\<open>\<close>

lemma soundness_trees:
  assumes "build_forests \<G> \<omega> (\<E>arley_list \<G> \<omega>) = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry  
(*>*)

(*<*)
end
(*>*)
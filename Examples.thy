theory Examples
  imports Earley_Parser
begin

section \<open>Epsilon productions\<close>

definition \<epsilon>_free :: "('a, 'b) cfg \<Rightarrow> bool" where
  "\<epsilon>_free \<G> \<longleftrightarrow> (\<forall>r \<in> set (\<RR> \<G>). rule_body r \<noteq> [])"

lemma \<epsilon>_free_impl_non_empty_sentence_deriv:
  "\<epsilon>_free \<G> \<Longrightarrow> a \<noteq> [] \<Longrightarrow> \<not> Derivation \<G> a D []"
proof (induction "length D" arbitrary: a D rule: nat_less_induct)
  case 1
  show ?case
  proof (rule ccontr)
    assume assm: "\<not> \<not> Derivation \<G> a D []"
    show False
    proof (cases "D = []")
      case True
      then show ?thesis
        using "1.prems"(2) assm by auto
    next
      case False
      then obtain d D' \<alpha> where *:
        "D = d # D'" "Derives1 \<G> a (fst d) (snd d) \<alpha>" "Derivation \<G> \<alpha> D' []" "snd d \<in> set (\<RR> \<G>)"
        using list.exhaust assm Derives1_def by (metis Derivation.simps(2))
      show ?thesis
      proof cases
        assume "\<alpha> = []"
        thus ?thesis
          using *(2,4) Derives1_split \<epsilon>_free_def rule_body_def "1.prems"(1) by (metis append_is_Nil_conv)
      next
        assume "\<not> \<alpha> = []"
        thus ?thesis
          using *(1,3) "1.hyps" "1.prems"(1) by auto
      qed
    qed
  qed
qed

lemma \<epsilon>_free_impl_non_empty_deriv:
  "\<epsilon>_free \<G> \<Longrightarrow> \<forall>s. \<not> derives \<G> [s] []"
  using \<epsilon>_free_impl_non_empty_sentence_deriv derives_implies_Derivation by (metis not_Cons_self2)

lemma nonempty_deriv_impl_\<epsilon>_free:
  assumes "\<forall>s. \<not> derives \<G> [s] []"
  shows "\<epsilon>_free \<G>"
proof (rule ccontr)
  assume "\<not> \<epsilon>_free \<G>"
  then obtain N \<alpha> where *: "(N, \<alpha>) \<in> set (\<RR> \<G>)" "rule_body (N, \<alpha>) = []"
    unfolding \<epsilon>_free_def by auto
  hence "derives1 \<G> [N] []"
    unfolding derives1_def rule_body_def by auto
  hence "derives \<G> [N] []"
    by auto
  thus False
    using assms(1) by blast
qed

lemma nonempty_deriv_iff_\<epsilon>_free:
  shows "(\<forall>s. \<not> derives \<G> [s] []) \<longleftrightarrow> \<epsilon>_free \<G>"
  using \<epsilon>_free_impl_non_empty_deriv nonempty_deriv_impl_\<epsilon>_free by blast

section \<open>Example 1: Addition\<close>

datatype T1 = x | plus
datatype N1 = S

definition rules1 :: "(T1, N1) rule list" where
  "rules1 = [
    (NT S, [T x]),
    (NT S, [NT S, T plus, NT S])
  ]"

definition start_symbol1 :: "(T1, N1) symbol" where
  "start_symbol1 = NT S"

definition cfg1 :: "(T1, N1) cfg" where
  "cfg1 = CFG rules1 start_symbol1"

definition inp1 :: "(T1, N1) sentence" where
  "inp1 = [T x, T plus, T x, T plus, T x]"

lemmas cfg1_defs = cfg1_def rules1_def start_symbol1_def

lemma wf_\<G>1:
  "wf_\<G> cfg1"
  by (auto simp: wf_\<G>_def cfg1_defs)

lemma is_word_inp1:
  "is_word inp1"
  by (auto simp: is_word_def is_terminal_def cfg1_defs inp1_def)

lemma nonempty_derives1:
  "nonempty_derives cfg1"
  by (auto simp: \<epsilon>_free_def cfg1_defs rule_body_def nonempty_derives_def \<epsilon>_free_impl_non_empty_deriv)

lemma correctness1:
  "recognizing (bins (Earley\<^sub>L cfg1 inp1)) cfg1 inp1 \<longleftrightarrow> derives cfg1 [\<SS> cfg1] inp1"
  using correctness_Earley\<^sub>L wf_\<G>1 is_word_inp1 nonempty_derives1 by blast

lemma wf_tree1:
  assumes "build_tree cfg1 inp1 (Earley\<^sub>L cfg1 inp1) = Some t"
  shows "wf_rule_tree cfg1 t \<and> root_tree t = \<SS> cfg1 \<and> yield_tree t = inp1"
  using assms nonempty_derives1 wf_\<G>1 wf_rule_root_yield_tree_build_tree_Earley\<^sub>L by blast

lemma correctness_tree1:
  "(\<exists>t. build_tree cfg1 inp1 (Earley\<^sub>L cfg1 inp1) = Some t) \<longleftrightarrow> derives cfg1 [\<SS> cfg1] inp1"
  using correctness_build_tree_Earley\<^sub>L is_word_inp1 nonempty_derives1 wf_\<G>1 by blast

lemma wf_trees1:
  assumes "build_trees cfg1 inp1 (Earley\<^sub>L cfg1 inp1) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree cfg1 t \<and> root_tree t = \<SS> cfg1 \<and> yield_tree t = inp1"
  using assms nonempty_derives1 wf_\<G>1 wf_rule_root_yield_tree_build_trees_Earley\<^sub>L by blast

lemma soundness_trees1:
  assumes "build_trees cfg1 inp1 (Earley\<^sub>L cfg1 inp1) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "derives cfg1 [\<SS> cfg1] inp1"
  using assms is_word_inp1 nonempty_derives1 soundness_build_trees_Earley\<^sub>L wf_\<G>1 by blast

section \<open>Example 2: Cyclic reduction pointers\<close>

datatype T2 = x
datatype N2 = A | B

definition rules2 :: "(T2, N2) rule list" where
  "rules2 = [
    (NT B, [NT A]),
    (NT A, [NT B]),
    (NT A, [T x])
  ]"

definition start_symbol2 :: "(T2, N2) symbol" where
  "start_symbol2 = NT A"

definition cfg2 :: "(T2, N2) cfg" where
  "cfg2 = CFG rules2 start_symbol2"

definition inp2 :: "(T2, N2) sentence" where
  "inp2 = [T x]"

lemmas cfg2_defs = cfg2_def rules2_def start_symbol2_def

lemma wf_\<G>2:
  "wf_\<G> cfg2"
  by (auto simp: wf_\<G>_def cfg2_defs)

lemma is_word_inp2:
  "is_word inp2"
  by (auto simp: is_word_def is_terminal_def cfg2_defs inp2_def)

lemma nonempty_derives2:
  "nonempty_derives cfg2"
  by (auto simp: \<epsilon>_free_def cfg2_defs rule_body_def nonempty_derives_def \<epsilon>_free_impl_non_empty_deriv)

lemma correctness2:
  "recognizing (bins (Earley\<^sub>L cfg2 inp2)) cfg2 inp2 \<longleftrightarrow> derives cfg2 [\<SS> cfg2] inp2"
  using correctness_Earley\<^sub>L wf_\<G>2 is_word_inp2 nonempty_derives2 by blast

lemma wf_tree2:
  assumes "build_tree cfg2 inp2 (Earley\<^sub>L cfg2 inp2) = Some t"
  shows "wf_rule_tree cfg2 t \<and> root_tree t = \<SS> cfg2 \<and> yield_tree t = inp2"
  using assms nonempty_derives2 wf_\<G>2 wf_rule_root_yield_tree_build_tree_Earley\<^sub>L by blast

lemma correctness_tree2:
  "(\<exists>t. build_tree cfg2 inp2 (Earley\<^sub>L cfg2 inp2) = Some t) \<longleftrightarrow> derives cfg2 [\<SS> cfg2] inp2"
  using correctness_build_tree_Earley\<^sub>L is_word_inp2 nonempty_derives2 wf_\<G>2 by blast

lemma wf_trees2:
  assumes "build_trees cfg2 inp2 (Earley\<^sub>L cfg2 inp2) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree cfg2 t \<and> root_tree t = \<SS> cfg2 \<and> yield_tree t = inp2"
  using assms nonempty_derives2 wf_\<G>2 wf_rule_root_yield_tree_build_trees_Earley\<^sub>L by blast

lemma soundness_trees2:
  assumes "build_trees cfg2 inp2 (Earley\<^sub>L cfg2 inp2) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "derives cfg2 [\<SS> cfg2] inp2"
  using assms is_word_inp2 nonempty_derives2 soundness_build_trees_Earley\<^sub>L wf_\<G>2 by blast

end
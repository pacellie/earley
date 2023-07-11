theory Examples
  imports Earley_Parser
begin

declare [[names_short]]

subsection \<open>Epsilon Productions\<close>

definition \<epsilon>_free :: "'a cfg \<Rightarrow> bool" where
  "\<epsilon>_free cfg \<longleftrightarrow> (\<forall>r \<in> set (\<RR> cfg). rule_body r \<noteq> [])"

lemma \<epsilon>_free_impl_non_empty_sentence_deriv:
  "\<epsilon>_free cfg \<Longrightarrow> a \<noteq> [] \<Longrightarrow> \<not> Derivation cfg a D []"
proof (induction "length D" arbitrary: a D rule: nat_less_induct)
  case 1
  show ?case
  proof (rule ccontr)
    assume assm: "\<not> \<not> Derivation cfg a D []"
    show False
    proof (cases "D = []")
      case True
      then show ?thesis
        using "1.prems"(2) assm by auto
    next
      case False
      then obtain d D' \<alpha> where *:
        "D = d # D'" "Derives1 cfg a (fst d) (snd d) \<alpha>" "Derivation cfg \<alpha> D' []" "snd d \<in> set (\<RR> cfg)"
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
  "\<epsilon>_free cfg \<Longrightarrow> \<forall>N \<in> set (\<NN> cfg). \<not> derives cfg [N] []"
  using \<epsilon>_free_impl_non_empty_sentence_deriv derives_implies_Derivation by (metis not_Cons_self2)

lemma nonempty_deriv_impl_\<epsilon>_free:
  assumes "\<forall>N \<in> set (\<NN> cfg). \<not> derives cfg [N] []" "\<forall>(N, \<alpha>) \<in> set (\<RR> cfg). N \<in> set (\<NN> cfg)"
  shows "\<epsilon>_free cfg"
proof (rule ccontr)
  assume "\<not> \<epsilon>_free cfg"
  then obtain N \<alpha> where *: "(N, \<alpha>) \<in> set (\<RR> cfg)" "rule_body (N, \<alpha>) = []"
    unfolding \<epsilon>_free_def by auto
  hence "derives1 cfg [N] []"
    unfolding derives1_def rule_body_def by auto
  hence "derives cfg [N] []"
    by auto
  moreover have "N \<in> set (\<NN> cfg)"
    using *(1) assms(2) by blast
  ultimately show False
    using assms(1) by blast
qed

lemma nonempty_deriv_iff_\<epsilon>_free:
  assumes "\<forall>(N, \<alpha>) \<in> set (\<RR> cfg). N \<in> set (\<NN> cfg)"
  shows "(\<forall>N \<in> set (\<NN> cfg). \<not> derives cfg [N] []) \<longleftrightarrow> \<epsilon>_free cfg"
  using \<epsilon>_free_impl_non_empty_deriv nonempty_deriv_impl_\<epsilon>_free[OF _ assms] by blast

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

lemma wf_tree1:
  assumes "build_tree cfg1 inp1 (\<II>_it cfg1 inp1) = Some t"
  shows "wf_rule_tree cfg1 t \<and> root_tree t = \<SS> cfg1 \<and> yield_tree t = inp1"
  using assms nonempty_derives1 wf_cfg1 wf_rule_root_yield_tree_build_tree_\<II>_it by blast

lemma correctness_tree1:
  "(\<exists>t. build_tree cfg1 inp1 (\<II>_it cfg1 inp1) = Some t) \<longleftrightarrow> derives cfg1 [\<SS> cfg1] inp1"
  using correctness_build_tree_\<II>_it is_word_inp1 nonempty_derives1 wf_cfg1 by blast

lemma wf_trees1:
  assumes "build_trees cfg1 inp1 (\<II>_it cfg1 inp1) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree cfg1 t \<and> root_tree t = \<SS> cfg1 \<and> yield_tree t = inp1"
  using assms nonempty_derives1 wf_cfg1 wf_rule_root_yield_tree_build_trees_\<II>_it by blast

lemma soundness_trees1:
  assumes "build_trees cfg1 inp1 (\<II>_it cfg1 inp1) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "derives cfg1 [\<SS> cfg1] inp1"
  using assms is_word_inp1 nonempty_derives1 soundness_build_trees_\<II>_it wf_cfg1 by blast

value "\<II>_it cfg1 inp1"
value "earley_recognized_it (\<II>_it cfg1 inp1) cfg1 inp1"
value "build_trees cfg1 inp1 (\<II>_it cfg1 inp1)"
value "map_option (map trees) (build_trees cfg1 inp1 (\<II>_it cfg1 inp1))"

subsection \<open>Example 2: Addition performance sanity check\<close>

fun size_bins :: "'a bins \<Rightarrow> nat" where
  "size_bins bs = fold (+) (map length bs) 0"

definition inp1' :: "s1 list" where
  "inp1' = [
    Terminal x, Terminal plus, Terminal x, Terminal plus, Terminal x, Terminal plus, Terminal x
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
value "map_option length (build_trees cfg1 inp1' (\<II>_it cfg1 inp1'))"
value "map_option (foldl (+) 0 \<circ> map length) (map_option (map trees) (build_trees cfg1 inp1' (\<II>_it cfg1 inp1')))"

section \<open>Example 3: Cyclic reduction pointers\<close>

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
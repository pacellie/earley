theory Derivations
  imports
    LocalLexing.InductRules
    LocalLexing.ListTools
    CFG
begin

section \<open>Slightly adjusted content from AFP/LocalLexing\<close>

type_synonym 'a derivation = "(nat \<times> 'a rule) list"

lemma [simp]: "is_word cfg []" by (auto simp add: is_word_def)

definition leftderives1 :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "leftderives1 cfg u v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> is_word cfg x
        \<and> (N, \<alpha>) \<in> set (\<RR> cfg))"  

lemma leftderives1_implies_derives1[simp]: "leftderives1 cfg u v \<Longrightarrow> derives1 cfg u v"
  by (auto simp add: leftderives1_def derives1_def)

definition leftderivations1 :: "'a cfg \<Rightarrow> ('a sentence \<times> 'a sentence) set" where
  "leftderivations1 cfg = { (u,v) | u v. leftderives1 cfg u v }"

lemma [simp]: "leftderivations1 cfg \<subseteq> derivations1 cfg"
  by (auto simp add: leftderivations1_def derivations1_def)

definition leftderivations :: "'a cfg \<Rightarrow> ('a sentence \<times> 'a sentence) set" where 
  "leftderivations cfg = (leftderivations1 cfg)^*"

lemma rtrancl_subset_implies: "a \<subseteq> b \<Longrightarrow> a \<subseteq> b^*" by blast

lemma leftderivations_subset_derivations[simp]: "leftderivations cfg \<subseteq> derivations cfg"
  apply (simp add: leftderivations_def derivations_def)
  apply (rule rtrancl_subset_rtrancl)
  apply (rule rtrancl_subset_implies)
  by simp

definition leftderives :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "leftderives cfg u v = ((u, v) \<in> leftderivations cfg)"

lemma leftderives_implies_derives[simp]: "leftderives cfg u v \<Longrightarrow> derives cfg u v"
  apply (auto simp add: leftderives_def derives_def)
  by (rule subsetD[OF leftderivations_subset_derivations])

definition is_leftderivation :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool"  where
  "is_leftderivation cfg u = leftderives cfg [\<SS> cfg] u"

lemma leftderivation_implies_derivation[simp]: 
  "is_leftderivation cfg u \<Longrightarrow> is_derivation cfg u"
  by (simp add: is_leftderivation_def is_derivation_def)

lemma leftderives_refl[simp]: "leftderives cfg u u"
  by (auto simp add: leftderives_def leftderivations_def)

lemma leftderives1_implies_leftderives[simp]:"leftderives1 cfg a b \<Longrightarrow> leftderives cfg a b"
  by (auto simp add: leftderives_def leftderivations_def leftderivations1_def)

lemma leftderives_trans: "leftderives cfg a b \<Longrightarrow> leftderives cfg b c \<Longrightarrow> leftderives cfg a c"
  by (auto simp add: leftderives_def leftderivations_def)

lemma leftderives1_eq_leftderivations1: "leftderives1 cfg x y = ((x, y) \<in> leftderivations1 cfg)"
  by (simp add: leftderivations1_def)

lemma leftderives_induct[consumes 1, case_names Base Step]:
  assumes derives: "leftderives cfg a b"
  assumes Pa: "P a"
  assumes induct: "\<And>y z. leftderives cfg a y \<Longrightarrow> leftderives1 cfg y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
proof -
  note rtrancl_lemma = rtrancl_induct[where a = a and b = b and r = "leftderivations1 cfg" and P=P]
  from derives Pa induct rtrancl_lemma show "P b"
    by (metis leftderives_def leftderivations_def leftderives1_eq_leftderivations1)
qed

lemma derives1_implies_derives[simp]:"derives1 cfg a b \<Longrightarrow> derives cfg a b"
  by (auto simp add: derives_def derivations_def derivations1_def)

lemma derives_trans: "derives cfg a b \<Longrightarrow> derives cfg b c \<Longrightarrow> derives cfg a c"
  by (auto simp add: derives_def derivations_def)

lemma derives1_eq_derivations1: "derives1 cfg x y = ((x, y) \<in> derivations1 cfg)"
  by (simp add: derivations1_def)

lemma derives_induct[consumes 1, case_names Base Step]:
  assumes derives: "derives cfg a b"
  assumes Pa: "P a"
  assumes induct: "\<And>y z. derives cfg a y \<Longrightarrow> derives1 cfg y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
proof -
  note rtrancl_lemma = rtrancl_induct[where a = a and b = b and r = "derivations1 cfg" and P=P]
  from derives Pa induct rtrancl_lemma show "P b"
    by (metis derives_def derivations_def derives1_eq_derivations1)
qed

definition Derives1 :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "Derives1 cfg u i r v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> (N, \<alpha>) \<in> set (\<RR> cfg)
        \<and> r = (N, \<alpha>) \<and> i = length x)"  

lemma Derives1_split:
  "Derives1 cfg u i r v \<Longrightarrow> \<exists> x y. u = x @ [fst r] @ y \<and> v = x @ (snd r) @ y \<and> length x = i"
  by (metis Derives1_def fst_conv snd_conv)

lemma Derives1_implies_derives1: "Derives1 cfg u i r v \<Longrightarrow> derives1 cfg u v"
  by (auto simp add: Derives1_def derives1_def)

lemma derives1_implies_Derives1: "derives1 cfg u v \<Longrightarrow> \<exists> i r. Derives1 cfg u i r v"
  by (auto simp add: Derives1_def derives1_def)

lemma Derives1_unique_dest: "Derives1 cfg u i r v \<Longrightarrow> Derives1 cfg u i r w \<Longrightarrow> v = w"
  by (auto simp add: Derives1_def derives1_def)

lemma Derives1_unique_src: "Derives1 cfg u i r w \<Longrightarrow> Derives1 cfg v i r w \<Longrightarrow> u = v"
  by (auto simp add: Derives1_def derives1_def)

fun Derivation :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a derivation \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "Derivation _ a [] b = (a = b)"
| "Derivation cfg a (d#D) b = (\<exists> x. Derives1 cfg a (fst d) (snd d) x \<and> Derivation cfg x D b)"

lemma Derivation_implies_derives: "Derivation cfg a D b \<Longrightarrow> derives cfg a b"
proof (induct D arbitrary: a b)
  case Nil thus ?case 
    by (simp add: derives_def derivations_def)
next
  case (Cons d D)
    note ihyps = this
    from ihyps have "\<exists> x. Derives1 cfg a (fst d) (snd d) x \<and> Derivation cfg x D b" by auto
    then obtain x where "Derives1 cfg a (fst d) (snd d) x" and xb: "Derivation cfg x D b" by blast
    with Derives1_implies_derives1 have d1: "derives cfg a x" by fastforce
    from ihyps xb have d2:"derives cfg x b" by simp
    show "derives cfg a b" by (rule derives_trans[OF d1 d2])
qed 

lemma Derivation_Derives1: "Derivation cfg a S y \<Longrightarrow> Derives1 cfg y i r z \<Longrightarrow> Derivation cfg a (S@[(i,r)]) z"
proof (induct S arbitrary: a y z i r)
  case Nil thus ?case by simp
next
  case (Cons s S) thus ?case 
    by (metis Derivation.simps(2) append_Cons) 
qed

lemma derives_implies_Derivation: "derives cfg a b \<Longrightarrow> \<exists> D. Derivation cfg a D b"
proof (induct rule: derives_induct)
  case Base
  show ?case by (rule exI[where x="[]"], simp)
next
  case (Step y z)
  note ihyps = this
  from ihyps obtain D where ay: "Derivation cfg a D y" by blast
  from ihyps derives1_implies_Derives1 obtain i r where yz: "Derives1 cfg y i r z" by blast
  from Derivation_Derives1[OF ay yz] show ?case by auto
qed
    
lemma Derives1_take: "Derives1 cfg a i r b \<Longrightarrow> take i a = take i b"
  by (auto simp add: Derives1_def)

lemma Derives1_drop: "Derives1 cfg a i r b \<Longrightarrow> drop (Suc i) a = drop (i + length (snd r)) b"
  by (auto simp add: Derives1_def)

lemma Derives1_bound: "Derives1 cfg a i r b \<Longrightarrow> i < length a"
  by (auto simp add: Derives1_def)

lemma Derives1_length: "Derives1 cfg a i r b \<Longrightarrow> length b = length a + length (snd r) - 1"
  by (auto simp add: Derives1_def)

definition leftmost :: "'a cfg \<Rightarrow> nat \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "leftmost cfg i s = (i < length s \<and> is_word cfg (take i s) \<and> is_nonterminal cfg (s ! i))" 

lemma set_take: "set (take n s) = { s ! i | i. i < n \<and> i < length s}"
proof (cases "n \<le> length s")
  case True thus ?thesis
  by (subst List.nth_image[symmetric], auto)
next
  case False thus ?thesis
    apply (subst set_conv_nth)
    by (metis less_trans linear not_le take_all)
qed
  
lemma list_all_take: "list_all P (take n s) = (\<forall> i. i < n \<and> i < length s \<longrightarrow> P (s ! i))"
  by (auto simp add: set_take list_all_iff)

lemma rule_nonterminal_type[simp]: "wf_cfg cfg \<Longrightarrow> (N, \<alpha>) \<in> set (\<RR> cfg) \<Longrightarrow> is_nonterminal cfg N"
  by (auto simp add: is_nonterminal_def wf_cfg_defs)

lemma [elim]: "Derives1 cfg a i r b \<Longrightarrow> r \<in> set (\<RR> cfg)"
  using Derives1_def by metis

lemma is_terminal_nonterminal: "wf_cfg cfg \<Longrightarrow> is_terminal cfg x \<Longrightarrow> is_nonterminal cfg x \<Longrightarrow> False"
  by (auto simp: wf_cfg_defs disjoint_iff is_nonterminal_def is_terminal_def)

lemma Derives1_leftmost:
  assumes "Derives1 cfg a i r b" "wf_cfg cfg" "wf_sentence cfg a"
  shows "\<exists> j. leftmost cfg j a \<and> j \<le> i"
proof -
  let ?J = "{j . j < length a \<and> is_nonterminal cfg (a ! j)}"
  let ?M = "Min ?J"
  from assms have J1:"i \<in> ?J"
    by (auto simp add: Derives1_def is_nonterminal_def wf_cfg_defs)
  have J2:"finite ?J" by auto
  note J = J1 J2
  from J have M1: "?M \<in> ?J" by (rule_tac Min_in, auto) 
  {
    fix j
    assume "j \<in> ?J"
    with J have "?M \<le> j" by auto
  }
  note M3 = this[OF J1]
  have is_word: "is_word cfg (take ?M a)"
    apply (auto simp add: is_word_def list_all_take)
    using is_terminal_nonterminal[OF assms(2)] less_le_not_le mem_Collect_eq set_take
      \<open>\<And>j. j \<in> {j. j < length a \<and> is_nonterminal cfg (a ! j)} \<Longrightarrow> Min {j. j < length a \<and> is_nonterminal cfg (a ! j)} \<le> j\<close>
    by (smt (verit, ccfv_threshold) assms(3) in_set_takeD wf_sentence_def is_symbol_def)
 show ?thesis 
    apply (rule_tac exI[where x="?M"])
    apply (simp add: leftmost_def)
    by (metis (mono_tags, lifting) M1 M3 is_word mem_Collect_eq)
qed

lemma Derivation_leftmost: "wf_cfg cfg \<Longrightarrow> wf_sentence cfg a \<Longrightarrow> D \<noteq> [] \<Longrightarrow> Derivation cfg a D b \<Longrightarrow> \<exists> i. leftmost cfg i a"
  apply (case_tac "D")
  apply (auto)
  apply (metis Derives1_leftmost)
  done

lemma nonword_has_nonterminal:
  "wf_cfg cfg \<Longrightarrow> wf_sentence cfg a \<Longrightarrow> \<not> (is_word cfg a) \<Longrightarrow> \<exists> k. k < length a \<and> is_nonterminal cfg (a ! k)"
  apply (auto simp add: list_all_iff is_word_def)
  by (metis in_set_conv_nth wf_sentence_def is_symbol_def)

lemma leftmost_cons_nonterminal: 
  "is_nonterminal cfg x \<Longrightarrow> leftmost cfg 0 (x#xs)"
  by (simp add: leftmost_def)

lemma leftmost_cons_terminal: 
  "wf_cfg cfg \<Longrightarrow> is_terminal cfg x \<Longrightarrow> leftmost cfg i (x#xs) = (i > 0 \<and> leftmost cfg (i - 1) xs)"
  using is_terminal_nonterminal is_word_def leftmost_def
  by (smt (verit, ccfv_threshold) Suc_diff_1 Suc_less_eq length_Cons list.set_intros(2) not_gr0 nth_Cons' set_ConsD take_Suc_Cons)

lemma is_nonterminal_cons_terminal: 
  "wf_cfg cfg \<Longrightarrow> is_terminal cfg x \<Longrightarrow> k < length (x # a) \<Longrightarrow> is_nonterminal cfg ((x # a) ! k) \<Longrightarrow>
   k > 0 \<and> k - 1 < length a \<and> is_nonterminal cfg (a ! (k - 1))"
by (metis One_nat_def Suc_leI is_terminal_nonterminal less_diff_conv2 
    list.size(4) nth_non_equal_first_eq)

lemma leftmost_exists:
  assumes "wf_cfg cfg" "wf_sentence cfg a"
  shows "k < length a \<Longrightarrow> is_nonterminal cfg (a ! k) \<Longrightarrow> 
   \<exists> i. leftmost cfg i a \<and> i \<le> k"
  using assms
proof (induct a arbitrary: k)
  case Nil thus ?case by auto
next
  case (Cons x a) 
  show ?case
  proof(cases "is_nonterminal cfg x")
    case True thus ?thesis
      apply(rule_tac exI[where x="0"])
      apply (simp add: leftmost_cons_nonterminal)
      done
  next
    case False
    then have x: "is_terminal cfg x"
      by (meson Cons.prems(4) list.set_intros(1) wf_sentence_def is_symbol_def)
    note k = is_nonterminal_cons_terminal[OF assms(1) x Cons(2) Cons(3)]
    with Cons have "\<exists>i. leftmost cfg i a \<and> i \<le> k - 1"
      by (meson list.set_intros(2) wf_sentence_def)
    then show ?thesis
      apply (auto simp add: leftmost_cons_terminal[OF assms(1) x])
      by (metis le_diff_conv2 Suc_leI add_Suc_right add_diff_cancel_right' k 
          le_0_eq le_imp_less_Suc nat_le_linear)
  qed
qed

lemma nonword_leftmost_exists: 
  "wf_cfg cfg \<Longrightarrow> wf_sentence cfg a \<Longrightarrow> \<not> (is_word cfg a) \<Longrightarrow> \<exists> i. leftmost cfg i a"
  by (metis leftmost_exists nonword_has_nonterminal)
  
lemma leftmost_unaffected_Derives1: "leftmost cfg j a \<Longrightarrow> j < i \<Longrightarrow> Derives1 cfg a i r b \<Longrightarrow> leftmost cfg j b"
apply (simp add: leftmost_def)
proof -
  assume a1: "j < length a \<and> is_word cfg (take j a) \<and> is_nonterminal cfg (a ! j)"
  assume a2: "j < i"
  assume "Derives1 cfg a i r b"
  then have f3: "take i a = take i b"
    by (metis Derives1_take)
  have f4: "\<And>n ss ssa. take (length (take n (ss::'a list))) (ssa::'a list) = take (length ss) (take n ssa)"
    by (metis length_take take_take)
  have f5: "\<And>ss. take j (ss::'a list) = take i (take j ss)"
    using a2 by simp
  have f6: "length (take j a) = j"
    using a1 by simp
  then have f7: "\<And>n. min j n = length (take n (take j a))"
    by (metis length_take)
  have f8: "\<And>n ss. n = length (take n (ss::'a list)) \<or> length ss < n"
    by (metis leI length_take min.absorb2)
  have f9: "\<And>ss. take j (ss::'a list) = take j (take i ss)"
    using f7 f6 f5 by simp
  have f10: "\<And>ss n. length (ss::'a list) \<le> n \<or> length (take n ss) = n"
    using f8 by auto
  then have f11: "\<And>ss ssa. length (ss::'a list) = length (take (length ss) (ssa::'a list)) \<or> length (take (length ssa) ss) = length ssa"
    by (metis length_take min.absorb2)
  have f12: "\<And>ss ssa n. take (length (ss::'a list)) (ssa::'a list) = take n (take (length ss) ssa) \<or> length (take n ss) = n"
    using f10 by (metis min.absorb2 take_take)
  { assume "\<not> j < j"
    { assume "\<not> j < j \<and> i \<noteq> j"
      moreover
      { assume "length a \<noteq> j \<and> length (take i a) \<noteq> i"
        then have "\<exists>ss. length (take (length (take i (take (length a) (ss::'a list)))) (take j ss)) \<noteq> length (take i (take (length a) ss))"
          using f12 f11 f6 f5 f4 by (metis Ex_list_of_length length_take)
        then have "\<exists>ss ssa. take (length (ss::'a list)) (take j (ssa::'a list)) \<noteq> take (length ss) (take i (take (length a) ssa))"
          using f11 by metis
        then have "length b \<noteq> j"
          using f9 f4 f3 by metis }
      ultimately have "length b \<noteq> j"
        using f7 f6 f5 f3 a1 by (metis length_take) }
    then have "length b = j \<longrightarrow> j < j"
      using a2 by metis }
  then have "j < length b"
    using f9 f8 f7 f6 f4 f3 by (metis length_take)
  then show "j < length b \<and> is_word cfg (take j b) \<and> is_nonterminal cfg (b ! j)"
    using f9 f3 a2 a1 by (metis nth_take)
qed

definition derivation_ge :: "'a derivation \<Rightarrow> nat \<Rightarrow> bool" where
  "derivation_ge D i = (\<forall> d \<in> set D. fst d \<ge> i)"

lemma derivation_ge_cons: "derivation_ge (d#D) i = (fst d \<ge> i \<and> derivation_ge D i)"
  by (auto simp add: derivation_ge_def)

lemma derivation_ge_append: 
  "derivation_ge (D@E) i = (derivation_ge D i \<and> derivation_ge E i)"
  by (auto simp add: derivation_ge_def)

lemma leftmost_unaffected_Derivation: 
  "derivation_ge D (Suc i) \<Longrightarrow> leftmost cfg i a \<Longrightarrow> Derivation cfg a D b \<Longrightarrow> leftmost cfg i b"
proof (induct D arbitrary: a)
  case Nil thus ?case by auto
next
  case (Cons d D) 
  then have "\<exists> x. Derives1 cfg a (fst d) (snd d) x \<and> Derivation cfg x D b" by simp
  then obtain x where x1: "Derives1 cfg a (fst d) (snd d) x" and x2: "Derivation cfg x D b" by blast  
  with Cons have leftmost_x: "leftmost cfg i x"
    apply (rule_tac leftmost_unaffected_Derives1[
           where a=a and j=i and b="x" and i="fst d" and r="snd d"])
    by (auto simp add: derivation_ge_def)
  with Cons x2 show ?case by (auto simp add: derivation_ge_def)
qed

lemma le_Derives1_take: 
  assumes le: "i \<le> j" 
  and D: "Derives1 cfg a j r b"
  shows "take i a = take i b"
proof -
  note Derives1_take[where a=a and i=j and r=r and b=b]
  with le D show ?thesis by (rule_tac le_take_same[where i=i and j=j], auto)
qed  

lemma Derivation_take: "derivation_ge D i \<Longrightarrow> Derivation cfg a D b \<Longrightarrow> take i a = take i b"
proof(induct D arbitrary: a b)
  case Nil thus ?case by auto
next
  case (Cons d D)
  then have "\<exists> x. Derives1 cfg a (fst d) (snd d) x \<and> Derivation cfg x D b"
    by simp
  then obtain x where ax: "Derives1 cfg a (fst d) (snd d) x" and xb: "Derivation cfg x D b" by blast  
  from derivation_ge_cons Cons(2) have d: "i \<le> fst d" and D: "derivation_ge D i" by blast+
  note take_i_xb = Cons(1)[OF D xb]
  note take_i_ax = le_Derives1_take[OF d ax]
  from take_i_xb take_i_ax show ?case by auto
qed

lemma leftmost_cons_less: "i < length u \<Longrightarrow> leftmost cfg i (u@v) = leftmost cfg i u"
  by (auto simp add: leftmost_def nth_append)

lemma leftmost_is_nonterminal: "leftmost cfg i u \<Longrightarrow> is_nonterminal cfg (u ! i)"
  by (metis leftmost_def)

lemma is_word_is_terminal: "i < length u \<Longrightarrow> is_word cfg u \<Longrightarrow> is_terminal cfg (u ! i)"
  using is_word_def by force
  
lemma leftmost_append: 
  assumes wf_cfg: "wf_cfg cfg"
  assumes leftmost: "leftmost cfg i (u@v)"
  and is_word: "is_word cfg u"
  shows "length u \<le> i"
proof (cases "i < length u")
  case False thus ?thesis by auto
next
  case True 
  with leftmost have "leftmost cfg i u" using leftmost_cons_less[OF True] by simp
  then have is_nonterminal: "is_nonterminal cfg (u ! i)" by (rule leftmost_is_nonterminal)
  note is_terminal = is_word_is_terminal[OF True is_word]
  note is_terminal_nonterminal[OF wf_cfg is_terminal is_nonterminal]
  then show ?thesis by auto
qed

lemma derivation_ge_empty[simp]: "derivation_ge [] i" 
by (simp add: derivation_ge_def)

lemma leftmost_notword: "wf_cfg cfg \<Longrightarrow> leftmost cfg i a \<Longrightarrow> j > i \<Longrightarrow> \<not> (is_word cfg (take j a))"
  by (metis append_take_drop_id leD leI leftmost_append leftmost_def length_take min.absorb4 take_all_iff)

lemma leftmost_unique: "wf_cfg cfg \<Longrightarrow> leftmost cfg i a \<Longrightarrow> leftmost cfg j a \<Longrightarrow> i = j" 
  by (metis leftmost_def leftmost_notword linorder_neqE_nat)

lemma leftmost_Derives1: "wf_cfg cfg \<Longrightarrow> wf_sentence cfg a \<Longrightarrow> leftmost cfg i a \<Longrightarrow> Derives1 cfg a j r b \<Longrightarrow> i \<le> j"
  using Derives1_leftmost leftmost_unique wf_cfg_def by blast

lemma leftmost_Derives1_propagate:
  assumes wf_cfg: "wf_cfg cfg" "wf_sentence cfg a" "wf_sentence cfg b"
  assumes leftmost: "leftmost cfg i a"
      and Derives1: "Derives1 cfg a j r b"
    shows "(is_word cfg b \<and> i = j) \<or> (\<exists> k. leftmost cfg k b \<and> i \<le> k)"
proof -
  from leftmost_Derives1[OF wf_cfg(1,2) leftmost Derives1] have ij: "i \<le> j" by auto
  show ?thesis
  proof (cases "is_word cfg b")
    case True show ?thesis
      by (metis Derives1 True ij le_neq_implies_less leftmost 
          leftmost_unaffected_Derives1 order_refl)
  next
    case False show ?thesis
      using assms Derives1 Derives1_take ij le_neq_implies_less leftmost leftmost_def leftmost_notword
          leftmost_unaffected_Derives1 nonword_leftmost_exists not_le_imp_less wf_cfg by metis
  qed
qed

lemma is_word_Derives1[elim]: "wf_cfg cfg \<Longrightarrow> is_word cfg a \<Longrightarrow> Derives1 cfg a i r b \<Longrightarrow> False"
  by (metis Derives1_leftmost append.right_neutral is_word_def leftmost_append leftmost_def linorder_not_less wf_sentence_def is_symbol_def)
  
lemma is_word_Derivation[elim]: "wf_cfg cfg \<Longrightarrow> is_word cfg a \<Longrightarrow> Derivation cfg a D b \<Longrightarrow> D = []"
  by (meson Derivation.elims(2) is_word_Derives1)

lemma Derives1_wf_sentence_propagate:
  assumes "wf_cfg cfg" "wf_sentence cfg a" "Derives1 cfg a i r b"
  shows "wf_sentence cfg b"
proof -
  obtain x y N \<alpha> where *:
    "a = x @ [N] @ y" "b = x @ \<alpha> @ y" "(N,\<alpha>) \<in> set (\<RR> cfg)" "r = (N,\<alpha>)" "i = length x"
    using assms(3) Derives1_def by (smt (verit, best))
  have "wf_sentence cfg x" "wf_sentence cfg y"
    using assms(2) *(1) unfolding wf_sentence_def by auto
  moreover have "wf_sentence cfg \<alpha>"
    using assms(1) *(3) unfolding wf_cfg_def valid_rules_def wf_sentence_def is_terminal_def is_nonterminal_def is_symbol_def by blast
  ultimately show ?thesis
    using *(2) unfolding wf_sentence_def by auto
qed

lemma Derivation_wf_sentence_propagate:
  assumes "wf_cfg cfg" "wf_sentence cfg a" "Derivation cfg a D b"
  shows "wf_sentence cfg b"
  using assms
proof (induction D arbitrary: a b)
  case (Cons d D)
  thus ?case
    apply (auto)
    using Derives1_wf_sentence_propagate by blast
qed simp

lemma leftmost_Derivation:
  "wf_cfg cfg \<Longrightarrow> wf_sentence cfg a \<Longrightarrow> wf_sentence cfg b \<Longrightarrow> leftmost cfg i a \<Longrightarrow> Derivation cfg a D b \<Longrightarrow> j \<le> i \<Longrightarrow> derivation_ge D j"
proof (induct D arbitrary: a b i j)
  case Nil thus ?case by auto
next
  case (Cons d D)
  then have "\<exists> x. Derives1 cfg a (fst d) (snd d) x \<and> Derivation cfg x D b" by auto
  then obtain x where ax:"Derives1 cfg a (fst d) (snd d) x" and xb:"Derivation cfg x D b" by blast
  note ji = Cons(7)
  have "wf_sentence cfg x"
    using Derives1_wf_sentence_propagate Cons.prems(1,2) ax by blast
  note i_fstd = leftmost_Derives1[OF Cons(2,3) Cons(5) ax]
  note disj = leftmost_Derives1_propagate[OF Cons(2,3) \<open>wf_sentence cfg x\<close> Cons(5) ax]
  thus ?case
  proof(induct rule: disjCases2)
    case 1 
    with xb have "D = []"
      using Cons.prems(1) by auto
    with 1 ji show ?case by (simp add: derivation_ge_def)
  next
    case 2 
    then obtain k where k: "leftmost cfg k x" and ik: "i \<le> k" by blast
    note ge = Cons(1)[OF Cons(2) \<open>wf_sentence cfg x\<close> Cons(4) k xb, where j=j]
    from ji ik i_fstd ge show ?case
      by (simp add: derivation_ge_cons)
  qed
qed

lemma derivation_ge_list_all: "derivation_ge D i = list_all (\<lambda> d. fst d \<ge> i) D"
by (simp add: Ball_set derivation_ge_def)

lemma split_derivation_leftmost:
  assumes "derivation_ge D i"
  and "\<not> (derivation_ge D (Suc i))"
  shows "\<exists> E F r. D = E@[(i, r)]@F \<and> derivation_ge E (Suc i)"
proof -
  from assms have "\<exists> k. k < length D \<and> fst(D ! k) \<ge> i \<and> \<not>(fst(D ! k) \<ge> Suc i)"
    by (metis derivation_ge_def in_set_conv_nth)
  then have "\<exists> k. k < length D \<and> fst(D ! k) = i" by auto
  then show ?thesis
  proof(induct rule: ex_minimal_witness)
    case (Minimal k)
      then have k_len: "k < length D" and k_i: "fst (D ! k) = i" by auto
      let ?E = "take k D"
      let ?r = "snd (D ! k)"
      let ?F = "drop (Suc k) D"
      note split = split_list_at[OF k_len]
      from k_i have D_k: "D ! k = (i, ?r)" by auto
      show ?case
        apply (rule exI[where x="?E"])
        apply (rule exI[where x="?F"])
        apply (rule exI[where x="?r"])
        apply (subst D_k[symmetric])
        apply (rule conjI)
        apply (rule split)
        by (metis (mono_tags, lifting) Minimal.hyps(2) Suc_leI assms(1) 
            derivation_ge_list_all le_neq_implies_less list_all_length list_all_take)
  qed
qed

lemma Derives1_Derives1_swap:
  assumes "i < j"
  and "Derives1 cfg a j p b"
  and "Derives1 cfg b i q c"
  shows "\<exists> b'. Derives1 cfg a i q b' \<and> Derives1 cfg b' (j - 1 + length (snd q)) p c"
proof -
  from Derives1_split[OF assms(2)] obtain a1 a2 where
    a_src: "a = a1 @ [fst p] @ a2" and a_dest: "b = a1 @ snd p @ a2" 
    and a1_len: "length a1 = j" by blast
  note a = this
  from Derives1_split[OF assms(3)] obtain b1 b2 where
    b_src: "b = b1 @ [fst q] @ b2" and b_dest: "c = b1 @ snd q @ b2" 
    and b1_len: "length b1 = i" by blast
  have a_take_j: "a1 = take j a" by (metis a1_len a_src append_eq_conv_conj) 
  have b_take_i: "b1 @ [fst q] = take (Suc i) b"
    by (metis append_assoc append_eq_conv_conj b1_len b_src length_append_singleton) 
  from a_take_j b_take_i  take_eq_take_append[where j=j and i="Suc i" and a=a]
  have "\<exists> u. a1 = (b1 @ [fst q]) @ u"
    by (metis le_iff_add Suc_leI a1_len a_dest append_eq_conv_conj assms(1) take_add) 
  then obtain u where u1: "a1 = (b1 @ [fst q]) @ u" by blast
  then have j_i_u: "j = i + 1 + length u"
    using Suc_eq_plus1 a1_len b1_len length_append length_append_singleton by auto
  have u2: "b2 = u @ snd p @ a2" by (metis a_dest append_assoc b_src same_append_eq u1) 
  let ?b = "b1 @ (snd q) @ u @ [fst p] @ a2"
  from assms have q_dom: "q \<in> set (\<RR> cfg)" by auto
  have a_b': "Derives1 cfg a i q ?b"
    apply (subst Derives1_def)
    apply (rule exI[where x="b1"])
    apply (rule exI[where x="u@[fst p]@a2"])
    apply (rule exI[where x="fst q"])
    apply (rule exI[where x="snd q"])
    apply (auto simp add: b1_len a_src u1 q_dom)
    done
  from assms have p_dom: "p \<in> set (\<RR> cfg)" by auto
  have b'_c: "Derives1 cfg ?b (j - 1 + length (snd q)) p c"
    apply (subst Derives1_def)
    apply (rule exI[where x="b1 @ (snd q) @ u"])
    apply (rule exI[where x="a2"])
    apply (rule exI[where x="fst p"])
    apply (rule exI[where x="snd p"])
    apply (auto simp add: p_dom b_dest u2 b1_len j_i_u)
    done
  show ?thesis
    apply (rule exI[where x="?b"])
    apply (rule conjI)
    apply (rule a_b')
    apply (rule b'_c)
    done
qed

definition derivation_shift :: "'a derivation \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a derivation" where
  "derivation_shift D left right = map (\<lambda> d. (fst d - left + right, snd d)) D"

lemma derivation_shift_empty[simp]: "derivation_shift [] left right = []" 
  by (auto simp add: derivation_shift_def)

lemma derivation_shift_cons[simp]:
  "derivation_shift (d#D) left right = ((fst d - left + right, snd d)#(derivation_shift D left right))"
by (simp add: derivation_shift_def)

lemma Derivation_append: "Derivation cfg a (D@E) c = (\<exists> b. Derivation cfg a D b \<and> Derivation cfg b E c)"
proof(induct D arbitrary: a c E)
  case Nil thus ?case by auto
next
  case (Cons d D) thus ?case by auto
qed

lemma Derivation_implies_append: 
  "Derivation cfg a D b \<Longrightarrow> Derivation cfg b E c \<Longrightarrow> Derivation cfg a (D@E) c"
using Derivation_append by blast

lemma Derivation_swap_single_end_to_front: 
  "i < j \<Longrightarrow> derivation_ge D j \<Longrightarrow> Derivation cfg a (D@[(i,r)]) b \<Longrightarrow>
   Derivation cfg a ((i,r)#(derivation_shift D 1 (length (snd r)))) b"
proof(induct D arbitrary: a)
  case Nil thus ?case by auto
next
  case (Cons d D) 
  from Cons have "\<exists> c. Derives1 cfg a (fst d) (snd d) c \<and> Derivation cfg c (D @ [(i, r)]) b"
    by simp
  then obtain c where ac: "Derives1 cfg a (fst d) (snd d) c"
    and cb: "Derivation cfg c (D @ [(i, r)]) b" by blast
  from Cons(3) have D_j: "derivation_ge D j" by (simp add: derivation_ge_cons)
  from Cons(1)[OF Cons(2) D_j cb, simplified]
  obtain x where cx: "Derives1 cfg c i r x" and  
    xb: "Derivation cfg x (derivation_shift D 1 (length (snd r))) b" by auto
  have i_fst_d: "i < fst d" using Cons derivation_ge_cons dual_order.strict_trans1 by blast
  from Derives1_Derives1_swap[OF i_fst_d ac cx]
  obtain b' where ab': "Derives1 cfg a i r b'" and 
    b'x: "Derives1 cfg b' (fst d - 1 + length (snd r)) (snd d) x" by blast
  show ?case using ab' b'x xb by auto
qed    

lemma Derivation_swap_single_mid_to_front: 
  assumes "i < j"
  and "derivation_ge D j" 
  and "Derivation cfg a (D@[(i,r)]@E) b"
  shows "Derivation cfg a ((i,r)#((derivation_shift D 1 (length (snd r)))@E)) b"
proof -
  from assms have "\<exists> x. Derivation cfg a (D@[(i, r)]) x \<and> Derivation cfg x E b"
    using Derivation_append by fastforce
  then obtain x where ax: "Derivation cfg a (D@[(i, r)]) x" and xb: "Derivation cfg x E b"
    by blast
  with assms have "Derivation cfg a ((i, r)#(derivation_shift D 1 (length (snd r)))) x"
    using Derivation_swap_single_end_to_front by blast
  then show ?thesis using Derivation_append xb by fastforce
qed

lemma length_derivation_shift[simp]: 
  "length(derivation_shift D left right) = length D"
  by (simp add: derivation_shift_def)

definition LeftDerives1 :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentence \<Rightarrow> bool" where 
  "LeftDerives1 cfg u i r v = (leftmost cfg i u \<and> Derives1 cfg u i r v)"

lemma LeftDerives1_implies_leftderives1: "LeftDerives1 cfg u i r v \<Longrightarrow> leftderives1 cfg u v"
  by (metis Derives1_def LeftDerives1_def append_eq_conv_conj leftderives1_def leftmost_def)
    
lemma leftmost_Derives1_leftderives: 
  "leftmost cfg i a \<Longrightarrow> Derives1 cfg a i r b \<Longrightarrow> leftderives cfg b c \<Longrightarrow> leftderives cfg a c"
using LeftDerives1_def LeftDerives1_implies_leftderives1 
  leftderives1_implies_leftderives leftderives_trans by blast

theorem Derivation_implies_leftderives_gen:
  assumes "wf_cfg cfg" "wf_sentence cfg a"
  shows "Derivation cfg a D (u@v) \<Longrightarrow> is_word cfg u \<Longrightarrow> (\<exists> w. 
          leftderives cfg a (u@w) \<and> 
          (v = [] \<longrightarrow> w = []) \<and> 
          (\<forall> X. is_first X v \<longrightarrow> is_first X w))"
  using assms
proof (induct "length D" arbitrary: D a u v)
  case 0
    then have "a = u@v" by auto
    thus ?case by (rule_tac x = v in exI, auto)
next
  case (Suc n)
    from Suc have "D \<noteq> []" by auto
    with Suc Derivation_leftmost have "\<exists> i. leftmost cfg i a"
      by metis
    then obtain i where i: "leftmost cfg i a" by blast
    show "?case"
    proof (cases "derivation_ge D (Suc i)")
      case True
        with Suc have leftmost: "leftmost cfg i (u@v)" 
          by (rule_tac leftmost_unaffected_Derivation[OF True i], auto)
        have length_u: "length u \<le> i" 
          using leftmost_append[OF assms(1) leftmost Suc(4)] .
        have take_Suc: "take (Suc i) a = take (Suc i) (u@v)" 
          using  Derivation_take[OF True Suc(3)] .
        with length_u have is_prefix_u: "is_prefix u a"
          by (metis append_assoc append_take_drop_id dual_order.strict_implies_order 
              is_prefix_def le_imp_less_Suc take_all take_append)  
        have a: "u @ drop (length u) a = a" 
          using is_prefix_unsplit[OF is_prefix_u] .
        from take_Suc have length_take_Suc: "length (take (Suc i) a) = Suc i"
          by (metis Suc_leI i leftmost_def length_take min.absorb2)
        have v: "v \<noteq> []"
        proof(cases "v = []")
          case False thus ?thesis by auto
        next
          case True
          with length_u have right: "length(take (Suc i) (u@v)) = length u" by simp
          note left = length_take_Suc
          from left right take_Suc have "Suc i = length u" by auto
          with length_u show ?thesis by auto
        qed
        then have "\<exists> X w. v = X#w" by (cases v, auto)
        then obtain X w where v: "v = X#w" by blast
        have is_first_X: "is_first X (drop (length u) a)"
          apply (rule_tac is_first_drop_length[where v=v and w=w and k="Suc i"])
          apply (simp_all add: take_Suc v)
          apply (metis Suc_leI i leftmost_def)
          apply (insert length_u)
          apply arith
          done
        show ?thesis
          apply (rule exI[where x="drop (length u) a"])
          by (simp add: a v is_first_cons is_first_X)
    next
      case False
      have "wf_sentence cfg (u @ v)"
        using Derivation_wf_sentence_propagate Suc.prems(1,4) assms(1) by auto
      have Di: "derivation_ge D i" 
      using leftmost_Derivation[OF Suc(5,6) \<open>wf_sentence cfg (u @ v)\<close> i Suc(3), where j=i, simplified] .
      from split_derivation_leftmost[OF Di False]
      obtain E F r where D_split: "D = E @ [(i, r)] @ F" 
        and E_Suc: "derivation_ge E (Suc i)" by auto
      let ?D = "(derivation_shift E 1 (length (snd r)))@F"
      from D_split 
      have "Derivation cfg a ((i,r) # ?D) (u @ v)"
        using Derivation_swap_single_mid_to_front E_Suc Suc.prems(1) lessI by blast
      then have "\<exists> y. Derives1 cfg a i r y \<and> Derivation cfg y ?D (u @ v)" by simp
      then obtain y where ay:"Derives1 cfg a i r y" 
        and yuv: "Derivation cfg y ?D (u @ v)" by blast
      have length_D': "length ?D = n" using D_split Suc.hyps(2) by auto
      from Suc(1)[OF length_D'[symmetric] yuv Suc(4)] 
      obtain w where "leftderives cfg y (u @ w)" and "(v = [] \<longrightarrow> w = [])" 
        and "\<forall>X. is_first X v \<longrightarrow> is_first X w"
        using Derives1_wf_sentence_propagate Suc.prems(4) assms(1) ay by blast
      then show ?thesis using ay i leftmost_Derives1_leftderives by blast
    qed    
qed   

lemma derives_implies_leftderives_gen: 
  assumes "wf_cfg cfg" "wf_sentence cfg a"
  shows "derives cfg a (u@v) \<Longrightarrow> is_word cfg u \<Longrightarrow> (\<exists> w. 
          leftderives cfg a (u@w) \<and> 
          (v = [] \<longrightarrow> w = []) \<and> 
          (\<forall> X. is_first X v \<longrightarrow> is_first X w))"
using Derivation_implies_leftderives_gen derives_implies_Derivation assms by blast

lemma derives_implies_leftderives: "wf_cfg cfg \<Longrightarrow> wf_sentence cfg a \<Longrightarrow> derives cfg a b \<Longrightarrow> is_word cfg b \<Longrightarrow> leftderives cfg a b"
using derives_implies_leftderives_gen by force

fun LeftDerivation :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a derivation \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "LeftDerivation _ a [] b = (a = b)"
| "LeftDerivation cfg a (d#D) b = (\<exists> x. LeftDerives1 cfg a (fst d) (snd d) x \<and> LeftDerivation cfg x D b)"
  
lemma LeftDerives1_implies_Derives1: "LeftDerives1 cfg a i r b \<Longrightarrow> Derives1 cfg a i r b"
by (metis LeftDerives1_def)

lemma LeftDerivation_implies_Derivation:
  "LeftDerivation cfg a D b \<Longrightarrow> Derivation cfg a D b"
proof (induct D arbitrary: a)
  case (Nil) thus ?case by simp
next
  case (Cons d D)
  thus ?case
  using LeftDerivation.simps(2) Derivation.simps(2) 
    LeftDerives1_implies_Derives1 by blast
qed

lemma LeftDerivation_implies_leftderives: "LeftDerivation cfg a D b \<Longrightarrow> leftderives cfg a b"
proof (induct D arbitrary: a b)
  case Nil thus ?case by simp
next
  case (Cons d D)
    note ihyps = this
    from ihyps have "\<exists> x. LeftDerives1 cfg a (fst d) (snd d) x \<and> LeftDerivation cfg x D b" by auto
    then obtain x where "LeftDerives1 cfg a (fst d) (snd d) x" and xb: "LeftDerivation cfg x D b" by blast
    with LeftDerives1_implies_leftderives1 have d1: "leftderives cfg a x" by fastforce
    from ihyps xb have d2:"leftderives cfg x b" by simp
    show "leftderives cfg a b" by (rule leftderives_trans[OF d1 d2])
qed 

lemma leftmost_witness[simp]: "leftmost cfg (length x) (x@(N#y)) = (is_word cfg x \<and> is_nonterminal cfg N)"
  by (auto simp add: leftmost_def)

lemma leftderives1_implies_LeftDerives1:
  assumes wf_cfg: "wf_cfg cfg"
  assumes leftderives1: "leftderives1 cfg u v"
  shows "\<exists> i r. LeftDerives1 cfg u i r v"
proof -
  from leftderives1 have 
    "\<exists>x y N \<alpha>. u = x @ [N] @ y \<and> v = x @ \<alpha> @ y \<and> is_word cfg x \<and> (N, \<alpha>) \<in> set (\<RR> cfg)"
    by (simp add: leftderives1_def)
  then obtain x y N \<alpha> where 
    u:"u = x @ [N] @ y" and
    v:"v = x @ \<alpha> @ y" and
    x:"is_word cfg x" and  
    r:"(N, \<alpha>) \<in> set (\<RR> cfg)"
    by blast
  show ?thesis
    apply (rule_tac x="length x" in exI)
    apply (rule_tac x="(N, \<alpha>)" in exI)
    apply (auto simp add: LeftDerives1_def)
    apply (simp add: leftmost_def x u rule_nonterminal_type[OF wf_cfg r])
    apply (simp add: Derives1_def u v)
    apply (rule_tac x=x in exI)
    apply (rule_tac x=y in exI)
    apply (auto simp add: x r)
    done
qed    

lemma LeftDerivation_LeftDerives1: 
  "LeftDerivation cfg a S y \<Longrightarrow> LeftDerives1 cfg y i r z \<Longrightarrow> LeftDerivation cfg a (S@[(i,r)]) z"
proof (induct S arbitrary: a y z i r)
  case Nil thus ?case by simp
next
  case (Cons s S) thus ?case 
    by (metis LeftDerivation.simps(2) append_Cons) 
qed

lemma leftderives_implies_LeftDerivation:
  assumes "wf_cfg cfg"
  shows "leftderives cfg a b \<Longrightarrow> \<exists> D. LeftDerivation cfg a D b"
proof (induct rule: leftderives_induct)
  case Base
  show ?case by (rule exI[where x="[]"], simp)
next
  case (Step y z)
  note ihyps = this
  from ihyps obtain D where ay: "LeftDerivation cfg a D y" by blast
  from ihyps leftderives1_implies_LeftDerives1 obtain i r where yz: "LeftDerives1 cfg y i r z" using assms by blast
  from LeftDerivation_LeftDerives1[OF ay yz] show ?case by auto
qed

lemma LeftDerivation_append: 
  "LeftDerivation cfg a (D@E) c = (\<exists> b. LeftDerivation cfg a D b \<and> LeftDerivation cfg b E c)"
proof(induct D arbitrary: a c E)
  case Nil thus ?case by auto
next
  case (Cons d D) thus ?case by auto
qed

lemma LeftDerivation_implies_append: 
  "LeftDerivation cfg a D b \<Longrightarrow> LeftDerivation cfg b E c \<Longrightarrow> LeftDerivation cfg a (D@E) c"
using LeftDerivation_append by blast

lemma Derivation_unique_dest: "Derivation cfg a D b \<Longrightarrow> Derivation cfg a D c \<Longrightarrow> b = c"
  apply (induct D arbitrary: a b c)
  apply auto
  using Derives1_unique_dest by blast

lemma Derivation_unique_src: "Derivation cfg a D c \<Longrightarrow> Derivation cfg b D c \<Longrightarrow> a = b"
  apply (induct D arbitrary: a b c)
  apply auto
  using Derives1_unique_src by blast

lemma LeftDerives1_unique: "wf_cfg cfg \<Longrightarrow> LeftDerives1 cfg a i r b \<Longrightarrow> LeftDerives1 cfg a j s b \<Longrightarrow> i = j \<and> r = s"
using Derives1_def LeftDerives1_def leftmost_unique by (smt (verit, ccfv_SIG) append_eq_append_conv list.size(4) nth_Cons_0)
 
lemma leftlang: "wf_cfg cfg \<Longrightarrow> \<L> cfg = { v | v. is_word cfg v \<and> is_leftderivation cfg v }"
  using is_derivation_def is_leftderivation_def leftderivation_implies_derivation derives_implies_leftderives \<L>_def
  apply auto
  apply blast
  apply (metis (no_types, lifting) bot_nat_0.extremum_unique in_set_conv_nth is_nonterminal_startsymbol length_Cons less_Suc_eq_le list.size(3) mem_Collect_eq nth_Cons' wf_sentence_def is_symbol_def)
  by blast

lemma leftprefixlang: "wf_cfg cfg \<Longrightarrow> \<L>\<^sub>P cfg = { u | u v. is_word cfg u \<and> is_leftderivation cfg (u@v) }"
  apply (auto simp add: \<L>\<^sub>P_def)
  using derives_implies_leftderives_gen is_derivation_def is_leftderivation_def
  apply (metis is_nonterminal_startsymbol is_word_def leftmost_cons_nonterminal leftmost_def set_ConsD take_Cons' wf_sentence_def is_symbol_def)
  using leftderivation_implies_derivation by blast

lemma is_word_implies_wf_sentence:
  "is_word cfg a \<Longrightarrow> wf_sentence cfg a"
  unfolding is_word_def wf_sentence_def is_symbol_def by blast

lemma derives_implies_leftderives_cons:
  "wf_cfg cfg \<Longrightarrow> wf_sentence cfg u \<Longrightarrow> is_word cfg a \<Longrightarrow> derives cfg u (a@X#b) \<Longrightarrow> \<exists> c. leftderives cfg u  (a@X#c)"
  using derives_implies_leftderives_gen by (metis append_Cons append_Nil is_first_def)

lemma is_word_append[simp]: "is_word cfg (a@b) = (is_word cfg a \<and> is_word cfg b)"
  by (auto simp add: is_word_def)

lemma \<L>\<^sub>P_split: "a@b \<in> \<L>\<^sub>P cfg \<Longrightarrow> a \<in> \<L>\<^sub>P cfg"
  by (auto simp add: \<L>\<^sub>P_def)

lemma \<L>\<^sub>P_is_word: "wf_cfg cfg \<Longrightarrow> a \<in> \<L>\<^sub>P cfg \<Longrightarrow> is_word cfg a"
  by (metis (no_types, lifting) leftprefixlang mem_Collect_eq)

definition Derive :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a derivation \<Rightarrow> 'a sentence" where 
  "Derive cfg a D = (THE b. Derivation cfg a D b)"

lemma Derivation_dest_ex_unique: "Derivation cfg a D b \<Longrightarrow> \<exists>! x. Derivation cfg a D x"
  using Derivation_unique_dest by metis

lemma Derive:
  assumes ab: "Derivation cfg a D b"
  shows "Derive cfg a D = b"
proof -
  note the1_equality[OF Derivation_dest_ex_unique[OF ab] ab]
  thus ?thesis by (simp add: Derive_def)
qed

end
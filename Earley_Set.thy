theory Earley_Set
  imports
    LocalLexing.InductRules
    LocalLexing.ListTools
begin

section \<open>Slightly adjusted content from AFP/LocalLexing\<close>

subsection \<open>CFG.thy\<close>

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

subsection \<open>Derivations.thy\<close>

context CFG begin

lemma [simp]: "is_word []" by (auto simp add: is_word_def)

definition leftderives1 :: "'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "leftderives1 u v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> is_word x
        \<and> (N, \<alpha>) \<in> set \<RR>)"  

lemma leftderives1_implies_derives1[simp]: "leftderives1 u v \<Longrightarrow> derives1 u v"
  by (auto simp add: leftderives1_def derives1_def)

definition leftderivations1 :: "('a sentence \<times> 'a sentence) set" where
  "leftderivations1 = { (u,v) | u v. leftderives1 u v }"

lemma [simp]: "leftderivations1 \<subseteq> derivations1"
  by (auto simp add: leftderivations1_def derivations1_def)

definition leftderivations :: "('a sentence \<times> 'a sentence) set" where 
  "leftderivations = leftderivations1^*"

lemma rtrancl_subset_implies: "a \<subseteq> b \<Longrightarrow> a \<subseteq> b^*" by blast

lemma leftderivations_subset_derivations[simp]: "leftderivations \<subseteq> derivations"
  apply (simp add: leftderivations_def derivations_def)
  apply (rule rtrancl_subset_rtrancl)
  apply (rule rtrancl_subset_implies)
  by simp

definition leftderives :: "'a sentence \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "leftderives u v = ((u, v) \<in> leftderivations)"

lemma leftderives_implies_derives[simp]: "leftderives u v \<Longrightarrow> derives u v"
  apply (auto simp add: leftderives_def derives_def)
  by (rule subsetD[OF leftderivations_subset_derivations])

definition is_leftderivation :: "'a sentence \<Rightarrow> bool"  where
  "is_leftderivation u = leftderives [\<SS>] u"

lemma leftderivation_implies_derivation[simp]: 
  "is_leftderivation u \<Longrightarrow> is_derivation u"
  by (simp add: is_leftderivation_def is_derivation_def)

lemma leftderives_refl[simp]: "leftderives u u"
  by (auto simp add: leftderives_def leftderivations_def)

lemma leftderives1_implies_leftderives[simp]:"leftderives1 a b \<Longrightarrow> leftderives a b"
  by (auto simp add: leftderives_def leftderivations_def leftderivations1_def)

lemma leftderives_trans: "leftderives a b \<Longrightarrow> leftderives b c \<Longrightarrow> leftderives a c"
  by (auto simp add: leftderives_def leftderivations_def)

lemma leftderives1_eq_leftderivations1: "leftderives1 x y = ((x, y) \<in> leftderivations1)"
  by (simp add: leftderivations1_def)

lemma leftderives_induct[consumes 1, case_names Base Step]:
  assumes derives: "leftderives a b"
  assumes Pa: "P a"
  assumes induct: "\<And>y z. leftderives a y \<Longrightarrow> leftderives1 y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
proof -
  note rtrancl_lemma = rtrancl_induct[where a = a and b = b and r = leftderivations1 and P=P]
  from derives Pa induct rtrancl_lemma show "P b"
    by (metis leftderives_def leftderivations_def leftderives1_eq_leftderivations1)
qed

end

context CFG begin

lemma derives1_implies_derives[simp]:"derives1 a b \<Longrightarrow> derives a b"
  by (auto simp add: derives_def derivations_def derivations1_def)

lemma derives_trans: "derives a b \<Longrightarrow> derives b c \<Longrightarrow> derives a c"
  by (auto simp add: derives_def derivations_def)

lemma derives1_eq_derivations1: "derives1 x y = ((x, y) \<in> derivations1)"
  by (simp add: derivations1_def)

lemma derives_induct[consumes 1, case_names Base Step]:
  assumes derives: "derives a b"
  assumes Pa: "P a"
  assumes induct: "\<And>y z. derives a y \<Longrightarrow> derives1 y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
proof -
  note rtrancl_lemma = rtrancl_induct[where a = a and b = b and r = derivations1 and P=P]
  from derives Pa induct rtrancl_lemma show "P b"
    by (metis derives_def derivations_def derives1_eq_derivations1)
qed

end

type_synonym 'a derivation = "(nat \<times> 'a rule) list"

context CFG begin

definition Derives1 :: "'a sentence \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "Derives1 u i r v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> (N, \<alpha>) \<in> set \<RR>
        \<and> r = (N, \<alpha>) \<and> i = length x)"  

lemma Derives1_split:
  "Derives1 u i r v \<Longrightarrow> \<exists> x y. u = x @ [fst r] @ y \<and> v = x @ (snd r) @ y \<and> length x = i"
  by (metis Derives1_def fst_conv snd_conv)

lemma Derives1_implies_derives1: "Derives1 u i r v \<Longrightarrow> derives1 u v"
  by (auto simp add: Derives1_def derives1_def)

lemma derives1_implies_Derives1: "derives1 u v \<Longrightarrow> \<exists> i r. Derives1 u i r v"
  by (auto simp add: Derives1_def derives1_def)

lemma Derives1_unique_dest: "Derives1 u i r v \<Longrightarrow> Derives1 u i r w \<Longrightarrow> v = w"
  by (auto simp add: Derives1_def derives1_def)

lemma Derives1_unique_src: "Derives1 u i r w \<Longrightarrow> Derives1 v i r w \<Longrightarrow> u = v"
  by (auto simp add: Derives1_def derives1_def)

fun Derivation :: "'a sentence \<Rightarrow> 'a derivation \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "Derivation a [] b = (a = b)"
| "Derivation a (d#D) b = (\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b)"

lemma Derivation_implies_derives: "Derivation a D b \<Longrightarrow> derives a b"
proof (induct D arbitrary: a b)
  case Nil thus ?case 
    by (simp add: derives_def derivations_def)
next
  case (Cons d D)
    note ihyps = this
    from ihyps have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b" by auto
    then obtain x where "Derives1 a (fst d) (snd d) x" and xb: "Derivation x D b" by blast
    with Derives1_implies_derives1 have d1: "derives a x" by auto
    from ihyps xb have d2:"derives x b" by simp
    show "derives a b" by (rule derives_trans[OF d1 d2])
qed 

lemma Derivation_Derives1: "Derivation a S y \<Longrightarrow> Derives1 y i r z \<Longrightarrow> Derivation a (S@[(i,r)]) z"
proof (induct S arbitrary: a y z i r)
  case Nil thus ?case by simp
next
  case (Cons s S) thus ?case 
    by (metis Derivation.simps(2) append_Cons) 
qed

lemma derives_implies_Derivation: "derives a b \<Longrightarrow> \<exists> D. Derivation a D b"
proof (induct rule: derives_induct)
  case Base
  show ?case by (rule exI[where x="[]"], simp)
next
  case (Step y z)
  note ihyps = this
  from ihyps obtain D where ay: "Derivation a D y" by blast
  from ihyps derives1_implies_Derives1 obtain i r where yz: "Derives1 y i r z" by blast
  from Derivation_Derives1[OF ay yz] show ?case by auto
qed
    
lemma Derives1_take: "Derives1 a i r b \<Longrightarrow> take i a = take i b"
  by (auto simp add: Derives1_def)

lemma Derives1_drop: "Derives1 a i r b \<Longrightarrow> drop (Suc i) a = drop (i + length (snd r)) b"
  by (auto simp add: Derives1_def)

lemma Derives1_bound: "Derives1 a i r b \<Longrightarrow> i < length a"
  by (auto simp add: Derives1_def)

lemma Derives1_length: "Derives1 a i r b \<Longrightarrow> length b = length a + length (snd r) - 1"
  by (auto simp add: Derives1_def)

definition leftmost :: "nat \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "leftmost i s = (i < length s \<and> is_word (take i s) \<and> is_nonterminal (s ! i))" 

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

lemma rule_nonterminal_type[simp]: "(N, \<alpha>) \<in> set \<RR> \<Longrightarrow> is_nonterminal N"
  apply (insert valid_rules)
  by (auto simp add: is_nonterminal_def)

lemma [elim]: "Derives1 a i r b \<Longrightarrow> r \<in> set \<RR>"
  using Derives1_def by auto

lemma is_symbol_distinct: "is_terminal x \<noteq> is_nonterminal x"
  apply (insert disjunct_symbols)
  apply (auto simp add: is_terminal_def is_nonterminal_def)
  using univ_symbols by auto

lemma is_terminal_nonterminal: "is_terminal x \<Longrightarrow> is_nonterminal x \<Longrightarrow> False"
  by (metis is_symbol_distinct)

lemma Derives1_leftmost:
  assumes "Derives1 a i r b"
  shows "\<exists> j. leftmost j a \<and> j \<le> i"
proof -
  let ?J = "{j . j < length a \<and> is_nonterminal (a ! j)}"
  let ?M = "Min ?J"
  from assms have J1:"i \<in> ?J"
    apply (auto simp add: Derives1_def is_nonterminal_def)
    by (metis (mono_tags, lifting) prod.simps(2) valid_rules)
  have J2:"finite ?J" by auto
  note J = J1 J2
  from J have M1: "?M \<in> ?J" by (rule_tac Min_in, auto) 
  {
    fix j
    assume "j \<in> ?J"
    with J have "?M \<le> j" by auto
  }
  note M3 = this[OF J1]
  have is_word: "is_word (take ?M a)"
    apply (auto simp add: is_word_def list_all_take)
    by (smt (verit, ccfv_SIG) \<open>\<And>j. j \<in> {j. j < length a \<and> is_nonterminal (a ! j)} \<Longrightarrow> Min {j. j < length a \<and> is_nonterminal (a ! j)} \<le> j\<close> is_symbol_distinct less_le_not_le mem_Collect_eq set_take)
  show ?thesis 
    apply (rule_tac exI[where x="?M"])
    apply (simp add: leftmost_def)
    by (metis (mono_tags, lifting) M1 M3 is_word mem_Collect_eq)
qed

lemma Derivation_leftmost: "D \<noteq> [] \<Longrightarrow> Derivation a D b \<Longrightarrow> \<exists> i. leftmost i a"
  apply (case_tac "D")
  apply (auto)
  apply (metis Derives1_leftmost)
  done

lemma nonword_has_nonterminal:
  "\<not> (is_word a) \<Longrightarrow> \<exists> k. k < length a \<and> is_nonterminal (a ! k)"
  apply (auto simp add: list_all_iff is_word_def)
  by (metis in_set_conv_nth is_symbol_distinct)

lemma leftmost_cons_nonterminal: 
  "is_nonterminal x \<Longrightarrow> leftmost 0 (x#xs)"
  by (simp add: leftmost_def)

lemma leftmost_cons_terminal: 
  "is_terminal x \<Longrightarrow> leftmost i (x#xs) = (i > 0 \<and> leftmost (i - 1) xs)"
  using is_terminal_nonterminal is_word_def leftmost_def
  by (smt (verit, ccfv_threshold) Suc_diff_1 Suc_less_eq length_Cons list.set_intros(2) not_gr0 nth_Cons' set_ConsD take_Suc_Cons)

lemma is_nonterminal_cons_terminal: 
  "is_terminal x \<Longrightarrow> k < length (x # a) \<Longrightarrow> is_nonterminal ((x # a) ! k) \<Longrightarrow>
   k > 0 \<and> k - 1 < length a \<and> is_nonterminal (a ! (k - 1))"
by (metis One_nat_def Suc_leI is_terminal_nonterminal less_diff_conv2 
    list.size(4) nth_non_equal_first_eq)

lemma leftmost_exists:
  "k < length a \<Longrightarrow> is_nonterminal (a ! k) \<Longrightarrow> 
   \<exists> i. leftmost i a \<and> i \<le> k" 
proof (induct a arbitrary: k)
  case Nil thus ?case by auto
next
  case (Cons x a) 
  show ?case
  proof(cases "is_nonterminal x")
    case True thus ?thesis
      apply(rule_tac exI[where x="0"])
      apply (simp add: leftmost_cons_nonterminal)
      done
  next
    case False
    then have x: "is_terminal x"
      by (metis is_symbol_distinct)
    note k = is_nonterminal_cons_terminal[OF x Cons(2) Cons(3)]
    with Cons have "\<exists>i. leftmost i a \<and> i \<le> k - 1" by blast
    then show ?thesis
      apply (auto simp add: leftmost_cons_terminal[OF x])
      by (metis le_diff_conv2 Suc_leI add_Suc_right add_diff_cancel_right' k 
          le_0_eq le_imp_less_Suc nat_le_linear)
  qed
qed

lemma nonword_leftmost_exists: 
  "\<not> (is_word a) \<Longrightarrow> \<exists> i. leftmost i a"
  by (metis leftmost_exists nonword_has_nonterminal)
  
lemma leftmost_unaffected_Derives1: "leftmost j a \<Longrightarrow> j < i \<Longrightarrow> Derives1 a i r b \<Longrightarrow> leftmost j b"
apply (simp add: leftmost_def)
proof -
  assume a1: "j < length a \<and> is_word (take j a) \<and> is_nonterminal (a ! j)"
  assume a2: "j < i"
  assume "Derives1 a i r b"
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
  then show "j < length b \<and> is_word (take j b) \<and> is_nonterminal (b ! j)"
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
  "derivation_ge D (Suc i) \<Longrightarrow> leftmost i a \<Longrightarrow> Derivation a D b \<Longrightarrow> leftmost i b"
proof (induct D arbitrary: a)
  case Nil thus ?case by auto
next
  case (Cons d D) 
  then have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b" by simp
  then obtain x where x1: "Derives1 a (fst d) (snd d) x" and x2: "Derivation x D b" by blast  
  with Cons have leftmost_x: "leftmost i x"
    apply (rule_tac leftmost_unaffected_Derives1[
           where a=a and j=i and b="x" and i="fst d" and r="snd d"])
    by (auto simp add: derivation_ge_def)
  with Cons x2 show ?case by (auto simp add: derivation_ge_def)
qed

lemma le_Derives1_take: 
  assumes le: "i \<le> j" 
  and D: "Derives1 a j r b"
  shows "take i a = take i b"
proof -
  note Derives1_take[where a=a and i=j and r=r and b=b]
  with le D show ?thesis by (rule_tac le_take_same[where i=i and j=j], auto)
qed  

lemma Derivation_take: "derivation_ge D i \<Longrightarrow> Derivation a D b \<Longrightarrow> take i a = take i b"
proof(induct D arbitrary: a b)
  case Nil thus ?case by auto
next
  case (Cons d D)
  then have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b"
    by simp
  then obtain x where ax: "Derives1 a (fst d) (snd d) x" and xb: "Derivation x D b" by blast  
  from derivation_ge_cons Cons(2) have d: "i \<le> fst d" and D: "derivation_ge D i" by auto
  note take_i_xb = Cons(1)[OF D xb]
  note take_i_ax = le_Derives1_take[OF d ax]
  from take_i_xb take_i_ax show ?case by auto
qed

lemma leftmost_cons_less: "i < length u \<Longrightarrow> leftmost i (u@v) = leftmost i u"
  by (auto simp add: leftmost_def nth_append)

lemma leftmost_is_nonterminal: "leftmost i u \<Longrightarrow> is_nonterminal (u ! i)"
  by (metis leftmost_def)

lemma is_word_is_terminal: "i < length u \<Longrightarrow> is_word u \<Longrightarrow> is_terminal (u ! i)"
  using is_word_def by force
  
lemma leftmost_append: 
  assumes leftmost: "leftmost i (u@v)"
  and is_word: "is_word u"
  shows "length u \<le> i"
proof (cases "i < length u")
  case False thus ?thesis by auto
next
  case True 
  with leftmost have "leftmost i u" using leftmost_cons_less[OF True] by simp
  then have is_nonterminal: "is_nonterminal (u ! i)" by (rule leftmost_is_nonterminal)
  note is_terminal = is_word_is_terminal[OF True is_word]
  note is_terminal_nonterminal[OF is_terminal is_nonterminal]
  then show ?thesis by auto
qed

lemma derivation_ge_empty[simp]: "derivation_ge [] i" 
by (simp add: derivation_ge_def)

lemma leftmost_notword: "leftmost i a \<Longrightarrow> j > i \<Longrightarrow> \<not> (is_word (take j a))"
  by (metis append_take_drop_id leD leI leftmost_append leftmost_def length_take min.absorb4 take_all_iff)

lemma leftmost_unique: "leftmost i a \<Longrightarrow> leftmost j a \<Longrightarrow> i = j" 
  by (metis leftmost_def leftmost_notword linorder_neqE_nat)

lemma leftmost_Derives1: "leftmost i a \<Longrightarrow> Derives1 a j r b \<Longrightarrow> i \<le> j"
  by (metis Derives1_leftmost leftmost_unique)

lemma leftmost_Derives1_propagate: 
  assumes leftmost: "leftmost i a"
      and Derives1: "Derives1 a j r b"
    shows "(is_word b \<and> i = j) \<or> (\<exists> k. leftmost k b \<and> i \<le> k)"
proof -
  from leftmost_Derives1[OF leftmost Derives1] have ij: "i \<le> j" by auto
  show ?thesis
  proof (cases "is_word b")
    case True show ?thesis
      by (metis Derives1 True ij le_neq_implies_less leftmost 
          leftmost_unaffected_Derives1 order_refl)
  next
    case False show ?thesis
      by (metis (no_types, opaque_lifting) Derives1 Derives1_bound
          Derives1_take append_take_drop_id ij le_neq_implies_less leftmost 
          leftmost_append leftmost_cons_less leftmost_def length_take 
          min.absorb2 nat_le_linear nonword_leftmost_exists not_le)
  qed
qed

lemma is_word_Derives1[elim]: "is_word a \<Longrightarrow> Derives1 a i r b \<Longrightarrow> False"
  by (metis Derives1_leftmost is_terminal_nonterminal is_word_is_terminal leftmost_def)
  
lemma is_word_Derivation[elim]: "is_word a \<Longrightarrow> Derivation a D b \<Longrightarrow> D = []"
  by (meson Derivation_leftmost is_symbol_distinct is_word_is_terminal leftmost_def)
 
lemma leftmost_Derivation: 
  "leftmost i a \<Longrightarrow> Derivation a D b \<Longrightarrow> j \<le> i \<Longrightarrow> derivation_ge D j"
proof (induct D arbitrary: a b i j)
  case Nil thus ?case by auto
next
  case (Cons d D)
  then have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b" by auto
  then obtain x where ax:"Derives1 a (fst d) (snd d) x" and xb:"Derivation x D b" by blast
  note ji = Cons(4)
  note i_fstd = leftmost_Derives1[OF Cons(2) ax]
  note disj = leftmost_Derives1_propagate[OF Cons(2) ax]
  thus ?case
  proof(induct rule: disjCases2)
    case 1 
    with xb have "D = []" by auto
    with 1 ji show ?case by (simp add: derivation_ge_def)
  next
    case 2 
    then obtain k where k: "leftmost k x" and ik: "i \<le> k" by blast
    note ge = Cons(1)[OF k xb, where j=j]
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
  and "Derives1 a j p b"
  and "Derives1 b i q c"
  shows "\<exists> b'. Derives1 a i q b' \<and> Derives1 b' (j - 1 + length (snd q)) p c"
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
  from assms have q_dom: "q \<in> set \<RR>" by auto
  have a_b': "Derives1 a i q ?b"
    apply (subst Derives1_def)
    apply (rule exI[where x="b1"])
    apply (rule exI[where x="u@[fst p]@a2"])
    apply (rule exI[where x="fst q"])
    apply (rule exI[where x="snd q"])
    apply (auto simp add: b1_len a_src u1 q_dom)
    done
  from assms have p_dom: "p \<in> set \<RR>" by auto
  have b'_c: "Derives1 ?b (j - 1 + length (snd q)) p c"
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

lemma Derivation_append: "Derivation a (D@E) c = (\<exists> b. Derivation a D b \<and> Derivation b E c)"
proof(induct D arbitrary: a c E)
  case Nil thus ?case by auto
next
  case (Cons d D) thus ?case by auto
qed

lemma Derivation_implies_append: 
  "Derivation a D b \<Longrightarrow> Derivation b E c \<Longrightarrow> Derivation a (D@E) c"
using Derivation_append by blast

lemma Derivation_swap_single_end_to_front: 
  "i < j \<Longrightarrow> derivation_ge D j \<Longrightarrow> Derivation a (D@[(i,r)]) b \<Longrightarrow>
   Derivation a ((i,r)#(derivation_shift D 1 (length (snd r)))) b"
proof(induct D arbitrary: a)
  case Nil thus ?case by auto
next
  case (Cons d D) 
  from Cons have "\<exists> c. Derives1 a (fst d) (snd d) c \<and> Derivation c (D @ [(i, r)]) b"
    by simp
  then obtain c where ac: "Derives1 a (fst d) (snd d) c"
    and cb: "Derivation c (D @ [(i, r)]) b" by blast
  from Cons(3) have D_j: "derivation_ge D j" by (simp add: derivation_ge_cons)
  from Cons(1)[OF Cons(2) D_j cb, simplified]
  obtain x where cx: "Derives1 c i r x" and  
    xb: "Derivation x (derivation_shift D 1 (length (snd r))) b" by auto
  have i_fst_d: "i < fst d" using Cons derivation_ge_cons by auto
  from Derives1_Derives1_swap[OF i_fst_d ac cx]
  obtain b' where ab': "Derives1 a i r b'" and 
    b'x: "Derives1 b' (fst d - 1 + length (snd r)) (snd d) x" by blast
  show ?case using ab' b'x xb by auto
qed    

lemma Derivation_swap_single_mid_to_front: 
  assumes "i < j"
  and "derivation_ge D j" 
  and "Derivation a (D@[(i,r)]@E) b"
  shows "Derivation a ((i,r)#((derivation_shift D 1 (length (snd r)))@E)) b"
proof -
  from assms have "\<exists> x. Derivation a (D@[(i, r)]) x \<and> Derivation x E b"
    using Derivation_append by auto
  then obtain x where ax: "Derivation a (D@[(i, r)]) x" and xb: "Derivation x E b"
    by blast
  with assms have "Derivation a ((i, r)#(derivation_shift D 1 (length (snd r)))) x"
    using Derivation_swap_single_end_to_front by blast
  then show ?thesis using Derivation_append xb by auto
qed

lemma length_derivation_shift[simp]: 
  "length(derivation_shift D left right) = length D"
  by (simp add: derivation_shift_def)

definition LeftDerives1 :: "'a sentence \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentence \<Rightarrow> bool" where 
  "LeftDerives1 u i r v = (leftmost i u \<and> Derives1 u i r v)"

lemma LeftDerives1_implies_leftderives1: "LeftDerives1 u i r v \<Longrightarrow> leftderives1 u v"
  by (metis Derives1_def LeftDerives1_def append_eq_conv_conj leftderives1_def leftmost_def)
    
lemma leftmost_Derives1_leftderives: 
  "leftmost i a \<Longrightarrow> Derives1 a i r b \<Longrightarrow> leftderives b c \<Longrightarrow> leftderives a c"
using LeftDerives1_def LeftDerives1_implies_leftderives1 
  leftderives1_implies_leftderives leftderives_trans by blast

theorem Derivation_implies_leftderives_gen:
  "Derivation a D (u@v) \<Longrightarrow> is_word u \<Longrightarrow> (\<exists> w. 
          leftderives a (u@w) \<and> 
          (v = [] \<longrightarrow> w = []) \<and> 
          (\<forall> X. is_first X v \<longrightarrow> is_first X w))"
proof (induct "length D" arbitrary: D a u v)
  case 0
    then have "a = u@v" by auto
    thus ?case by (rule_tac x = v in exI, auto)
next
  case (Suc n)
    from Suc have "D \<noteq> []" by auto
    with Suc Derivation_leftmost have "\<exists> i. leftmost i a" by auto
    then obtain i where i: "leftmost i a" by blast
    show "?case"
    proof (cases "derivation_ge D (Suc i)")
      case True
        with Suc have leftmost: "leftmost i (u@v)" 
          by (rule_tac leftmost_unaffected_Derivation[OF True i], auto)
        have length_u: "length u \<le> i" 
          using leftmost_append[OF leftmost Suc(4)] .
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
      have Di: "derivation_ge D i" 
      using leftmost_Derivation[OF i Suc(3), where j=i, simplified] .
      from split_derivation_leftmost[OF Di False]
      obtain E F r where D_split: "D = E @ [(i, r)] @ F" 
        and E_Suc: "derivation_ge E (Suc i)" by auto
      let ?D = "(derivation_shift E 1 (length (snd r)))@F"
      from D_split 
      have "Derivation a ((i,r) # ?D) (u @ v)"
        using Derivation_swap_single_mid_to_front E_Suc Suc.prems(1) lessI by blast
      then have "\<exists> y. Derives1 a i r y \<and> Derivation y ?D (u @ v)" by simp
      then obtain y where ay:"Derives1 a i r y" 
        and yuv: "Derivation y ?D (u @ v)" by blast
      have length_D': "length ?D = n" using D_split Suc.hyps(2) by auto
      from Suc(1)[OF length_D'[symmetric] yuv Suc(4)] 
      obtain w where "leftderives y (u @ w)" and "(v = [] \<longrightarrow> w = [])" 
        and "\<forall>X. is_first X v \<longrightarrow> is_first X w" by blast 
      then show ?thesis using ay i leftmost_Derives1_leftderives by blast
    qed    
qed   

lemma derives_implies_leftderives_gen: "derives a (u@v) \<Longrightarrow> is_word u \<Longrightarrow> (\<exists> w. 
          leftderives a (u@w) \<and> 
          (v = [] \<longrightarrow> w = []) \<and> 
          (\<forall> X. is_first X v \<longrightarrow> is_first X w))"
using Derivation_implies_leftderives_gen derives_implies_Derivation by blast

lemma derives_implies_leftderives: "derives a b \<Longrightarrow> is_word b \<Longrightarrow> leftderives a b"
using derives_implies_leftderives_gen by force

fun LeftDerivation :: "'a sentence \<Rightarrow> 'a derivation \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "LeftDerivation a [] b = (a = b)"
| "LeftDerivation a (d#D) b = (\<exists> x. LeftDerives1 a (fst d) (snd d) x \<and> LeftDerivation x D b)"
  
lemma LeftDerives1_implies_Derives1: "LeftDerives1 a i r b \<Longrightarrow> Derives1 a i r b"
by (metis LeftDerives1_def)

lemma LeftDerivation_implies_Derivation:
  "LeftDerivation a D b \<Longrightarrow> Derivation a D b"
proof (induct D arbitrary: a)
  case (Nil) thus ?case by simp
next
  case (Cons d D)
  thus ?case
  using CFG.LeftDerivation.simps(2) CFG_axioms Derivation.simps(2) 
    LeftDerives1_implies_Derives1 by (meson LeftDerivation.simps(2))
qed

lemma LeftDerivation_implies_leftderives: "LeftDerivation a D b \<Longrightarrow> leftderives a b"
proof (induct D arbitrary: a b)
  case Nil thus ?case by simp
next
  case (Cons d D)
    note ihyps = this
    from ihyps have "\<exists> x. LeftDerives1 a (fst d) (snd d) x \<and> LeftDerivation x D b" by auto
    then obtain x where "LeftDerives1 a (fst d) (snd d) x" and xb: "LeftDerivation x D b" by blast
    with LeftDerives1_implies_leftderives1 have d1: "leftderives a x" by auto
    from ihyps xb have d2:"leftderives x b" by simp
    show "leftderives a b" by (rule leftderives_trans[OF d1 d2])
qed 

lemma leftmost_witness[simp]: "leftmost (length x) (x@(N#y)) = (is_word x \<and> is_nonterminal N)"
  by (auto simp add: leftmost_def)

lemma leftderives1_implies_LeftDerives1: 
  assumes leftderives1: "leftderives1 u v"
  shows "\<exists> i r. LeftDerives1 u i r v"
proof -
  from leftderives1 have 
    "\<exists>x y N \<alpha>. u = x @ [N] @ y \<and> v = x @ \<alpha> @ y \<and> is_word x \<and> (N, \<alpha>) \<in> set \<RR>"
    by (simp add: leftderives1_def)
  then obtain x y N \<alpha> where 
    u:"u = x @ [N] @ y" and
    v:"v = x @ \<alpha> @ y" and
    x:"is_word x" and  
    r:"(N, \<alpha>) \<in> set \<RR>"
    by blast
  show ?thesis
    apply (rule_tac x="length x" in exI)
    apply (rule_tac x="(N, \<alpha>)" in exI)
    apply (auto simp add: LeftDerives1_def)
    apply (simp add: leftmost_def x u rule_nonterminal_type[OF r])
    apply (simp add: Derives1_def u v)
    apply (rule_tac x=x in exI)
    apply (rule_tac x=y in exI)
    apply (auto simp add: x r)
    done
qed    

lemma LeftDerivation_LeftDerives1: 
  "LeftDerivation a S y \<Longrightarrow> LeftDerives1 y i r z \<Longrightarrow> LeftDerivation a (S@[(i,r)]) z"
proof (induct S arbitrary: a y z i r)
  case Nil thus ?case by simp
next
  case (Cons s S) thus ?case 
    by (metis LeftDerivation.simps(2) append_Cons) 
qed

lemma leftderives_implies_LeftDerivation: "leftderives a b \<Longrightarrow> \<exists> D. LeftDerivation a D b"
proof (induct rule: leftderives_induct)
  case Base
  show ?case by (rule exI[where x="[]"], simp)
next
  case (Step y z)
  note ihyps = this
  from ihyps obtain D where ay: "LeftDerivation a D y" by blast
  from ihyps leftderives1_implies_LeftDerives1 obtain i r where yz: "LeftDerives1 y i r z" by blast
  from LeftDerivation_LeftDerives1[OF ay yz] show ?case by auto
qed

lemma LeftDerivation_append: 
  "LeftDerivation a (D@E) c = (\<exists> b. LeftDerivation a D b \<and> LeftDerivation b E c)"
proof(induct D arbitrary: a c E)
  case Nil thus ?case by auto
next
  case (Cons d D) thus ?case by auto
qed

lemma LeftDerivation_implies_append: 
  "LeftDerivation a D b \<Longrightarrow> LeftDerivation b E c \<Longrightarrow> LeftDerivation a (D@E) c"
using LeftDerivation_append by blast

lemma Derivation_unique_dest: "Derivation a D b \<Longrightarrow> Derivation a D c \<Longrightarrow> b = c"
  apply (induct D arbitrary: a b c)
  apply auto
  using Derives1_unique_dest by blast

lemma Derivation_unique_src: "Derivation a D c \<Longrightarrow> Derivation b D c \<Longrightarrow> a = b"
  apply (induct D arbitrary: a b c)
  apply auto
  using Derives1_unique_src by blast

lemma LeftDerives1_unique: "LeftDerives1 a i r b \<Longrightarrow> LeftDerives1 a j s b \<Longrightarrow> i = j \<and> r = s"
using Derives1_def LeftDerives1_def leftmost_unique by auto
 
lemma leftlang: "\<L> = { v | v. is_word v \<and> is_leftderivation v }"
by (metis (no_types, lifting) CFG.is_derivation_def CFG.is_leftderivation_def 
    CFG.leftderivation_implies_derivation CFG_axioms Collect_cong 
    \<L>_def derives_implies_leftderives)
  
lemma leftprefixlang:  "\<L>\<^sub>P = { u | u v. is_word u \<and> is_leftderivation (u@v) }"
apply (auto simp add: \<L>\<^sub>P_def)
using derives_implies_leftderives_gen is_derivation_def is_leftderivation_def apply blast
using leftderivation_implies_derivation by blast

lemma derives_implies_leftderives_cons:
  "is_word a \<Longrightarrow> derives u (a@X#b) \<Longrightarrow> \<exists> c. leftderives u  (a@X#c)"
by (metis append_Cons append_Nil derives_implies_leftderives_gen is_first_def) 

lemma is_word_append[simp]: "is_word (a@b) = (is_word a \<and> is_word b)"
  by (auto simp add: is_word_def)

lemma \<L>\<^sub>P_split: "a@b \<in> \<L>\<^sub>P \<Longrightarrow> a \<in> \<L>\<^sub>P"
  by (auto simp add: \<L>\<^sub>P_def)

lemma \<L>\<^sub>P_is_word: "a \<in> \<L>\<^sub>P \<Longrightarrow> is_word a"
  by (metis (no_types, lifting) leftprefixlang mem_Collect_eq)

definition Derive :: "'a sentence \<Rightarrow> 'a derivation \<Rightarrow> 'a sentence" where 
  "Derive a D = (THE b. Derivation a D b)"

lemma Derivation_dest_ex_unique: "Derivation a D b \<Longrightarrow> \<exists>! x. Derivation a D x"
  using CFG.Derivation_unique_dest CFG_axioms by metis

lemma Derive:
  assumes ab: "Derivation a D b"
  shows "Derive a D = b"
proof -
  note the1_equality[OF Derivation_dest_ex_unique[OF ab] ab]
  thus ?thesis by (simp add: Derive_def)
qed

end

subsection \<open>LocalLexing.thy\<close>

fun funpower :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "funpower f 0 x = x"
| "funpower f (Suc n) x = f (funpower f n x)"

definition natUnion :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "natUnion f = \<Union> { f n | n. True }"

definition limit  :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit f x = natUnion (\<lambda> n. funpower f n x)"

subsection \<open>Limit.thy\<close>

definition setmonotone :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "setmonotone f = (\<forall> X. X \<subseteq> f X)"

lemma setmonotone_funpower: "setmonotone f \<Longrightarrow> setmonotone (funpower f n)"
  by (induct n, auto simp add: setmonotone_def)

lemma subset_setmonotone: "setmonotone f \<Longrightarrow> X \<subseteq> f X"
  by (simp add: setmonotone_def)

lemma elem_setmonotone: "setmonotone f \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> f X"
  by (auto simp add: setmonotone_def)

lemma elem_natUnion: "(\<forall> n. x \<in> f n) \<Longrightarrow> x \<in> natUnion f"
  by (auto simp add: natUnion_def)

lemma subset_natUnion: "(\<forall> n. X \<subseteq> f n) \<Longrightarrow> X \<subseteq> natUnion f"
  by (auto simp add: natUnion_def)
  
lemma setmonotone_limit:
  assumes fmono: "setmonotone f"
  shows "setmonotone (limit f)"
proof -
  show "setmonotone (limit f)" 
    apply (auto simp add: setmonotone_def limit_def)
    apply (rule elem_natUnion, auto)
    apply (rule elem_setmonotone[OF setmonotone_funpower])
    by (auto simp add: fmono)
qed

lemma[simp]: "funpower id n = id"
  by (rule ext, induct n, simp_all)

lemma[simp]: "limit id = id"
  by (rule ext, auto simp add: limit_def natUnion_def)

lemma natUnion_decompose[consumes 1, case_names Decompose]:
  assumes p: "p \<in> natUnion S"
  assumes decompose: "\<And> n p. p \<in> S n \<Longrightarrow> P p" 
  shows "P p" 
proof -
  from p have "\<exists> n. p \<in> S n" 
    by (auto simp add: natUnion_def)
  then obtain n where "p \<in> S n" by blast
  from decompose[OF this] show ?thesis .
qed

lemma limit_induct[consumes 1, case_names Init Iterate]:
  assumes p: "(p :: 'a) \<in> limit f X"
  assumes init: "\<And> p. p \<in> X \<Longrightarrow> P p"
  assumes iterate: "\<And> p Y. (\<And> q . q \<in> Y \<Longrightarrow> P q) \<Longrightarrow> p \<in> f Y \<Longrightarrow> P p"
  shows "P p"
proof -
  from p have p_in_natUnion: "p \<in> natUnion (\<lambda> n. funpower f n X)"    
    by (simp add: limit_def)
  {
    fix p :: 'a
    fix n :: nat
    have "p \<in> funpower f n X \<Longrightarrow> P p"
    proof (induct n arbitrary: p) 
      case 0 thus ?case using init[OF 0[simplified]] by simp
    next
      case (Suc n) show ?case 
        using iterate[OF Suc(1) Suc(2)[simplified], simplified] by simp
    qed
  }
  with p_in_natUnion show ?thesis
    by (induct rule: natUnion_decompose)
qed

definition chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "chain C = (\<forall> i. C i \<subseteq> C (i + 1))"

definition continuous :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool"
where
  "continuous f = (\<forall> C. chain C \<longrightarrow> (chain (f o C) \<and> f (natUnion C) = natUnion (f o C)))"

lemma continuous_apply:
  "continuous f \<Longrightarrow> chain C \<Longrightarrow> f (natUnion C) = natUnion (f o C)"
by (simp add: continuous_def)

lemma continuous_imp_mono:
  assumes continuous: "continuous f"
  shows "mono f"
proof -
  { 
    fix A :: "'a set"
    fix B :: "'a set"
    assume sub: "A \<subseteq> B"
    let ?C = "\<lambda> (i::nat). if (i = 0) then A else B"
    have "chain ?C" by (simp add: chain_def sub) 
    then have fC: "chain (f o ?C)" using continuous continuous_def by blast
    then have "f (?C 0) \<subseteq> f (?C (0 + 1))"
    proof -
      have "\<And>f n. \<not> chain f \<or> (f n::'b set) \<subseteq> f (Suc n)"
        by (metis Suc_eq_plus1 chain_def)
      then show ?thesis using fC by fastforce
    qed
    then have "f A \<subseteq> f B" by auto
  }
  then show "mono f" by (simp add: monoI)
qed 
      
lemma mono_maps_chain_to_chain: 
  assumes f: "mono f"
  assumes C: "chain C"
  shows "chain (f o C)"
by (metis C comp_def f chain_def mono_def)

lemma natUnion_upperbound: 
  "(\<And> n. f n \<subseteq> G) \<Longrightarrow> (natUnion f) \<subseteq> G"
by (auto simp add: natUnion_def)

lemma funpower_upperbound:
  "(\<And> I. I \<subseteq> G \<Longrightarrow> f I \<subseteq> G) \<Longrightarrow> I \<subseteq> G \<Longrightarrow> funpower f n I \<subseteq> G"
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case by simp
qed

lemma limit_upperbound:
  "(\<And> I. I \<subseteq> G \<Longrightarrow> f I \<subseteq> G) \<Longrightarrow> I \<subseteq> G \<Longrightarrow> limit f I \<subseteq> G"
by (simp add: funpower_upperbound limit_def natUnion_upperbound)

lemma elem_limit_simp: "x \<in> limit f X = (\<exists> n. x \<in> funpower f n X)"
by (auto simp add: limit_def natUnion_def)

definition pointwise :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "pointwise f = (\<forall> X. f X = \<Union> { f {x} | x. x \<in> X})" 

lemma pointwise_simp: 
  assumes f: "pointwise f"
  shows "f X =  \<Union> { f {x} | x. x \<in> X}"
proof -
  from f have "\<forall> X. f X = \<Union> { f {x} | x. x \<in> X}"
    by (rule iffD1[OF pointwise_def[where f=f]])
  then show ?thesis by blast
qed

lemma natUnion_elem: "x \<in> f n \<Longrightarrow> x \<in> natUnion f"
using natUnion_def by fastforce
  
lemma limit_elem: "x \<in> funpower f n X \<Longrightarrow> x \<in> limit f X"
by (simp add: limit_def natUnion_elem)

lemma limit_step_pointwise:
  assumes x: "x \<in> limit f X"
  assumes f: "pointwise f"
  assumes y: "y \<in> f {x}"
  shows "y \<in> limit f X"
proof - 
  from x have "\<exists> n. x \<in> funpower f n X" 
    by (simp add: elem_limit_simp)
  then obtain n where n: "x \<in> funpower f n X" by blast
  have "y \<in> funpower f (Suc n) X"
    apply simp 
    apply (subst pointwise_simp[OF f])
    using y n by auto
  then show "y \<in> limit f X" by (meson limit_elem)
qed

definition pointbase :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set" where
  "pointbase F I = \<Union> { F X | X. finite X \<and> X \<subseteq> I }"

definition pointbased :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "pointbased f = (\<exists> F. f = pointbase F)"

lemma pointwise_implies_pointbased:
  assumes pointwise: "pointwise f"
  shows "pointbased f"
proof -
  let ?F = "\<lambda> X. f X"
  {
    fix I :: "'a set"
    fix x :: "'b"
    have lr: "x \<in> pointbase ?F I \<Longrightarrow> x \<in> f I"
    proof -
      assume x: "x \<in> pointbase ?F I"
      have "\<exists> X. x \<in> f X \<and> X \<subseteq> I"
        proof -
          have "x \<in> \<Union>{f A |A. finite A \<and> A \<subseteq> I}"
            by (metis pointbase_def x)
          then show ?thesis
            by blast
        qed
      then obtain X where X:"x \<in> f X \<and> X \<subseteq> I" by blast
      have "\<exists> y. y \<in> I \<and> x \<in> f {y}"
        using X apply (simp add: pointwise_simp[OF pointwise, where X=X])
        by blast
      then show "x \<in> f I"
        apply (simp add: pointwise_simp[OF pointwise, where X=I])
        by blast
    qed
    have rl: "x \<in> f I \<Longrightarrow> x \<in> pointbase ?F I"
    proof -
      assume x: "x \<in> f I"
      have "\<exists> y. y \<in> I \<and> x \<in> f {y}"
        using x apply (simp add: pointwise_simp[OF pointwise, where X=I])
        by blast
      then obtain y where "y \<in> I \<and> x \<in> f {y}" by blast
      then have "\<exists> X. x \<in> f X \<and> finite X \<and> X \<subseteq> I" by blast
      then show "x \<in> pointbase f I"
        apply (simp add: pointbase_def)
        by blast
    qed
    note lr rl
  }
  then have "\<And> I. pointbase f I = f I" by blast
  then have "pointbase f = f" by blast
  then show ?thesis by (metis pointbased_def) 
qed  
   
lemma pointbase_is_mono:
  "mono (pointbase f)"
proof -
  {
    fix A :: "'a set"
    fix B :: "'a set"
    assume subset: "A \<subseteq> B"
    have "(pointbase f) A \<subseteq> (pointbase f) B" 
      apply (simp add: pointbase_def)
      using subset by fastforce
  }
  then show ?thesis by (simp add: mono_def)
qed

lemma chain_implies_mono: "chain C \<Longrightarrow> mono C"
by (simp add: chain_def mono_iff_le_Suc)

lemma chain_cover_witness: "finite X \<Longrightarrow> chain C \<Longrightarrow> X \<subseteq> natUnion C \<Longrightarrow> \<exists> n. X \<subseteq> C n"
proof (induct rule: finite.induct)
  case emptyI thus ?case by blast
next
  case (insertI X x) 
  then have "X \<subseteq> natUnion C" by simp
  with insertI have "\<exists> n. X \<subseteq> C n" by blast
  then obtain n where n: "X \<subseteq> C n" by blast
  have x: "x \<in> natUnion C" using insertI.prems(2) by blast
  then have "\<exists> m. x \<in> C m"
  proof -
    have "x \<in> \<Union>{A. \<exists>n. A = C n}" by (metis x natUnion_def)
    then show ?thesis by blast
  qed
  then obtain m where m: "x \<in> C m" by blast
  have mono_C: "\<And> i j. i \<le> j \<Longrightarrow> C i \<subseteq> C j"
    using chain_implies_mono insertI(3) mono_def by blast 
  show ?case
    apply (rule_tac x="max n m" in exI)
    apply auto
    apply (meson contra_subsetD m max.cobounded2 mono_C)
    by (metis max_def mono_C n subsetCE)
qed
    
lemma pointbase_is_continuous:
  "continuous (pointbase f)"
proof -
  {
    fix C :: "nat \<Rightarrow> 'a set"
    assume C: "chain C"
    have mono: "chain ((pointbase f) o C)"
      by (simp add: C mono_maps_chain_to_chain pointbase_is_mono)
    have subset1: "natUnion ((pointbase f) o C) \<subseteq> (pointbase f) (natUnion C)"
    proof (auto)
      fix y :: "'b"
      assume "y \<in> natUnion ((pointbase f) o C)"
      then show "y \<in> (pointbase f) (natUnion C)"
      proof (induct rule: natUnion_decompose)
        case (Decompose n p)
          thus ?case by (metis comp_apply contra_subsetD mono_def natUnion_elem 
            pointbase_is_mono subsetI) 
      qed
    qed
    have subset2: "(pointbase f) (natUnion C) \<subseteq> natUnion ((pointbase f) o C)"
    proof (auto)
      fix y :: "'b"
      assume y: "y \<in> (pointbase f) (natUnion C)"
      have "\<exists> X. finite X \<and> X \<subseteq> natUnion C \<and> y \<in> f X"
      proof -
        have "y \<in> \<Union>{f A |A. finite A \<and> A \<subseteq> natUnion C}"
          by (metis y pointbase_def)
        then show ?thesis by blast
      qed
      then obtain X where X: "finite X \<and> X \<subseteq> natUnion C \<and> y \<in> f X" by blast
      then have "\<exists> n. X \<subseteq> C n" using chain_cover_witness C by blast
      then obtain n where X_sub_C: "X \<subseteq> C n" by blast
      show "y \<in> natUnion ((pointbase f) o C)" 
        apply (rule_tac natUnion_elem[where n=n])
        proof -
          have "y \<in> \<Union>{f A |A. finite A \<and> A \<subseteq> C n}"
          using X X_sub_C by blast
          then show "y \<in> (pointbase f \<circ> C) n" by (simp add: pointbase_def)
      qed
    qed
    note mono subset1 subset2
  }  
  then show ?thesis by (simp add: continuous_def subset_antisym)   
qed
 
lemma pointbased_implies_continuous:
  "pointbased f \<Longrightarrow> continuous f"
  using pointbase_is_continuous pointbased_def by force

lemma setmonotone_implies_chain_funpower:
  assumes setmonotone: "setmonotone f"
  shows "chain (\<lambda> n. funpower f n I)"
by (simp add: chain_def setmonotone subset_setmonotone)  

lemma natUnion_subset: "(\<And> n. \<exists> m. f n \<subseteq> g m) \<Longrightarrow> natUnion f \<subseteq> natUnion g"
  by (meson natUnion_elem natUnion_upperbound subset_iff)

lemma natUnion_eq[case_names Subset Superset]: 
  "(\<And> n. \<exists> m. f n \<subseteq> g m) \<Longrightarrow> (\<And> n. \<exists> m. g n \<subseteq> f m) \<Longrightarrow> natUnion f = natUnion g"
by (simp add: natUnion_subset subset_antisym)
  
lemma natUnion_shift[symmetric]: 
  assumes chain: "chain C"
  shows "natUnion C = natUnion (\<lambda> n. C (n + m))"
proof (induct rule: natUnion_eq)
  case (Subset n)
    show ?case using chain chain_implies_mono le_add1 mono_def by blast 
next
  case (Superset n)
    show ?case by blast 
qed

definition regular :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "regular f = (setmonotone f \<and> continuous f)"

lemma regular_fixpoint:
  assumes regular: "regular f"
  shows "f (limit f I) = limit f I"
proof -
  have setmonotone: "setmonotone f" using regular regular_def by blast
  have continuous: "continuous f" using regular regular_def by blast

  let ?C = "\<lambda> n. funpower f n I"
  have chain: "chain ?C"
    by (simp add: setmonotone setmonotone_implies_chain_funpower)
  have "f (limit f I) = f (natUnion ?C)"
    using limit_def by metis
  also have "f (natUnion ?C) = natUnion (f o ?C)"
    by (metis continuous continuous_def chain)
  also have "natUnion (f o ?C) = natUnion (\<lambda> n. f(funpower f n I))"
    by (meson comp_apply)
  also have "natUnion (\<lambda> n. f(funpower f n I)) = natUnion (\<lambda> n. ?C (n + 1))"
    by simp
  also have "natUnion (\<lambda> n. ?C(n + 1)) = natUnion ?C"
    apply (subst natUnion_shift)
    using chain by (blast+)
  finally show ?thesis by (simp add: limit_def)
qed  
    
lemma fix_is_fix_of_limit:
  assumes fixpoint: "f I = I"   
  shows "limit f I = I"
proof -
  have funpower: "\<And> n. funpower f n I = I" 
  proof -  
    fix n :: nat
    from fixpoint show "funpower f n I = I"
      by (induct n, auto)
  qed
  show ?thesis by (simp add: limit_def funpower natUnion_def)
qed     

lemma limit_is_idempotent: "regular f \<Longrightarrow> limit f (limit f I) = limit f I"
by (simp add: fix_is_fix_of_limit regular_fixpoint)

definition mk_regular1 :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "mk_regular1 P F I = I \<union> { F q x | q x. x \<in> I \<and> P q x }"

definition mk_regular2 :: "('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "mk_regular2 P F I = I \<union> { F q x y | q x y. x \<in> I \<and> y \<in> I \<and> P q x y }"

lemma setmonotone_mk_regular1: "setmonotone (mk_regular1 P F)"
by (simp add: mk_regular1_def setmonotone_def)

lemma setmonotone_mk_regular2: "setmonotone (mk_regular2 P F)"
by (simp add: mk_regular2_def setmonotone_def)

lemma pointbased_mk_regular1: "pointbased (mk_regular1 P F)"
proof -
  let ?f = "\<lambda> X. X \<union> { F q x | q x. x \<in> X \<and> P q x }"
  {
    fix I :: "'a set"
    have 1: "pointbase ?f I \<subseteq> mk_regular1 P F I"
      by (auto simp add: pointbase_def mk_regular1_def)
    have 2: "mk_regular1 P F I \<subseteq> pointbase ?f I"
      apply (simp add: pointbase_def mk_regular1_def)
      apply blast
      done
    from 1 2 have "pointbase ?f I = mk_regular1 P F I" by blast
  }
  then show ?thesis
    apply (subst pointbased_def)
    apply (rule_tac x="?f" in exI)
    by blast
qed

lemma pointbased_mk_regular2: "pointbased (mk_regular2 P F)"
proof -
  let ?f = "\<lambda> X. X \<union> { F q x y | q x y. x \<in> X \<and> y \<in> X \<and> P q x y }"
  {
    fix I :: "'a set"
    have 1: "pointbase ?f I \<subseteq> mk_regular2 P F I"
      by (auto simp add: pointbase_def mk_regular2_def)
    have 2: "mk_regular2 P F I \<subseteq> pointbase ?f I"
      apply (auto simp add: pointbase_def mk_regular2_def)
      apply blast
      proof -
        fix q x y
        assume x: "x \<in> I"
        assume y: "y \<in> I"
        assume P: "P q x y"
        let ?X = "{x, y}"
        let ?A = "?X \<union> {F q x y |q x y. x \<in> ?X \<and> y \<in> ?X \<and> P q x y}"
        show "\<exists>A. (\<exists>X. A = X \<union> {F q x y |q x y. x \<in> X \<and> y \<in> X \<and> P q x y} \<and> 
          finite X \<and> X \<subseteq> I) \<and> F q x y \<in> A"
          apply (rule_tac x="?A" in exI)
          apply (rule conjI)
          apply (rule_tac x="?X" in exI)
          apply (auto simp add: x y)[1]
          using x y P by blast
      qed  
    from 1 2 have "pointbase ?f I = mk_regular2 P F I" by blast
  }
  then show ?thesis
    apply (subst pointbased_def)
    apply (rule_tac x="?f" in exI)
    by blast
qed

lemma regular1:"regular (mk_regular1 P F)"
by (simp add: pointbased_implies_continuous pointbased_mk_regular1 regular_def 
  setmonotone_mk_regular1)
  
lemma regular2: "regular (mk_regular2 P F)"
by (simp add: pointbased_implies_continuous pointbased_mk_regular2 regular_def 
  setmonotone_mk_regular2)

lemma continuous_comp: 
  assumes f: "continuous f"
  assumes g: "continuous g"
  shows "continuous (g o f)"
by (metis (no_types, lifting) comp_assoc comp_def continuous_def f g)

lemma setmonotone_comp:
  assumes f: "setmonotone f"
  assumes g: "setmonotone g"
  shows "setmonotone (g o f)"
by (metis (mono_tags, lifting) comp_def f g rev_subsetD setmonotone_def subsetI)

lemma regular_comp:
  assumes f: "regular f"
  assumes g: "regular g"
  shows "regular (g o f)"
using continuous_comp f g regular_def setmonotone_comp by blast

lemma setmonotone_id[simp]: "setmonotone id"
  by (simp add: id_def setmonotone_def)

lemma continuous_id[simp]: "continuous id"
  by (simp add: continuous_def)

lemma regular_id[simp]: "regular id"
  by (simp add: regular_def)

lemma regular_funpower: "regular f \<Longrightarrow> regular (funpower f n)"
proof (induct n)
  case 0 thus ?case by (simp add: id_def[symmetric])
next
  case (Suc n) 
  have funpower: "funpower f (Suc n) = f o (funpower f n)"
    apply (rule ext)
    by simp
  with Suc show ?case
    by (auto simp only: funpower regular_comp)
qed

lemma mono_id[simp]: "mono id"
  by (simp add: mono_def id_def)

lemma mono_funpower:
  assumes mono: "mono f"
  shows "mono (funpower f n)"
proof (induct n)
  case 0 thus ?case by (simp add: id_def[symmetric])
next
  case (Suc n) 
  show ?case by (simp add: Suc.hyps mono monoD monoI)
qed    

lemma mono_limit:
  assumes mono: "mono f"
  shows "mono (limit f)"
proof(auto simp add: mono_def limit_def)
  fix A :: "'a set" 
  fix B :: "'a set"
  fix x
  assume subset: "A \<subseteq> B"
  assume "x \<in> natUnion (\<lambda>n. funpower f n A)"
  then have "\<exists> n. x \<in> funpower f n A" using elem_limit_simp limit_def by fastforce 
  then obtain n where n: "x \<in> funpower f n A" by blast
  then have mono: "mono (funpower f n)" by (simp add: mono mono_funpower)
  then have "x \<in> funpower f n B" by (meson contra_subsetD monoD n subset)  
  then show "x \<in> natUnion (\<lambda>n. funpower f n B)" by (simp add: natUnion_elem) 
qed

lemma continuous_funpower:
  assumes continuous: "continuous f"
  shows "continuous (funpower f n)"
proof (induct n)
  case 0 thus ?case by (simp add: id_def[symmetric])
next
  case (Suc n)
  have mono: "mono (funpower f (Suc n))" 
    by (simp add: continuous continuous_imp_mono mono_funpower) 
  have chain: "\<forall> C. chain C \<longrightarrow> chain ((funpower f (Suc n)) o C)"
    by (simp del: funpower.simps add: mono mono_maps_chain_to_chain) 
  have limit: "\<And> C. chain C \<Longrightarrow> (funpower f (Suc n)) (natUnion C) = 
      natUnion ((funpower f (Suc n)) o C)"
      apply simp
      apply (subst continuous_apply[OF Suc])
      apply simp
      apply (subst continuous_apply[OF continuous])
      apply (simp add: Suc.hyps continuous_imp_mono mono_maps_chain_to_chain)
      apply (rule arg_cong[where f="natUnion"])
      apply (rule ext)
      by simp
  from chain limit show ?case using continuous_def by blast
qed      

lemma natUnion_swap:
  "natUnion (\<lambda> i. natUnion (\<lambda> j. f i j)) = natUnion (\<lambda> j. natUnion (\<lambda> i. f i j))"
by (metis (no_types, lifting) natUnion_elem natUnion_upperbound subsetI subset_antisym)
      
lemma continuous_limit:
  assumes continuous: "continuous f"
  shows "continuous (limit f)"
proof -
  have mono: "mono (limit f)"
    by (simp add: continuous continuous_imp_mono mono_limit) 
  have chain: "\<And> C. chain C \<Longrightarrow> chain ((limit f) o C)"
    by (simp add: mono mono_maps_chain_to_chain)
  have "\<And> C. chain C \<Longrightarrow> (limit f) (natUnion C) = natUnion ((limit f) o C)"
  proof -
    fix C :: "nat \<Rightarrow> 'a set"
    assume chain_C: "chain C"
    have contpower: "\<And> n. continuous (funpower f n)"
      by (simp add: continuous continuous_funpower) 
    have comp: "\<And> n F. F o C = (\<lambda> i. F (C i))"
      by auto    
    have "(limit f) (natUnion C) = natUnion (\<lambda> n. funpower f n (natUnion C))"
      by (simp add: limit_def)
    also have "natUnion (\<lambda> n. funpower f n (natUnion C)) = 
          natUnion (\<lambda> n. natUnion ((funpower f n) o C))"
      apply (subst continuous_apply[OF contpower])
      apply (simp add: chain_C)+
      done
    also have "natUnion (\<lambda> n. natUnion ((funpower f n) o C)) = 
      natUnion (\<lambda> n. natUnion (\<lambda> i. funpower f n (C i)))" 
      apply (subst comp)
      apply blast
      done
    also have "natUnion (\<lambda> n. natUnion (\<lambda> i. funpower f n (C i))) =
      natUnion (\<lambda> i. natUnion (\<lambda> n. funpower f n (C i)))"
      apply (subst natUnion_swap)
      apply blast
      done
    also have "natUnion (\<lambda> i. natUnion (\<lambda> n. funpower f n (C i))) = 
      (natUnion (\<lambda> i. limit f (C i)))"
      apply (simp add: limit_def)
      done
    also have "natUnion (\<lambda> i. limit f (C i)) = natUnion ((limit f) o C)"
      apply (subst comp)
      apply simp
      done
    finally show "(limit f) (natUnion C) = natUnion ((limit f) o C)" by blast
  qed
  with chain show ?thesis by (simp add: continuous_def)
qed   
      
lemma regular_limit: "regular f \<Longrightarrow> regular (limit f)"
by (simp add: continuous_limit regular_def setmonotone_limit)

lemma regular_implies_mono: "regular f \<Longrightarrow> mono f"
by (simp add: continuous_imp_mono regular_def)

lemma regular_implies_setmonotone: "regular f \<Longrightarrow> setmonotone f"
by (simp add: regular_def)
  
lemma regular_implies_continuous: "regular f \<Longrightarrow> continuous f"
by (simp add: regular_def)

declare [[names_short]]

section \<open>Slices\<close>

\<comment>\<open>slice a b xs: a is inclusive, b is exclusive\<close>
fun slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slice _ _ [] = []"
| "slice _ 0 (x#xs) = []"
| "slice 0 (Suc b) (x#xs) = x # slice 0 b xs"
| "slice (Suc a) (Suc b) (x#xs) = slice a b xs"

lemma slice_drop_take:
  "slice a b xs = drop a (take b xs)"
  by (induction a b xs rule: slice.induct) auto

lemma slice_append_aux:
  "Suc b \<le> c \<Longrightarrow> slice (Suc b) c (x # xs) = slice b (c-1) xs"
  using Suc_le_D by fastforce

lemma slice_concat:
  "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> slice a b xs @ slice b c xs = slice a c xs"
  apply (induction a b xs arbitrary: c rule: slice.induct)
  apply (auto simp: slice_append_aux)
  using Suc_le_D by fastforce

lemma slice_concat_Ex:
  "a \<le> c \<Longrightarrow> slice a c xs = ys @ zs \<Longrightarrow> \<exists>b. ys = slice a b xs \<and> zs = slice b c xs \<and> a \<le> b \<and> b \<le> c"
proof (induction a c xs arbitrary: ys zs rule: slice.induct)
  case (3 b x xs)
  show ?case
  proof (cases ys)
    case Nil
    then obtain zs' where "x # slice 0 b xs = x # zs'" "x # zs' = zs"
      using "3.prems"(2) by auto
    thus ?thesis
      using Nil by force
  next
    case (Cons y ys')
    then obtain ys' where "x # slice 0 b xs = x # ys' @ zs" "x # ys' = ys"
      using "3.prems"(2) by auto
    thus ?thesis
      using "3.IH"[of ys' zs] by force
  qed
next
  case (4 a b x xs)
  thus ?case
    by (auto, metis Earley_Set.slice.simps(4) Suc_le_mono)
qed auto

lemma slice_nth:
  "a < length xs \<Longrightarrow> slice a (a+1) xs = [xs!a]"
  unfolding slice_drop_take
  by (metis Cons_nth_drop_Suc One_nat_def diff_add_inverse drop_take take_Suc_Cons take_eq_Nil)

lemma slice_append_nth:
  "a \<le> b \<Longrightarrow> b < length xs \<Longrightarrow> slice a b xs @ [xs!b] = slice a (b+1) xs"
  by (metis le_add1 slice_concat slice_nth)

lemma slice_empty:
  "b \<le> a \<Longrightarrow> slice a b xs = []"
  by (simp add: slice_drop_take)

lemma slice_id[simp]:
  "slice 0 (length xs) xs = xs"
  by (simp add: slice_drop_take)

lemma slice_subset:
  "set (slice a b xs) \<subseteq> set xs"
  using slice_drop_take by (metis in_set_dropD in_set_takeD subsetI)

lemma slice_singleton:
  "b \<le> length xs \<Longrightarrow> [x] = slice a b xs \<Longrightarrow> b = a + 1"
  by (induction a b xs rule: slice.induct) (auto simp: slice_drop_take)

lemma slice_shift:
  "slice (a+i) (b+i) xs = slice a b (slice i (length xs) xs)"
  unfolding slice_drop_take by (simp add: drop_take)

section \<open>Derivations\<close>

context CFG
begin

lemma Derives1_prepend:
  assumes "Derives1 u i r v"
  shows "Derives1 (w@u) (i + length w) r (w@v)"
proof -
  obtain x y N \<alpha> where *:
    "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
    "(N, \<alpha>) \<in> set \<RR>" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by blast
  hence "w@u = w @ x @ [N] @ y" "w@v = w @ x @ \<alpha> @ y"
    by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="w@x"])
    apply (rule_tac exI[where x="y"])
    by simp
qed

lemma Derivation_prepend:
  "Derivation b D b' \<Longrightarrow> Derivation (a@b) (map (\<lambda>(i, r). (i + length a, r)) D) (a@b')"
  using Derives1_prepend by (induction D arbitrary: b b') (auto, blast)

lemma Derives1_append:
  assumes "Derives1 u i r v"
  shows "Derives1 (u@w) i r (v@w)"
proof -
  obtain x y N \<alpha> where *: 
    "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
    "(N, \<alpha>) \<in> set \<RR>" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by blast
  hence "u@w = x @ [N] @ y @ w" "v@w = x @ \<alpha> @ y @ w"
    by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="x"])
    apply (rule_tac exI[where x="y@w"])
    by blast
qed

lemma Derivation_append':
  "Derivation a D a' \<Longrightarrow> Derivation (a@b) D (a'@b)"
  using Derives1_append by (induction D arbitrary: a a') (auto, blast)

lemma Derivation_append_rewrite:
  assumes "Derivation a D (b @ c @ d) " "Derivation c E c'"
  shows "\<exists>F. Derivation a F (b @ c' @ d)"
  using assms Derivation_append' Derivation_prepend Derivation_implies_append by fast

lemma derives1_if_valid_rule:
  "(N, \<alpha>) \<in> set \<RR> \<Longrightarrow> derives1 [N] \<alpha>"
  unfolding derives1_def
  apply (rule_tac exI[where x="[]"])
  apply (rule_tac exI[where x="[]"])
  by simp

lemma derives_if_valid_rule:
  "(N, \<alpha>) \<in> set \<RR> \<Longrightarrow> derives [N] \<alpha>"
  using derives1_if_valid_rule by simp

lemma Derivation_from_empty:
  "Derivation [] D a \<Longrightarrow> a = []"
  by (cases D) (auto simp: Derives1_def)

lemma Derivation_concat_split:
  "Derivation (a@b) D c \<Longrightarrow> \<exists>E F a' b'. Derivation a E a' \<and> Derivation b F b' \<and>
     c = a' @ b' \<and> length E \<le> length D \<and> length F \<le> length D"
proof (induction D arbitrary: a b)
  case Nil
  thus ?case
    by (metis local.Derivation.simps(1) order_refl)
next
  case (Cons d D)
  then obtain ab where *: "Derives1 (a@b) (fst d) (snd d) ab" "Derivation ab D c"
    by auto
  then obtain x y N \<alpha> where #:
    "a@b = x @ [N] @ y" "ab = x @ \<alpha> @ y" "(N,\<alpha>) \<in> set \<RR>" "snd d = (N,\<alpha>)" "fst d = length x"
    using * unfolding Derives1_def by blast
  show ?case
  proof (cases "length a \<le> length x")
    case True
    hence ab_def: 
      "a = take (length a) x" 
      "b = drop (length a) x @ [N] @ y"
      "ab = take (length a) x @ drop (length a) x @ \<alpha> @ y"
      using #(1,2) True by (metis append_eq_append_conv_if)+
    then obtain E F a' b' where IH:
      "Derivation (take (length a) x) E a'"
      "Derivation (drop (length a) x @ \<alpha> @ y) F b'"
      "c = a' @ b'"
      "length E \<le> length D"
      "length F \<le> length D"
      using Cons *(2) by blast
    have "Derives1 b (fst d - length a) (snd d) (drop (length a) x @ \<alpha> @ y)"
      unfolding Derives1_def using *(1) #(3-5) ab_def(2) by (metis length_drop)
    hence "Derivation b ((fst d - length a, snd d) # F) b'"
      using IH(2) by force
    moreover have "Derivation a E a'"
      using IH(1) ab_def(1) by fastforce
    ultimately show ?thesis
      using IH(3-5) by fastforce
  next
    case False
    hence a_def: "a = x @ [N] @ take (length a - length x - 1) y"
      using #(1) append_eq_conv_conj[of a b "x @ [N] @ y"] take_all_iff take_append
      by (metis append_Cons append_Nil diff_is_0_eq le_cases take_Cons')
    hence b_def: "b = drop (length a - length x - 1) y"
      using #(1) by (metis List.append.assoc append_take_drop_id same_append_eq)
    have "ab = x @ \<alpha> @ take (length a - length x - 1) y @ drop (length a - length x - 1) y"
      using #(2) by force
    then obtain E F a' b' where IH:
      "Derivation (x @ \<alpha> @ take (length a - length x - 1) y) E a'"
      "Derivation (drop (length a - length x - 1) y) F b'"
      "c = a' @ b'"
      "length E \<le> length D"
      "length F \<le> length D"
      using Cons.IH[of "x @ \<alpha> @ take (length a - length x - 1) y" "drop (length a - length x - 1) y"] *(2) by auto
    have "Derives1 a (fst d) (snd d) (x @ \<alpha> @ take (length a - length x - 1) y)"
      unfolding Derives1_def using #(3-5) a_def by blast
    hence "Derivation a ((fst d, snd d) # E) a'"
      using IH(1) by fastforce
    moreover have "Derivation b F b'"
      using b_def IH(2) by blast
    ultimately show ?thesis
      using IH(3-5) by fastforce
  qed
qed


end

section \<open>Earley recognizer\<close>

subsection \<open>Earley items\<close>

definition rule_head :: "'a rule \<Rightarrow> 'a" where
  "rule_head = fst"

definition rule_body :: "'a rule \<Rightarrow> 'a list" where
  "rule_body = snd"

datatype 'a item = 
  Item 
    (item_rule: "'a rule") 
    (item_dot : nat) 
    (item_origin : nat)
    (item_end : nat)

type_synonym 'a items = "'a item set"

definition item_rule_head :: "'a item \<Rightarrow> 'a" where
  "item_rule_head x = rule_head (item_rule x)"

definition item_rule_body :: "'a item \<Rightarrow> 'a sentence" where
  "item_rule_body x = rule_body (item_rule x)"

definition item_\<alpha> :: "'a item \<Rightarrow> 'a sentence" where
  "item_\<alpha> x = take (item_dot x) (item_rule_body x)"

definition item_\<beta> :: "'a item \<Rightarrow> 'a sentence" where 
  "item_\<beta> x = drop (item_dot x) (item_rule_body x)"

definition init_item :: "'a rule \<Rightarrow> nat \<Rightarrow> 'a item" where
  "init_item r k = Item r 0 k k"

definition is_complete :: "'a item \<Rightarrow> bool" where
  "is_complete x = (item_dot x \<ge> length (item_rule_body x))"

definition next_symbol :: "'a item \<Rightarrow> 'a option" where
  "next_symbol x = (if is_complete x then None else Some ((item_rule_body x) ! (item_dot x)))"

definition inc_item :: "'a item \<Rightarrow> nat \<Rightarrow> 'a item" where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

lemmas item_defs = item_rule_head_def item_rule_body_def item_\<alpha>_def item_\<beta>_def rule_head_def rule_body_def

definition bin :: "'a items \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"

definition wf_item :: "'a rules \<Rightarrow> 'a list => 'a item \<Rightarrow> bool" where 
  "wf_item \<RR> inp x = (
    item_rule x \<in> set \<RR> \<and> 
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length inp)"

definition wf_items :: "'a rules \<Rightarrow> 'a list \<Rightarrow> 'a items \<Rightarrow> bool" where
  "wf_items \<RR> inp I = (\<forall>x \<in> I. wf_item \<RR> inp x)"

subsection \<open>Epsilon Productions\<close>

context CFG
begin

definition \<epsilon>_free :: "bool" where
  "\<epsilon>_free = (\<forall>r \<in> set \<RR>. rule_body r \<noteq> [])"

lemma \<epsilon>_free_impl_non_empty_sentence_deriv:
  "\<epsilon>_free \<Longrightarrow> a \<noteq> [] \<Longrightarrow> \<not> Derivation a D []"
proof (induction "length D" arbitrary: a D rule: nat_less_induct)
  case 1
  show ?case
  proof (rule ccontr)
    assume assm: "\<not> \<not> Derivation a D []"
    show False
    proof (cases "D = []")
      case True
      then show ?thesis
        using "1.prems"(2) assm by auto
    next
      case False
      then obtain d D' \<alpha> where *:
        "D = d # D'" "Derives1 a (fst d) (snd d) \<alpha>" "Derivation \<alpha> D' []" "snd d \<in> set \<RR>"
        using list.exhaust assm Derives1_def by (metis local.Derivation.simps(2))
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
  "\<epsilon>_free \<Longrightarrow> N \<in> set \<NN> \<Longrightarrow> \<not> derives [N] []"
  using \<epsilon>_free_impl_non_empty_sentence_deriv derives_implies_Derivation is_nonterminal_def by (meson not_Cons_self2)

end

subsection \<open>Earley algorithm\<close>

locale Earley_Set = CFG +
  fixes inp :: "'a list"
begin

definition Init :: "'a items" where
  "Init = { init_item r 0 | r. r \<in> set \<RR> \<and> fst r = \<SS> }"

definition Scan :: "nat \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Scan k I = 
    { inc_item x (k+1) | x a.
        x \<in> bin I k \<and>
        inp!k = a \<and>
        k < length inp \<and>
        next_symbol x = Some a }"

definition Predict :: "nat \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Predict k I =
    { init_item r k | r x.
        r \<in> set \<RR> \<and>
        x \<in> bin I k \<and>
        next_symbol x = Some (rule_head r) }"

definition Complete :: "nat \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Complete k I =
    { inc_item x k | x y.
        x \<in> bin I (item_origin y) \<and>
        y \<in> bin I k \<and>
        is_complete y \<and>
        next_symbol x = Some (item_rule_head y) }"

definition \<pi>_step :: "nat \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "\<pi>_step k I = I \<union> Scan k I \<union> Complete k I \<union> Predict k I"

definition \<pi> :: "nat \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "\<pi> k I = limit (\<pi>_step k) I"

fun \<I> :: "nat \<Rightarrow> 'a items" where
  "\<I> 0 = \<pi> 0 Init"
| "\<I> (Suc n) = \<pi> (Suc n) (\<I> n)"

definition \<II> :: "'a items" where
  "\<II> = \<I> (length inp)"

definition is_finished :: "'a item \<Rightarrow> bool" where
  "is_finished x \<longleftrightarrow> (
    item_rule_head x = \<SS> \<and>
    item_origin x = 0 \<and>
    item_end x = length inp \<and> 
    is_complete x)"

definition earley_recognized :: "bool" where
  "earley_recognized = (\<exists>x \<in> \<II>. is_finished x)"

subsection \<open>Wellformedness\<close>

lemma wf_items_Un:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp J \<Longrightarrow> wf_items \<RR> inp (I \<union> J)"
  unfolding wf_items_def by blast

lemmas wf_defs = wf_item_def wf_items_def

lemma wf_Init:
  "x \<in> Init \<Longrightarrow> wf_item \<RR> inp x"
  unfolding Init_def wf_item_def init_item_def by auto

lemma wf_Scan:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (Scan k I)"
  unfolding Scan_def wf_defs bin_def inc_item_def is_complete_def item_rule_body_def next_symbol_def
  by (auto split: if_splits)

lemma wf_Predict:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (Predict k I)"
  unfolding Predict_def wf_defs bin_def init_item_def by auto

lemma wf_Complete:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (Complete k I)"
  unfolding Complete_def wf_defs bin_def inc_item_def is_complete_def item_rule_body_def next_symbol_def
  by (auto split: if_splits; metis le_trans)

lemma wf_\<pi>_step:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (\<pi>_step k I)"
  unfolding \<pi>_step_def using wf_Scan wf_Predict wf_Complete wf_items_Un by simp

lemma wf_funpower:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (funpower (\<pi>_step k) n I)"
  using wf_\<pi>_step unfolding wf_items_def
  by (induction n) auto

lemma wf_\<pi>:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (\<pi> k I)"
  by (metis \<pi>_def elem_limit_simp wf_funpower wf_items_def)

lemma wf_\<pi>0:
  "wf_items \<RR> inp (\<pi> 0 Init)"
  using wf_items_def wf_Init wf_\<pi> by blast

lemma wf_\<I>:
  "wf_items \<RR> inp (\<I> n)"
  by (induction n) (auto simp: wf_\<pi>0 wf_\<pi>)

lemma wf_\<II>:
  "wf_items \<RR> inp \<II>"
  unfolding \<II>_def using wf_\<I> by blast

subsection \<open>Soundness\<close>

definition sound_item :: "'a item \<Rightarrow> bool" where
  "sound_item x = derives [item_rule_head x] (slice (item_origin x) (item_end x) inp @ item_\<beta> x)"

definition sound_items :: "'a items \<Rightarrow> bool" where
  "sound_items I = (\<forall>x \<in> I. sound_item x)"

lemmas sound_defs = sound_items_def sound_item_def

lemma sound_Init:
  "sound_items Init"
  unfolding sound_items_def
proof (standard)
  fix x
  assume *: "x \<in> Init"
  hence "item_dot x = 0"
    using Init_def by (auto, simp add: init_item_def)
  hence "(item_rule_head x, item_\<beta> x) \<in> set \<RR>"
    unfolding item_rule_head_def rule_head_def item_\<beta>_def item_rule_body_def rule_body_def
    using * wf_Init wf_item_def by auto
  hence "derives [item_rule_head x] (item_\<beta> x)"
    using derives_if_valid_rule by blast
  moreover have "item_origin x = item_end x"
    using * Init_def by (auto, simp add: init_item_def)
  ultimately show "sound_item x"
    unfolding sound_item_def by (simp add: slice_empty)
qed

lemma sound_item_inc_item:
  assumes "wf_item \<RR> inp x" "sound_item x"
  assumes "next_symbol x = Some a"
  assumes "k < length inp" "inp!k = a" "item_end x = k"
  shows "sound_item (inc_item x (k+1))"
proof -
  define x' where [simp]: "x' = inc_item x (k+1)"
  obtain item_\<beta>' where *: "item_\<beta> x = a # item_\<beta>'"
    using assms(3) apply (auto simp: item_\<beta>_def is_complete_def next_symbol_def split: if_splits)
    by (metis Cons_nth_drop_Suc leI)
  have "slice (item_origin x) (item_end x) inp @ item_\<beta> x = slice (item_origin x') (item_end x') inp @ item_\<beta>'"
    using * assms(1,4-6) slice_append_nth wf_item_def by (auto simp: inc_item_def; blast)
  moreover have "item_\<beta>' = item_\<beta> x'"
    using * by (auto simp: inc_item_def item_\<beta>_def item_rule_body_def, metis List.list.sel(3) drop_Suc tl_drop)
  moreover have "derives [item_rule_head x] (slice (item_origin x) (item_end x) inp @ item_\<beta> x)"
    using assms(1,2,6) sound_item_def by blast
  ultimately show ?thesis
    by (simp add: inc_item_def item_rule_head_def sound_item_def)
qed

lemma sound_Scan:
  "wf_items \<RR> inp I \<Longrightarrow> sound_items I \<Longrightarrow> sound_items (Scan k I)"
  unfolding Scan_def using sound_item_inc_item by (auto simp: wf_items_def sound_items_def bin_def)

lemma sound_Predict:
  "sound_items I \<Longrightarrow> sound_items (Predict k I)"
  unfolding Predict_def by (auto simp: sound_defs init_item_def derives_if_valid_rule slice_empty item_defs)

lemma sound_Complete:
  assumes "wf_items \<RR> inp I" "sound_items I"
  shows "sound_items (Complete k I)"
  unfolding sound_items_def
proof standard
  fix z
  assume "z \<in> Complete k I"
  show "sound_item z"
  proof cases
    assume "z \<in> I"
    thus ?thesis
      using assms unfolding sound_items_def by blast
  next
    assume "\<not> z \<in> I"
    then obtain x y where *:
      "z = inc_item x k" "x \<in> bin I (item_origin y)" "y \<in> bin I k" 
      "is_complete y" "next_symbol x = Some (item_rule_head y)"
      using \<open>z \<in> Complete k I\<close> unfolding Complete_def by blast

    have "derives [item_rule_head y] (slice (item_origin y) (item_end y) inp)"
      using *(3,4) sound_defs assms by (auto simp: bin_def is_complete_def item_\<beta>_def)
    then obtain E where E: "Derivation [item_rule_head y] E (slice (item_origin y) (item_end y) inp)"
      using derives_implies_Derivation by blast

    have "derives [item_rule_head x] (slice (item_origin x) (item_origin y) inp @ item_\<beta> x)"
      using *(2) sound_defs assms sound_items_def by (auto simp: bin_def)
    moreover have 0: "item_\<beta> x = (item_rule_head y) # tl (item_\<beta> x)"
      using *(5) by (auto simp: next_symbol_def item_\<beta>_def is_complete_def split: if_splits,
                     metis Cons_nth_drop_Suc drop_Suc drop_tl leI)
    ultimately obtain D where D: 
      "Derivation [item_rule_head x] D (slice (item_origin x) (item_origin y) inp @
       [item_rule_head y] @ (tl (item_\<beta> x)))"
      using derives_implies_Derivation by (metis append_Cons append_Nil)

    have "wf_item \<RR> inp x"
      using *(2) assms(1) bin_def wf_items_def by (metis (mono_tags, lifting) mem_Collect_eq)
    obtain G where 
      "Derivation [item_rule_head x] G (slice (item_origin x) (item_origin y) inp @
       slice (item_origin y) (item_end y) inp @ tl (item_\<beta> x))"
      using Derivation_append_rewrite D E by blast
    moreover have "item_origin x \<le> item_origin y"
      using *(2) \<open>wf_item \<RR> inp x\<close> wf_item_def by (auto simp: bin_def; force)
    moreover have "item_origin y \<le> item_end y"
      using *(3) wf_defs assms(1) by (auto simp: bin_def; blast)
    ultimately have "derives [item_rule_head x] (slice (item_origin x) (item_end y) inp @ tl (item_\<beta> x))"
      by (metis Derivation_implies_derives append.assoc slice_concat)
    moreover have "tl (item_\<beta> x) = item_\<beta> z"
      using *(1,5) 0 by (auto simp: inc_item_def item_rule_body_def tl_drop drop_Suc item_\<beta>_def)
    ultimately show ?thesis
      using sound_item_def *(1,3) by (auto simp: bin_def inc_item_def item_rule_head_def)
  qed
qed

lemma sound_\<pi>_step:
  "wf_items \<RR> inp I \<Longrightarrow> sound_items I \<Longrightarrow> sound_items (\<pi>_step k I)"
  unfolding \<pi>_step_def using sound_Scan sound_Predict sound_Complete by (metis UnE sound_items_def)

lemma sound_funpower:
  "wf_items \<RR> inp I \<Longrightarrow> sound_items I \<Longrightarrow> sound_items (funpower (\<pi>_step k) n I)"
  by (induction n) (auto simp: sound_\<pi>_step wf_\<pi>_step wf_funpower)

lemma sound_\<pi>:
  assumes "wf_items \<RR> inp I" "sound_items I"
  shows "sound_items (\<pi> k I)"
  by (metis \<pi>_def assms elem_limit_simp sound_items_def sound_funpower)

lemma sound_\<pi>0:
  "sound_items (\<pi> 0 Init)"
  using sound_items_def sound_Init sound_\<pi> wf_Init wf_items_def by metis

lemma sound_\<I>:
  "sound_items (\<I> k)"
  apply (induction k)
  apply (auto simp: sound_\<pi>0)
  using sound_\<pi> wf_\<I> by force

lemma sound_\<II>:
  "sound_items \<II>"
  unfolding \<II>_def using sound_\<I> by blast

theorem soundness:
  "earley_recognized \<Longrightarrow> derives [\<SS>] inp"
  using earley_recognized_def sound_\<II> sound_defs by (auto simp: is_complete_def is_finished_def item_\<beta>_def)

subsection \<open>Monotonicity and Absorption\<close>

lemma \<pi>_step_empty:
  "\<pi>_step k {} = {}"
  unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast

lemma \<pi>_step_setmonotone:
  "setmonotone (\<pi>_step k)"
  by (simp add: Un_assoc \<pi>_step_def setmonotone_def)

lemma \<pi>_step_continuous:
  "continuous (\<pi>_step k)"
  unfolding continuous_def
proof (standard, standard, standard)
  fix C :: "nat \<Rightarrow> 'a item set"
  assume "chain C"
  thus "chain (\<pi>_step k \<circ> C)"
    unfolding chain_def \<pi>_step_def by (auto simp: Scan_def Predict_def Complete_def bin_def subset_eq)
next
  fix C :: "nat \<Rightarrow> 'a item set"
  assume *: "chain C"
  show "\<pi>_step k (natUnion C) = natUnion (\<pi>_step k \<circ> C)"
    unfolding natUnion_def
  proof standard
    show "\<pi>_step k (\<Union> {C n |n. True}) \<subseteq> \<Union> {(\<pi>_step k \<circ> C) n |n. True}"
    proof standard
      fix x
      assume #: "x \<in> \<pi>_step k (\<Union> {C n |n. True})"
      show "x \<in> \<Union> {(\<pi>_step k \<circ> C) n |n. True}"
      proof (cases "x \<in> Complete k (\<Union> {C n |n. True})")
        case True
        then show ?thesis
          using * unfolding chain_def
          apply (auto simp: \<pi>_step_def Complete_def bin_def)
        proof -
          fix y :: "'a item" and z :: "'a item" and n :: nat and m :: nat
          assume a1: "is_complete z"
          assume a2: "item_end y = item_origin z"
          assume a3: "y \<in> C n"
          assume a4: "z \<in> C m"
          assume a5: "next_symbol y = Some (item_rule_head z)"
          assume "\<forall>i. C i \<subseteq> C (Suc i)"
          hence f6: "\<And>n m. \<not> n \<le> m \<or> C n \<subseteq> C m"
            by (meson lift_Suc_mono_le)
          hence f7: "\<And>n. \<not> m \<le> n \<or> z \<in> C n"
            using a4 by blast
          have "\<exists>n \<ge> m. y \<in> C n"
            using f6 a3 by (meson le_sup_iff subset_eq sup_ge1)
          thus "\<exists>I.
                  (\<exists>n. I = C n \<union> 
                           Scan (item_end z) (C n) \<union> 
                           {inc_item i (item_end z) |i. 
                              i \<in> C n \<and> 
                              (\<exists>j. 
                                item_end i = item_origin j \<and>
                                j \<in> C n \<and> 
                                item_end j = item_end z \<and> 
                                is_complete j \<and>
                                next_symbol i = Some (item_rule_head j))} \<union>
                           Predict (item_end z) (C n))
                  \<and> inc_item y (item_end z) \<in> I"
            using f7 a5 a2 a1 by blast
        qed
      next
        case False
        thus ?thesis
          using # Un_iff by (auto simp: \<pi>_step_def Scan_def Predict_def bin_def; blast)
      qed
    qed
  next
    show "\<Union> {(\<pi>_step k \<circ> C) n |n. True} \<subseteq> \<pi>_step k (\<Union> {C n |n. True})"
      unfolding \<pi>_step_def
      using * by (auto simp: Scan_def Predict_def Complete_def chain_def bin_def, metis+)
  qed
qed

lemma \<pi>_step_regular:
  "regular (\<pi>_step k)"
  by (simp add: \<pi>_step_continuous \<pi>_step_setmonotone regular_def)

lemma \<pi>_idem:
  "\<pi> k (\<pi> k I) = \<pi> k I"
  by (simp add: \<pi>_def \<pi>_step_regular limit_is_idempotent)

lemma Scan_bin_absorb:
  "Scan k (bin I k) = Scan k I"
  unfolding Scan_def bin_def by simp

lemma Predict_bin_absorb:
  "Predict k (bin I k) = Predict k I"
  unfolding Predict_def bin_def by simp

lemma Complete_bin_absorb:
  "Complete k (bin I k) \<subseteq> Complete k I"
  unfolding Complete_def bin_def by blast

lemma Scan_Un:
  "Scan k (I \<union> J) = Scan k I \<union> Scan k J"
  unfolding Scan_def bin_def by blast

lemma Predict_Un:
  "Predict k (I \<union> J) = Predict k I \<union> Predict k J"
  unfolding Predict_def bin_def by blast

lemma Scan_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Scan k I \<subseteq> Scan k J"
  unfolding Scan_def bin_def by blast

lemma Predict_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Predict k I \<subseteq> Predict k J"
  unfolding Predict_def bin_def by blast

lemma Complete_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Complete k I \<subseteq> Complete k J"
  unfolding Complete_def bin_def by blast

lemma \<pi>_step_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi>_step k I \<subseteq> \<pi>_step k J"
  unfolding \<pi>_step_def using Scan_sub_mono Predict_sub_mono Complete_sub_mono by (meson Un_mono)

lemma funpower_sub_mono:
  "I \<subseteq> J \<Longrightarrow> funpower (\<pi>_step k) n I \<subseteq> funpower (\<pi>_step k) n J"
  by (induction n) (auto simp: \<pi>_step_sub_mono)

lemma \<pi>_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi> k I \<subseteq> \<pi> k J"
proof standard
  fix x
  assume "I \<subseteq> J" "x \<in> \<pi> k I"
  then obtain n where "x \<in> funpower (\<pi>_step k) n I"
    unfolding \<pi>_def limit_def natUnion_def by blast
  hence "x \<in> funpower (\<pi>_step k) n J"
    using \<open>I \<subseteq> J\<close> funpower_sub_mono by blast
  thus "x \<in> \<pi> k J"
    unfolding \<pi>_def limit_def natUnion_def by blast
qed

lemma Scan_\<pi>_step_mono:
  "Scan k I \<subseteq> \<pi>_step k I"
  using \<pi>_step_def by auto

lemma Predict_\<pi>_step_mono:
  "Predict k I \<subseteq> \<pi>_step k I"
  using \<pi>_step_def by auto

lemma Complete_\<pi>_step_mono:
  "Complete k I \<subseteq> \<pi>_step k I"
  using \<pi>_step_def by auto

lemma \<pi>_step_\<pi>_mono:
  "\<pi>_step k I \<subseteq> \<pi> k I"
proof -
  have "\<pi>_step k I \<subseteq> funpower (\<pi>_step k) 1 I"
    by simp
  thus ?thesis
    by (metis \<pi>_def limit_elem subset_eq)
qed

lemma Scan_\<pi>_mono:
  "Scan k I \<subseteq> \<pi> k I"
  using Scan_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma Predict_\<pi>_mono:
  "Predict k I \<subseteq> \<pi> k I"
  using Predict_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma Complete_\<pi>_mono:
  "Complete k I \<subseteq> \<pi> k I"
  using Complete_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma \<pi>_mono:
  "I \<subseteq> \<pi> k I"
  using \<pi>_step_\<pi>_mono \<pi>_step_def by auto

lemma Scan_bin_empty:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Scan k I) i = {}"
  unfolding Scan_def bin_def inc_item_def by fastforce

lemma Predict_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Predict k I) i = {}"
  unfolding Predict_def bin_def init_item_def by auto

lemma Complete_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Complete k I) i = {}"
  unfolding Complete_def bin_def inc_item_def by auto

lemma \<pi>_step_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k + 1 \<Longrightarrow> bin (\<pi>_step k I) i = bin I i"
  unfolding \<pi>_step_def using Scan_bin_empty Predict_bin_empty Complete_bin_empty
  unfolding bin_def using Un_iff empty_iff mem_Collect_eq by fastforce

lemma funpower_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (funpower (\<pi>_step k) n I) i = bin I i"
  by (induction n) (auto simp: \<pi>_step_bin_absorb)

lemma \<pi>_bin_absorb:
  assumes "i \<noteq> k" "i \<noteq> k+1" 
  shows "bin (\<pi> k I) i = bin I i"
proof (standard; standard)
  fix x 
  assume "x \<in> bin (\<pi> k I) i"
  then obtain n where "x \<in> bin (funpower (\<pi>_step k) n I) i"
    unfolding \<pi>_def limit_def natUnion_def by (auto simp: bin_def)
  then show "x \<in> bin I i"
    using funpower_bin_absorb assms by blast
next
  fix x
  assume "x \<in> bin I i"
  show "x \<in> bin (\<pi> k I) i"
    using \<pi>_mono \<open>x \<in> bin I i\<close> by (auto simp: bin_def)
qed

subsection \<open>Completeness\<close>

lemma Scan_\<I>:
  assumes "i+1 \<le> k" "k \<le> length inp" "x \<in> bin (\<I> k) i" "next_symbol x = Some a" "inp!i = a"
  shows "inc_item x (i+1) \<in> \<I> k"
  using assms
proof (induction k arbitrary: i x a)
  case (Suc k)
  show ?case
  proof cases
    assume "i+1 \<le> k"
    hence "inc_item x (i+1) \<in> \<I> k"
      using Suc \<pi>_bin_absorb by simp
    thus ?thesis
      using \<pi>_mono unfolding Scan_def by force
  next
    assume "\<not> i+1 \<le> k"
    hence *: "i+1 = Suc k"
      using le_Suc_eq Suc.prems(1) by blast
    have "x \<in> bin (\<I> k) i"
      using Suc.prems(3) * \<pi>_bin_absorb by force
    hence "inc_item x (i+1) \<in> \<pi> i (\<I> k)"
      using * Suc.prems(2,4,5) Scan_\<pi>_mono unfolding Scan_def by force
    hence "inc_item x (i+1) \<in> \<pi> k (\<I> k)"
      using * by force
    hence "inc_item x (i+1) \<in> \<I> k"
      using \<pi>_idem by (metis local.\<I>.elims)
    thus ?thesis
      using \<pi>_mono by auto
  qed
qed simp

lemma Predict_\<I>:
  assumes "i \<le> k" "x \<in> bin (\<I> k) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set \<RR>"
  shows "init_item (N,\<alpha>) i \<in> \<I> k"
  using assms
proof (induction k arbitrary: i x N \<alpha>)
  case 0
  hence "init_item (N,\<alpha>) i \<in> Predict 0 (\<I> 0)"
    unfolding rule_head_def Predict_def by auto
  thus ?case
    using Predict_\<pi>_mono \<pi>_idem by fastforce
next
  case (Suc k)
  show ?case
  proof cases
    assume "i \<le> k"
    hence "init_item (N,\<alpha>) i \<in> \<I> k"
      using Suc.IH \<pi>_bin_absorb Suc.prems(2-4) by force
    thus ?thesis
      using \<pi>_mono by auto
  next
    assume "\<not> i \<le> k"
    hence "init_item (N,\<alpha>) i \<in> Predict i (\<I> (Suc k))"
      unfolding Predict_def rule_head_def using Suc.prems(2-4) by auto
    thus ?thesis
      using Predict_\<pi>_mono \<pi>_idem Suc.prems(1) \<open>\<not> i \<le> k\<close> by (metis le_SucE \<I>.simps(2) subsetD)
  qed
qed

lemma Complete_\<I>:
  assumes "i \<le> j" "j \<le> k" "x \<in> bin (\<I> k) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set \<RR>"
  assumes "i = item_origin y" "y \<in> bin (\<I> k) j" "item_rule y = (N,\<alpha>)" "is_complete y"
  shows "inc_item x j \<in> \<I> k"
  using assms
proof (induction k arbitrary: i j x N \<alpha> y)
  case 0
  hence "inc_item x 0 \<in> Complete 0 (\<I> 0)"
    unfolding Complete_def rule_head_def next_symbol_def item_rule_head_def by (auto split: if_splits; force)
  thus ?case
    using Complete_\<pi>_mono \<pi>_idem "0.prems"(2) by (metis le_0_eq \<I>.simps(1) subset_iff)
next
  case (Suc k)
  show ?case
  proof cases
    assume "j \<le> k"
    hence "inc_item x j \<in> \<I> k"
      using Suc  \<pi>_bin_absorb Orderings.order_class.dual_order.eq_iff by force
    thus ?thesis
      using \<pi>_mono by fastforce
  next
    assume "\<not> j \<le> k"
    hence "j = Suc k"
      using le_SucE Suc.prems(2) by blast
    hence "inc_item x (Suc k) \<in> Complete (Suc k) (\<I> (Suc k))"
      using Suc.prems(3-4,6-9) unfolding Complete_def rule_head_def item_rule_head_def by fastforce
    then show ?thesis
      using Complete_\<pi>_mono \<pi>_idem \<open>j = Suc k\<close> by fastforce
  qed
qed

definition partially_complete :: "nat \<Rightarrow> 'a items \<Rightarrow> ('a derivation \<Rightarrow> bool) \<Rightarrow> bool" where
  "partially_complete k I P = (
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length inp \<and>
      x \<in> bin I i \<and> next_symbol x = Some a \<and>
      Derivation [a] D (slice i j inp) \<and> P D \<longrightarrow>
      inc_item x j \<in> I
  )"

lemma fully_complete:
  assumes "j \<le> k" "k \<le> length inp"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> I" "wf_items \<RR> inp I"
  assumes "Derivation (item_\<beta> x) D (slice j k inp)"
  assumes "partially_complete k I (\<lambda>D'. length D' \<le> length D)"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> I"
  using assms
proof (induction "item_\<beta> x" arbitrary: d i j k N \<alpha> x D)
  case Nil
  have "item_\<alpha> x = \<alpha>"
    using Nil(1,4) unfolding item_\<alpha>_def item_\<beta>_def item_rule_body_def rule_body_def by simp
  hence "x = Item (N,\<alpha>) (length \<alpha>) i j"
    using Nil.hyps Nil.prems(3,4,5)
    unfolding wf_items_def wf_item_def rule_body_def item_rule_body_def item_defs(4) by auto
  have "Derivation [] D (slice j k inp)"
    using Nil.hyps Nil.prems(6) by simp
  hence "slice j k inp = []"
    using Derivation_from_empty by blast
  hence "j = k"
    unfolding slice_drop_take using Nil.prems(1,2) by simp
  thus ?case
    using \<open>x = Item (N, \<alpha>) (length \<alpha>) i j\<close> Nil.prems(4) by blast
next
  case (Cons b bs)
  then obtain j' E F where *: 
    "Derivation [b] E (slice j j' inp)"
    "Derivation bs F (slice j' k inp)"
    "j \<le> j'" "j' \<le> k" "length E \<le> length D" "length F \<le> length D"
    using Derivation_concat_split[of "[b]" bs D "slice j k inp"] slice_concat_Ex
    by (metis append_Cons append_Nil Cons.prems(1))
  have "x \<in> bin I j"
    using Cons.prems(3,4) by (auto simp: bin_def)
  moreover have "next_symbol x = Some b"
    using Cons unfolding item_defs(4) next_symbol_def is_complete_def by (auto, metis nth_via_drop)
  ultimately have "inc_item x j' \<in> I"
    using *(1,3-5) Cons.prems(2-4,7) partially_complete_def by metis
  moreover have "partially_complete k I (\<lambda>D'. length D' \<le> length F)"
    using Cons.prems(7) *(6) unfolding partially_complete_def by fastforce
  moreover have "bs = item_\<beta> (Item (N,\<alpha>) (d+1) i j')"
    using Cons.hyps(2) Cons.prems(3) unfolding item_defs(4) item_rule_body_def 
    by (auto, metis List.list.sel(3) drop_Suc drop_tl)
  ultimately show ?case
    using Cons.hyps(1) *(2,4) Cons.prems(2,3,5) wf_items_def by (auto simp: inc_item_def)
qed

lemma partially_complete_\<I>:
  "partially_complete k (\<I> k) (\<lambda>_. True)"
  unfolding partially_complete_def
proof (standard, standard, standard, standard, standard, standard)
  fix x i a D j
  assume
    "i \<le> j \<and> j \<le> k \<and> k \<le> length inp \<and>
     x \<in> bin (\<I> k) i \<and> next_symbol x = Some a \<and>
     Derivation [a] D (slice i j inp) \<and> (\<lambda>_. True) D"
  thus "inc_item x j \<in> \<I> k"
  proof (induction "length D" arbitrary: x i a j D rule: nat_less_induct)
    case 1
    show ?case
    proof cases
      assume "D = []"
      hence "[a] = slice i j inp"
        using "1.prems" by force
      moreover have "j \<le> length inp"
        using le_trans "1.prems" by blast
      ultimately have "j = i+1"
        using slice_singleton by metis
      hence "i < length inp"
        using \<open>j \<le> length inp\<close> discrete by blast
      hence "inp!i = a"
        using slice_nth \<open>[a] = slice i j inp\<close> \<open>j = i + 1\<close> by fastforce
      hence "inc_item x (i+1) \<in> \<I> k"
        using Scan_\<I> \<open>j = i + 1\<close> "1.prems" by blast
      thus ?thesis
        by (simp add: \<open>j = i + 1\<close> wf_Init wf_items_def)
    next
      assume "\<not> D = []"
      then obtain d D' where "D = d # D'"
        by (meson List.list.exhaust)
      then obtain b where *: "Derives1 [a] (fst d) (snd d) b" "Derivation b D' (slice i j inp)"
        using "1.prems" by auto
      show ?thesis
      proof cases
        assume "is_terminal a"
        then obtain N \<alpha> where "[a] = [N]" "(N,\<alpha>) \<in> set \<RR>"
          using *(1) unfolding Derives1_def by (metis Cons_eq_append_conv neq_Nil_conv)
         hence "is_nonterminal a"
           by simp
         thus ?thesis
          using \<open>is_terminal a\<close> is_terminal_nonterminal by blast
      next
        assume "\<not> is_terminal a"
        then obtain N \<alpha> where #: "[a] = [N]" "b = \<alpha>" "(N,\<alpha>) \<in> set \<RR>" "fst d = 0" "snd d = (N,\<alpha>)"
          using *(1) unfolding Derives1_def by (simp add: Cons_eq_append_conv)
        define y where y_def: "y = Item (N,\<alpha>) 0 i i"
        have "init_item (N, \<alpha>) i \<in> \<I> k"
          using Predict_\<I> #(1,3) "1.prems" by auto
        hence "y \<in> bin (\<I> k) i"
          unfolding init_item_def using y_def by (simp add: bin_def wf_Init wf_items_def)
        have "length D' < length D"
          using \<open>D = d # D'\<close> by fastforce
        hence "partially_complete k (\<I> k) (\<lambda>E. length E \<le> length D')"
          unfolding partially_complete_def using "1.hyps" "1.prems" le_less_trans by blast
        hence "partially_complete j (\<I> k) (\<lambda>E. length E \<le> length D')"
          unfolding partially_complete_def using "1.prems" by force
        moreover have "Derivation (item_\<beta> y) D' (slice i j inp)"
          using #(2) *(2) item_\<beta>_def item_rule_body_def rule_body_def y_def
          by (metis item.sel(1) item.sel(2) drop0 snd_conv)
        ultimately have 0: "Item (N,\<alpha>) (length \<alpha>) i j \<in> bin (\<I> k) j"
          using fully_complete wf_\<I> "1.prems" wf_items_def \<open>y \<in> bin (\<I> k) i\<close> by (auto simp: bin_def y_def)
        have 1: "x \<in> bin (\<I> k) i"
          by (simp add: "1.prems")
        have "next_symbol x = Some N"
          using #(1) "1.prems" by fastforce
        thus ?thesis
          using "1.prems" Complete_\<I>[OF _ _ 1 _ _ _ 0] #(3) by (auto simp: is_complete_def item_rule_body_def rule_body_def)
      qed
    qed
  qed
qed

lemma partially_complete_\<II>:
  "partially_complete (length inp) \<II> (\<lambda>_. True)"
  by (simp add: \<II>_def partially_complete_\<I>)

lemma Init_sub_\<I>:
  "Init \<subseteq> \<I> k"
  using \<pi>_mono by (induction k) auto

lemma Derivation_\<SS>1:
  assumes "Derivation [\<SS>] D inp" "set inp \<subseteq> set \<TT>"
  shows "\<exists>\<alpha> E. Derivation \<alpha> E inp \<and> (\<SS>,\<alpha>) \<in> set \<RR>"
proof (cases D)
  case Nil
  thus ?thesis
    using assms is_nonterminal_startsymbol is_terminal_def is_terminal_nonterminal by fastforce
next
  case (Cons d D)
  then obtain \<alpha> where "Derives1 [\<SS>] (fst d) (snd d) \<alpha>" "Derivation \<alpha> D inp"
    using assms by auto
  hence "(\<SS>, \<alpha>) \<in> set \<RR>"
    unfolding Derives1_def
    by (metis List.append.right_neutral List.list.discI append_eq_Cons_conv append_is_Nil_conv nth_Cons_0 self_append_conv2)
  thus ?thesis
    using \<open>Derivation \<alpha> D inp\<close> by auto
qed

theorem completeness:
  assumes "derives [\<SS>] inp" "set inp \<subseteq> set \<TT>"
  shows "earley_recognized"
proof -
  obtain \<alpha> where *: "(\<SS>,\<alpha>) \<in> set \<RR>" "derives \<alpha> inp"
    using Derivation_\<SS>1 assms Derivation_implies_derives derives_implies_Derivation by blast
  let ?x = "Item (\<SS>,\<alpha>) 0 0 0"
  have "?x \<in> \<II>" "wf_item \<RR> inp ?x"
    unfolding \<II>_def using *(1) Init_sub_\<I> Init_def wf_Init by (auto simp: init_item_def)
  moreover have "derives (item_\<beta> ?x) (slice 0 (length inp) inp)"
    using *(2) item_defs(4) by (simp add: item_\<beta>_def item_rule_body_def rule_body_def)
  ultimately have "Item (\<SS>,\<alpha>) (length \<alpha>) 0 (length inp) \<in> \<II>"
    using partially_complete_\<II> fully_complete unfolding partially_complete_def 
    using fully_complete wf_\<II> derives_implies_Derivation
    by (auto, metis Earley_Set.item.sel(4) le_refl slice_id wf_defs(1))
  then show ?thesis
    unfolding earley_recognized_def is_finished_def by (auto simp: is_complete_def item_defs, force)
qed

subsection \<open>Correctness\<close>

corollary correctness:
  assumes "set inp \<subseteq> set \<TT>"
  shows "earley_recognized \<longleftrightarrow> derives [\<SS>] inp"
  using assms soundness completeness by blast

subsection \<open>Finiteness\<close>

lemma finiteness_empty:
  "set \<RR> = {} \<Longrightarrow> finite { x | x. wf_item \<RR> inp x }"
  unfolding wf_item_def by simp

fun f :: "'a rule \<times> nat \<times> nat \<times> nat \<Rightarrow> 'a item" where
  "f (rule, dot, origin, ends) = Item rule dot origin ends" 

lemma finiteness_nonempty:
  assumes "set \<RR> \<noteq> {}"
  shows "finite { x | x. wf_item \<RR> inp x }"
proof -
  define M where "M = Max { length (rule_body r) | r. r \<in> set \<RR> }"
  define Top where "Top = (set \<RR> \<times> {0..M} \<times> {0..length inp} \<times> {0..length inp})"
  hence "finite Top"
    using finite_cartesian_product finite by blast
  have "inj_on f Top"
    unfolding Top_def inj_on_def by simp
  hence "finite (f ` Top)"
    using finite_image_iff \<open>finite Top\<close> by auto
  have "{ x | x. wf_item \<RR> inp x } \<subseteq> f ` Top"
  proof standard
    fix x
    assume "x \<in> { x | x. wf_item \<RR> inp x }"
    then obtain rule dot origin endp where *: "x = Item rule dot origin endp"
      "rule \<in> set \<RR>" "dot \<le> length (item_rule_body x)" "origin \<le> length inp" "endp \<le> length inp"
      unfolding wf_item_def using item.exhaust_sel le_trans by blast
    hence "length (rule_body rule) \<in> { length (rule_body r) | r. r \<in> set \<RR> }"
      using *(1,2) item_rule_body_def by blast
    moreover have "finite { length (rule_body r) | r. r \<in> set \<RR> }"
      using finite finite_image_set[of "\<lambda>x. x \<in> set \<RR>"] by fastforce
    ultimately have "M \<ge> length (rule_body rule)"
      unfolding M_def by simp
    hence "dot \<le> M"
      using *(1,3) item_rule_body_def by (metis item.sel(1) le_trans)
    hence "(rule, dot, origin, endp) \<in> Top"
      using *(2,4,5) unfolding Top_def by simp
    thus "x \<in> f ` Top"
      using *(1) by force
  qed
  thus ?thesis
    using \<open>finite (f ` Top)\<close> rev_finite_subset by auto
qed

lemma finiteness_UNIV_wf_item:
  "finite { x | x. wf_item \<RR> inp x }"
  using finiteness_empty finiteness_nonempty by fastforce

theorem finiteness:
  "finite \<II>"
  using finiteness_UNIV_wf_item wf_items_def wf_\<II> rev_finite_subset by (metis mem_Collect_eq subsetI)

end

end
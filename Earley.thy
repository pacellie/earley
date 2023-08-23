theory Earley
  imports
    Derivations
begin

section \<open>Slices\<close>

fun slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "slice [] _ _ = []"
| "slice _ _ 0 = []"
| "slice (x#xs) 0 (Suc b) = x # slice xs 0 b"
| "slice (x#xs) (Suc a) (Suc b) = slice xs a b"

syntax
  "slice" :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" ("_\<lbrakk>_.._\<rparr>" [1000,0,0] 1000)

lemma slice_drop_take:
  "xs\<lbrakk>a..b\<rparr> = drop a (take b xs)"
  by (induction xs a b rule: slice.induct) auto

lemma slice_append_aux:
  "Suc b \<le> c \<Longrightarrow> (x#xs)\<lbrakk>Suc b..c\<rparr> = xs\<lbrakk>b..c-1\<rparr>"
  using Suc_le_D by fastforce

lemma slice_concat:
  "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> xs\<lbrakk>a.. b\<rparr> @ xs\<lbrakk>b..c\<rparr> = xs\<lbrakk>a..c\<rparr>"
  apply (induction xs a b arbitrary: c rule: slice.induct)
     apply (auto simp: slice_append_aux)
  using Suc_le_D by fastforce

lemma slice_concat_Ex:
  "a \<le> c \<Longrightarrow> xs\<lbrakk>a..c\<rparr> = ys @ zs \<Longrightarrow> \<exists>b. ys = xs\<lbrakk>a..b\<rparr> \<and> zs = xs\<lbrakk>b..c\<rparr> \<and> a \<le> b \<and> b \<le> c"
proof (induction xs a c arbitrary: ys zs rule: slice.induct)
  case (3 x xs b)
  show ?case
  proof (cases ys)
    case Nil
    then obtain zs' where "x # xs\<lbrakk>0..b\<rparr> = x # zs'" "x # zs' = zs"
      using "3.prems"(2) by auto
    thus ?thesis
      using Nil by force
  next
    case (Cons y ys')
    then obtain ys' where "x # xs\<lbrakk>0..b\<rparr> = x # ys' @ zs" "x # ys' = ys"
      using "3.prems"(2) by auto
    thus ?thesis
      using "3.IH"[of ys' zs] by force
  qed
next
  case (4 a b x xs)
  thus ?case
    by (auto, metis slice.simps(4) Suc_le_mono)
qed auto

lemma slice_nth:
  "a < length xs \<Longrightarrow> xs\<lbrakk>a..a+1\<rparr> = [xs!a]"
  unfolding slice_drop_take
  by (metis Cons_nth_drop_Suc One_nat_def diff_add_inverse drop_take take_Suc_Cons take_eq_Nil)

lemma slice_append_nth:
  "a \<le> b \<Longrightarrow> b < length xs \<Longrightarrow> xs\<lbrakk>a..b\<rparr> @ [xs!b] = xs\<lbrakk>a..b+1\<rparr>"
  by (metis le_add1 slice_concat slice_nth)

lemma slice_empty:
  "b \<le> a \<Longrightarrow> xs\<lbrakk>a..b\<rparr> = []"
  by (simp add: slice_drop_take)

lemma slice_id[simp]:
  "xs\<lbrakk>0..length xs\<rparr> = xs"
  by (simp add: slice_drop_take)

lemma slice_singleton:
  "b \<le> length xs \<Longrightarrow> [x] = xs\<lbrakk>a..b\<rparr> \<Longrightarrow> b = a + 1"
  by (induction xs a b rule: slice.induct) (auto simp: slice_drop_take)


section \<open>Earley recognizer\<close>

subsection \<open>Earley items\<close>

definition rule_head :: "('a, 'b) rule \<Rightarrow> ('a, 'b) symbol" where
  "rule_head \<equiv> fst"

definition rule_body :: "('a, 'b) rule \<Rightarrow> ('a, 'b) word" where
  "rule_body \<equiv> snd"

datatype ('a, 'b) item = 
  Item (item_rule: "('a, 'b) rule") (item_dot : nat) (item_origin : nat) (item_end : nat)

definition item_rule_head :: "('a, 'b) item \<Rightarrow> ('a, 'b) symbol" where
  "item_rule_head x \<equiv> rule_head (item_rule x)"

definition item_rule_body :: "('a, 'b) item \<Rightarrow> ('a, 'b) word" where
  "item_rule_body x \<equiv> rule_body (item_rule x)"

definition item_\<alpha> :: "('a, 'b) item \<Rightarrow> ('a, 'b) word" where
  "item_\<alpha> x \<equiv> take (item_dot x) (item_rule_body x)"

definition item_\<beta> :: "('a, 'b) item \<Rightarrow> ('a, 'b) word" where 
  "item_\<beta> x \<equiv> drop (item_dot x) (item_rule_body x)"

definition is_complete :: "('a, 'b) item \<Rightarrow> bool" where
  "is_complete x \<equiv> item_dot x \<ge> length (item_rule_body x)"

definition next_symbol :: "('a, 'b) item \<Rightarrow> ('a, 'b) symbol option" where
  "next_symbol x \<equiv> if is_complete x then None else Some (item_rule_body x ! item_dot x)"

lemmas item_defs = item_rule_head_def item_rule_body_def item_\<alpha>_def item_\<beta>_def rule_head_def rule_body_def

definition is_finished :: "('a, 'b) cfg \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) item \<Rightarrow> bool" where
  "is_finished \<G> \<omega> x \<equiv>
    item_rule_head x = \<SS> \<G> \<and>
    item_origin x = 0 \<and>
    item_end x = length \<omega> \<and> 
    is_complete x"

definition recognizing :: "('a, 'b) item set \<Rightarrow> ('a, 'b) cfg \<Rightarrow> ('a, 'b) word \<Rightarrow> bool" where
  "recognizing I \<G> \<omega> \<equiv> \<exists>x \<in> I. is_finished \<G> \<omega> x"

inductive_set Earley :: "('a, 'b) cfg \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) item set"
  for \<G> :: "('a, 'b) cfg" and \<omega> :: "('a, 'b) word" where
    Init: "r \<in> set (\<RR> \<G>) \<Longrightarrow> fst r = \<SS> \<G> \<Longrightarrow>
      Item r 0 0 0 \<in> Earley \<G> \<omega>"
  | Scan: "x = Item r b i j \<Longrightarrow> x \<in> Earley \<G> \<omega> \<Longrightarrow>
    \<omega>!j = a \<Longrightarrow> j < length \<omega> \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
      Item r (b + 1) i (j + 1) \<in> Earley \<G> \<omega>"
  | Predict: "x = Item r b i j \<Longrightarrow> x \<in> Earley \<G> \<omega> \<Longrightarrow>
    r' \<in> set (\<RR> \<G>) \<Longrightarrow> next_symbol x = Some (rule_head r') \<Longrightarrow>
      Item r' 0 j j \<in> Earley \<G> \<omega>"
  | Complete: "x = Item r\<^sub>x b\<^sub>x i j \<Longrightarrow> x \<in> Earley \<G> \<omega> \<Longrightarrow> y = Item r\<^sub>y b\<^sub>y j k \<Longrightarrow> y \<in> Earley \<G> \<omega> \<Longrightarrow>
      is_complete y \<Longrightarrow> next_symbol x = Some (item_rule_head y) \<Longrightarrow>
        Item r\<^sub>x (b\<^sub>x + 1) i k \<in> Earley \<G> \<omega>"


subsection \<open>Well-formedness\<close>

definition wf_item :: "('a, 'b) cfg \<Rightarrow> ('a, 'b) word => ('a, 'b) item \<Rightarrow> bool" where 
  "wf_item \<G> \<omega> x \<equiv>
    item_rule x \<in> set (\<RR> \<G>) \<and> 
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length \<omega>"

lemma wf_Init:
  assumes "r \<in> set (\<RR> \<G>)" "fst r = \<SS> \<G>"
  shows "wf_item \<G> \<omega> (Item r 0 0 0)"
  using assms unfolding wf_item_def by simp

lemma wf_Scan:
  assumes "x = Item r b i j" "wf_item \<G> \<omega> x" "\<omega>!j = a" "j < length \<omega>" "next_symbol x = Some a"
  shows "wf_item \<G> \<omega> (Item r (b + 1) i (j+1))"
  using assms unfolding wf_item_def by (auto simp: item_defs is_complete_def next_symbol_def split: if_splits)

lemma wf_Predict:
  assumes "x = Item r b i j" "wf_item \<G> \<omega> x" "r' \<in> set (\<RR> \<G>)" "next_symbol x = Some (rule_head r')"
  shows "wf_item \<G> \<omega> (Item r' 0 j j)"
  using assms unfolding wf_item_def by simp

lemma wf_Complete:
  assumes "x = Item r\<^sub>x b\<^sub>x i j" "wf_item \<G> \<omega> x" "y = Item r\<^sub>y b\<^sub>y j k" "wf_item \<G> \<omega> y"
  assumes "is_complete y" "next_symbol x = Some (item_rule_head y)"
  shows "wf_item \<G> \<omega> (Item r\<^sub>x (b\<^sub>x + 1) i k)"
  using assms unfolding wf_item_def is_complete_def next_symbol_def item_rule_body_def
  by (auto split: if_splits)

lemma wf_Earley:
  assumes "x \<in> Earley \<G> \<omega>"
  shows "wf_item \<G> \<omega> x"
  using assms wf_Init wf_Scan wf_Predict wf_Complete
  by (induction rule: Earley.induct) fast+


subsection \<open>Soundness\<close>

definition sound_item :: "('a, 'b) cfg \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) item \<Rightarrow> bool" where
  "sound_item \<G> \<omega> x \<equiv> \<G> \<turnstile> [item_rule_head x] \<Rightarrow>\<^sup>* (\<omega>\<lbrakk>item_origin x..item_end x\<rparr> @ item_\<beta> x)"

lemma sound_Init:
  assumes "r \<in> set (\<RR> \<G>)" "fst r = \<SS> \<G>"
  shows "sound_item \<G> \<omega> (Item r 0 0 0)"
proof -
  let ?x = "Item r 0 0 0"
  have "(item_rule_head ?x, item_\<beta> ?x) \<in> set (\<RR> \<G>)"
    using assms(1) by (simp add: item_defs)
  hence "\<G> \<turnstile> [item_rule_head ?x] \<Rightarrow>\<^sup>* (item_\<beta> ?x)"
    using derives_if_valid_rule by metis
  thus "sound_item \<G> \<omega> ?x"
    unfolding sound_item_def by (simp add: slice_empty)
qed

lemma sound_Scan:
  assumes "x = Item r b i j" "wf_item \<G> \<omega> x" "sound_item \<G> \<omega> x"
  assumes "\<omega>!j = a" "j < length \<omega>" "next_symbol x = Some a"
  shows "sound_item \<G> \<omega> (Item r (b+1) i (j+1))"
proof -
  define x' where [simp]: "x' = Item r (b+1) i (j+1)"
  obtain item_\<beta>' where *: "item_\<beta> x = a # item_\<beta>'" "item_\<beta> x' = item_\<beta>'"
    using assms(1,6) apply (auto simp: item_defs next_symbol_def is_complete_def split: if_splits)
    by (metis Cons_nth_drop_Suc leI)
  have "\<omega>\<lbrakk>i..j\<rparr> @ item_\<beta> x = \<omega>\<lbrakk>i..j+1\<rparr> @ item_\<beta>'"
    using * assms(1,2,4,5) by (auto simp: slice_append_nth wf_item_def)
  moreover have "\<G> \<turnstile> [item_rule_head x] \<Rightarrow>\<^sup>* (\<omega>\<lbrakk>i..j\<rparr> @ item_\<beta> x)"
    using assms(1,3) sound_item_def by force
  ultimately show ?thesis
    using assms(1) * by (auto simp: item_defs sound_item_def)
qed

lemma sound_Predict:
  assumes "x = Item r b i j" "wf_item \<G> \<omega> x" "sound_item \<G> \<omega> x"
  assumes "r' \<in> set (\<RR> \<G>)" "next_symbol x = Some (rule_head r')"
  shows "sound_item \<G> \<omega> (Item r' 0 j j)"
  using assms by (auto simp: sound_item_def derives_if_valid_rule slice_empty item_defs)

lemma sound_Complete:
  assumes "x = Item r\<^sub>x b\<^sub>x i j" "wf_item \<G> \<omega> x" "sound_item \<G> \<omega> x"
  assumes "y = Item r\<^sub>y b\<^sub>y j k" "wf_item \<G> \<omega> y" "sound_item \<G> \<omega> y"
  assumes "is_complete y" "next_symbol x = Some (item_rule_head y)"
  shows "sound_item \<G> \<omega> (Item r\<^sub>x (b\<^sub>x + 1) i k)"
proof -
  have "\<G> \<turnstile> [item_rule_head y] \<Rightarrow>\<^sup>* (\<omega>\<lbrakk>j..k\<rparr>)"
    using assms(4,6,7) by (auto simp: sound_item_def is_complete_def item_defs)
  then obtain E where E: "Derivation \<G> [item_rule_head y] E (\<omega>\<lbrakk>j..k\<rparr>)"
    using derives_implies_Derivation by blast
  have "\<G> \<turnstile> [item_rule_head x] \<Rightarrow>\<^sup>* (\<omega>\<lbrakk>i..j\<rparr> @ item_\<beta> x)"
    using assms(1,3,4) by (auto simp: sound_item_def)
  moreover have 0: "item_\<beta> x = (item_rule_head y) # tl (item_\<beta> x)"
    using assms(8) apply (auto simp: next_symbol_def is_complete_def item_defs split: if_splits)
    by (metis drop_eq_Nil hd_drop_conv_nth leI list.collapse)
  ultimately obtain D where D: 
    "Derivation \<G> [item_rule_head x] D (\<omega>\<lbrakk>i..j\<rparr> @ [item_rule_head y] @ (tl (item_\<beta> x)))"
    using derives_implies_Derivation by (metis append_Cons append_Nil)
  obtain F where F:
    "Derivation \<G> [item_rule_head x] F (\<omega>\<lbrakk>i..j\<rparr> @ \<omega>\<lbrakk>j..k\<rparr> @ tl (item_\<beta> x))"
    using Derivation_append_rewrite D E by blast
  moreover have "i \<le> j"
    using assms(1,2) wf_item_def by force
  moreover have "j \<le> k"
    using assms(4,5) wf_item_def by force
  ultimately have "\<G> \<turnstile> [item_rule_head x] \<Rightarrow>\<^sup>* (\<omega>\<lbrakk>i..k\<rparr> @ tl (item_\<beta> x))"
    by (metis Derivation_implies_derives append.assoc slice_concat)
  thus "sound_item \<G> \<omega> (Item r\<^sub>x (b\<^sub>x + 1) i k)"
    using assms(1,4) by (auto simp: sound_item_def item_defs drop_Suc tl_drop)
qed

lemma sound_Earley:
  assumes "x \<in> Earley \<G> \<omega>" "wf_item \<G> \<omega> x"
  shows "sound_item \<G> \<omega> x"
  using assms
proof (induction rule: Earley.induct)
  case (Init r)
  thus ?case
    using sound_Init by blast
next
  case (Scan x r b i j a)
  thus ?case
    using wf_Earley sound_Scan by fast
next
  case (Predict x r b i j r')
  thus ?case
    using wf_Earley sound_Predict  by blast
next
  case (Complete x r\<^sub>x b\<^sub>x i j y r\<^sub>y b\<^sub>y k)
  thus ?case
    using wf_Earley sound_Complete by metis
qed

theorem soundness_Earley:
  assumes "recognizing (Earley \<G> \<omega>) \<G> \<omega>"
  shows "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
proof -
  obtain x where x: "x \<in> Earley \<G> \<omega>" "is_finished \<G> \<omega> x"
    using assms recognizing_def by blast
  hence "sound_item \<G> \<omega> x"
    using wf_Earley sound_Earley by blast
  thus ?thesis
    unfolding sound_item_def using x by (auto simp: is_finished_def is_complete_def item_defs)
qed


subsection \<open>Completeness\<close>

definition partially_completed :: "nat \<Rightarrow> ('a, 'b) cfg \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) item set \<Rightarrow> (('a, 'b) derivation \<Rightarrow> bool) \<Rightarrow> bool" where
  "partially_completed k \<G> \<omega> E P \<equiv> \<forall>r b i' i j x a D.
    i \<le> j \<and> j \<le> k \<and> k \<le> length \<omega> \<and>
    x = Item r b i' i \<and> x \<in> E \<and> next_symbol x = Some a \<and>
    Derivation \<G> [a] D \<omega>\<lbrakk>i..j\<rparr> \<and> P D \<longrightarrow>
    Item r (b+1) i' j \<in> E"

lemma partially_completed_upto:
  assumes "j \<le> k" "k \<le> length \<omega>"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> I" "\<forall>x \<in> I. wf_item \<G> \<omega> x"
  assumes "Derivation \<G> (item_\<beta> x) D \<omega>\<lbrakk>j..k\<rparr>"
  assumes "partially_completed k \<G> \<omega> I (\<lambda>D'. length D' \<le> length D)"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> I"
  using assms
proof (induction "item_\<beta> x" arbitrary: d i j k N \<alpha> x D)
  case Nil
  have "item_\<alpha> x = \<alpha>"
    using Nil(1,4) unfolding item_\<alpha>_def item_\<beta>_def item_rule_body_def rule_body_def by simp
  hence "x = Item (N,\<alpha>) (length \<alpha>) i j"
    using Nil.hyps Nil.prems(3-5) unfolding wf_item_def item_defs by auto
  have "Derivation \<G> [] D \<omega>\<lbrakk>j..k\<rparr>"
    using Nil.hyps Nil.prems(6) by auto
  hence "\<omega>\<lbrakk>j..k\<rparr> = []"
    using Derivation_from_empty by blast
  hence "j = k"
    unfolding slice_drop_take using Nil.prems(1,2) by simp
  thus ?case
    using \<open>x = Item (N, \<alpha>) (length \<alpha>) i j\<close> Nil.prems(4) by blast
next
  case (Cons b bs)
  obtain j' E F where *: 
    "Derivation \<G> [b] E \<omega>\<lbrakk>j..j'\<rparr>"
    "Derivation \<G> bs F \<omega>\<lbrakk>j'..k\<rparr>"
    "j \<le> j'" "j' \<le> k" "length E \<le> length D" "length F \<le> length D"
    using Derivation_concat_split[of \<G> "[b]" bs D "\<omega>\<lbrakk>j..k\<rparr>"] slice_concat_Ex
    using Cons.hyps(2) Cons.prems(1,6)
    by (smt (verit, ccfv_threshold) Cons_eq_appendI append_self_conv2)
  have "next_symbol x = Some b"
    using Cons.hyps(2) unfolding item_defs(4) next_symbol_def is_complete_def by (auto, metis nth_via_drop)
  hence "Item (N, \<alpha>) (d+1) i j' \<in> I"
    using Cons.prems(7) unfolding partially_completed_def
    using Cons.prems(2,3,4) *(1,3-5) by blast
  moreover have "partially_completed k \<G> \<omega> I (\<lambda>D'. length D' \<le> length F)"
    using Cons.prems(7) *(6) unfolding partially_completed_def by fastforce
  moreover have "bs = item_\<beta> (Item (N,\<alpha>) (d+1) i j')"
    using Cons.hyps(2) Cons.prems(3) unfolding item_defs(4) item_rule_body_def 
    by (auto, metis List.list.sel(3) drop_Suc drop_tl)
  ultimately show ?case
    using Cons.hyps(1) *(2,4) Cons.prems(2,3,5) wf_item_def by blast
qed

lemma partially_completed_Earley_k:
  assumes "wf_\<G> \<G>"
  shows "partially_completed k \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>_. True)"
  unfolding partially_completed_def
proof (standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix r b i' i j x a D
  assume
    "i \<le> j \<and> j \<le> k \<and> k \<le> length \<omega> \<and>
     x = Item r b i' i \<and> x \<in> Earley \<G> \<omega> \<and>
     next_symbol x = Some a \<and>
     Derivation \<G> [a] D \<omega>\<lbrakk>i..j\<rparr> \<and> True"
  thus "Item r (b + 1) i' j \<in> Earley \<G> \<omega>"
  proof (induction "length D" arbitrary: r b i' i j x a D rule: nat_less_induct)
    case 1
    show ?case
    proof cases
      assume "D = []"
      hence "[a] = \<omega>\<lbrakk>i..j\<rparr>"
        using "1.prems" by force
      moreover have "j \<le> length \<omega>"
        using le_trans "1.prems" by blast
      ultimately have "j = i+1"
        using slice_singleton by metis
      hence "i < length \<omega>"
        using \<open>j \<le> length \<omega>\<close> discrete by blast
      hence "\<omega>!i = a"
        using slice_nth \<open>[a] = \<omega>\<lbrakk>i..j\<rparr>\<close> \<open>j = i + 1\<close> by fastforce
      hence "Item r (b + 1) i' j \<in> Earley \<G> \<omega>"
        using Earley.Scan "1.prems" \<open>i < length \<omega>\<close> \<open>j = i + 1\<close> by metis
      thus ?thesis
        by (simp add: \<open>j = i + 1\<close>)
    next
      assume "\<not> D = []"
      then obtain d D' where "D = d # D'"
        by (meson List.list.exhaust)
      then obtain \<alpha> where *: "Derives1 \<G> [a] (fst d) (snd d) \<alpha>" "Derivation \<G> \<alpha> D' \<omega>\<lbrakk>i..j\<rparr>"
        using "1.prems" by auto
      hence rule: "(a, \<alpha>) \<in> set (\<RR> \<G>)" "fst d = 0" "snd d = (a ,\<alpha>)"
        using *(1) unfolding Derives1_def by (simp add: Cons_eq_append_conv)+
      show ?thesis
      proof cases
        assume "is_terminal a"
        have "is_nonterminal a"
          using rule assms by force
        thus ?thesis
          using \<open>is_terminal a\<close> is_terminal_nonterminal by (metis assms)
      next
        assume "\<not> is_terminal a"
        define y where y_def: "y = Item (a ,\<alpha>) 0 i i"
        have "length D' < length D"
          using \<open>D = d # D'\<close> by fastforce
        hence "partially_completed k \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>E. length E \<le> length D')"
          unfolding partially_completed_def using "1.hyps" order_le_less_trans by (smt (verit, best))
        hence "partially_completed j \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>E. length E \<le> length D')"
          unfolding partially_completed_def using "1.prems" by force
        moreover have "Derivation \<G> (item_\<beta> y) D' \<omega>\<lbrakk>i..j\<rparr>"
          using *(2) by (auto simp: item_defs y_def)
        moreover have "y \<in> Earley \<G> \<omega>"
          using y_def "1.prems" rule by (auto simp: item_defs Earley.Predict)
        moreover have "j \<le> length \<omega>"
          using "1.prems" by simp
        ultimately have "Item (a,\<alpha>) (length \<alpha>) i j \<in> Earley \<G> \<omega>"
          using partially_completed_upto "1.prems" wf_Earley y_def by metis
        moreover have x: "x = Item r b i' i" "x \<in> Earley \<G> \<omega>"
          using "1.prems" by blast+
        moreover have "next_symbol x = Some a"
          using "1.prems" by linarith
        ultimately show ?thesis
          using Earley.Complete[OF x] by (auto simp: is_complete_def item_defs)
      qed
    qed
  qed
qed

lemma partially_completed_Earley:
  "wf_\<G> \<G> \<Longrightarrow> partially_completed (length \<omega>) \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>_. True)"
  by (simp add: partially_completed_Earley_k)

theorem completeness_Earley:
  assumes "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>" "is_word \<omega>" "wf_\<G> \<G>"
  shows "recognizing (Earley \<G> \<omega>) \<G> \<omega>"
proof -
  obtain \<alpha> D where *: "(\<SS> \<G> ,\<alpha>) \<in> set (\<RR> \<G>)" "Derivation \<G> \<alpha> D \<omega>"
    using Derivation_\<SS>1 assms derives_implies_Derivation by metis
  define x where x_def: "x = Item (\<SS> \<G>, \<alpha>) 0 0 0"
  have "partially_completed (length \<omega>) \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>_. True)"
    using assms(3) partially_completed_Earley by blast
  hence 0: "partially_completed (length \<omega>) \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>D'. length D' \<le> length D)"
    unfolding partially_completed_def by blast
  have 1: "x \<in> Earley \<G> \<omega>"
    using x_def Earley.Init *(1) by fastforce
  have 2: "Derivation \<G> (item_\<beta> x) D \<omega>\<lbrakk>0..length \<omega>\<rparr>"
    using *(2) x_def by (simp add: item_defs)
  have "Item (\<SS> \<G>,\<alpha>) (length \<alpha>) 0 (length \<omega>) \<in> Earley \<G> \<omega>"
    using partially_completed_upto[OF _ _ _ _ _ 2 0] wf_Earley 1 x_def by auto
  then show ?thesis
    unfolding recognizing_def is_finished_def by (auto simp: is_complete_def item_defs, force)
qed


subsection \<open>Correctness\<close>

theorem correctness_Earley:
  assumes "wf_\<G> \<G>" "is_word \<omega>"
  shows "recognizing (Earley \<G> \<omega>) \<G> \<omega> \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
  using assms soundness_Earley completeness_Earley by blast


subsection \<open>Finiteness\<close>

lemma finiteness_empty:
  "set (\<RR> \<G>) = {} \<Longrightarrow> finite { x | x. wf_item \<G> \<omega> x }"
  unfolding wf_item_def by simp

fun item_intro :: "('a, 'b) rule \<times> nat \<times> nat \<times> nat \<Rightarrow> ('a, 'b) item" where
  "item_intro (rule, dot, origin, ends) = Item rule dot origin ends" 

lemma finiteness_nonempty:
  assumes "set (\<RR> \<G>) \<noteq> {}"
  shows "finite { x | x. wf_item \<G> \<omega> x }"
proof -
  define M where "M = Max { length (rule_body r) | r. r \<in> set (\<RR> \<G>) }"
  define Top where "Top = (set (\<RR> \<G>) \<times> {0..M} \<times> {0..length \<omega>} \<times> {0..length \<omega>})"
  hence "finite Top"
    using finite_cartesian_product finite by blast
  have "inj_on item_intro Top"
    unfolding Top_def inj_on_def by simp
  hence "finite (item_intro ` Top)"
    using finite_image_iff \<open>finite Top\<close> by auto
  have "{ x | x. wf_item \<G> \<omega> x } \<subseteq> item_intro ` Top"
  proof standard
    fix x
    assume "x \<in> { x | x. wf_item \<G> \<omega> x }"
    then obtain rule dot origin endp where *: "x = Item rule dot origin endp"
      "rule \<in> set (\<RR> \<G>)" "dot \<le> length (item_rule_body x)" "origin \<le> length \<omega>" "endp \<le> length \<omega>"
      unfolding wf_item_def using item.exhaust_sel le_trans by blast
    hence "length (rule_body rule) \<in> { length (rule_body r) | r. r \<in> set (\<RR> \<G>) }"
      using *(1,2) item_rule_body_def by blast
    moreover have "finite { length (rule_body r) | r. r \<in> set (\<RR> \<G>) }"
      using finite finite_image_set[of "\<lambda>x. x \<in> set (\<RR> \<G>)"] by fastforce
    ultimately have "M \<ge> length (rule_body rule)"
      unfolding M_def by simp
    hence "dot \<le> M"
      using *(1,3) item_rule_body_def by (metis item.sel(1) le_trans)
    hence "(rule, dot, origin, endp) \<in> Top"
      using *(2,4,5) unfolding Top_def by simp
    thus "x \<in> item_intro ` Top"
      using *(1) by force
  qed
  thus ?thesis
    using \<open>finite (item_intro ` Top)\<close> rev_finite_subset by auto
qed

lemma finiteness_UNIV_wf_item:
  "finite { x | x. wf_item \<G> \<omega> x }"
  using finiteness_empty finiteness_nonempty by fastforce

theorem finiteness_Earley:
  "finite (Earley \<G> \<omega>)"
  using finiteness_UNIV_wf_item wf_Earley rev_finite_subset by (metis mem_Collect_eq subsetI)

end
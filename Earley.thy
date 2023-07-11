theory Earley
  imports
    Derivations
    Limit
begin

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
    by (auto, metis slice.simps(4) Suc_le_mono)
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


section \<open>Derivation Lemmas\<close>

lemma Derives1_prepend:
  assumes "Derives1 cfg u i r v"
  shows "Derives1 cfg (w@u) (i + length w) r (w@v)"
proof -
  obtain x y N \<alpha> where *:
    "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
    "(N, \<alpha>) \<in> set (\<RR> cfg)" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by (smt (verit))
  hence "w@u = w @ x @ [N] @ y" "w@v = w @ x @ \<alpha> @ y"
    by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="w@x"])
    apply (rule_tac exI[where x="y"])
    by simp
qed

lemma Derivation_prepend:
  "Derivation cfg b D b' \<Longrightarrow> Derivation cfg (a@b) (map (\<lambda>(i, r). (i + length a, r)) D) (a@b')"
  using Derives1_prepend by (induction D arbitrary: b b') (auto, fast)

lemma Derives1_append:
  assumes "Derives1 cfg u i r v"
  shows "Derives1 cfg (u@w) i r (v@w)"
proof -
  obtain x y N \<alpha> where *: 
    "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
    "(N, \<alpha>) \<in> set (\<RR> cfg)" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by (smt (verit))
  hence "u@w = x @ [N] @ y @ w" "v@w = x @ \<alpha> @ y @ w"
    by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="x"])
    apply (rule_tac exI[where x="y@w"])
    by blast
qed

lemma Derivation_append':
  "Derivation cfg a D a' \<Longrightarrow> Derivation cfg (a@b) D (a'@b)"
  using Derives1_append by (induction D arbitrary: a a') (auto, fast)

lemma Derivation_append_rewrite:
  assumes "Derivation cfg a D (b @ c @ d) " "Derivation cfg c E c'"
  shows "\<exists>F. Derivation cfg a F (b @ c' @ d)"
  using assms Derivation_append' Derivation_prepend Derivation_implies_append by fast

lemma derives1_if_valid_rule:
  "(N, \<alpha>) \<in> set (\<RR> cfg) \<Longrightarrow> derives1 cfg [N] \<alpha>"
  unfolding derives1_def
  apply (rule_tac exI[where x="[]"])
  apply (rule_tac exI[where x="[]"])
  by simp

lemma derives_if_valid_rule:
  "(N, \<alpha>) \<in> set (\<RR> cfg) \<Longrightarrow> derives cfg [N] \<alpha>"
  using derives1_if_valid_rule by fastforce

lemma Derivation_from_empty:
  "Derivation cfg [] D a \<Longrightarrow> a = []"
  by (cases D) (auto simp: Derives1_def)

lemma Derivation_concat_split:
  "Derivation cfg (a@b) D c \<Longrightarrow> \<exists>E F a' b'. Derivation cfg a E a' \<and> Derivation cfg b F b' \<and>
     c = a' @ b' \<and> length E \<le> length D \<and> length F \<le> length D"
proof (induction D arbitrary: a b)
  case Nil
  thus ?case
    by (metis Derivation.simps(1) order_refl)
next
  case (Cons d D)
  then obtain ab where *: "Derives1 cfg (a@b) (fst d) (snd d) ab" "Derivation cfg ab D c"
    by auto
  then obtain x y N \<alpha> where #:
    "a@b = x @ [N] @ y" "ab = x @ \<alpha> @ y" "(N,\<alpha>) \<in> set (\<RR> cfg)" "snd d = (N,\<alpha>)" "fst d = length x"
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
      "Derivation cfg (take (length a) x) E a'"
      "Derivation cfg (drop (length a) x @ \<alpha> @ y) F b'"
      "c = a' @ b'"
      "length E \<le> length D"
      "length F \<le> length D"
      using Cons *(2) by blast
    have "Derives1 cfg b (fst d - length a) (snd d) (drop (length a) x @ \<alpha> @ y)"
      unfolding Derives1_def using *(1) #(3-5) ab_def(2) by (metis length_drop)
    hence "Derivation cfg b ((fst d - length a, snd d) # F) b'"
      using IH(2) by force
    moreover have "Derivation cfg a E a'"
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
      "Derivation cfg (x @ \<alpha> @ take (length a - length x - 1) y) E a'"
      "Derivation cfg (drop (length a - length x - 1) y) F b'"
      "c = a' @ b'"
      "length E \<le> length D"
      "length F \<le> length D"
      using Cons.IH[of "x @ \<alpha> @ take (length a - length x - 1) y" "drop (length a - length x - 1) y"] *(2) by auto
    have "Derives1 cfg a (fst d) (snd d) (x @ \<alpha> @ take (length a - length x - 1) y)"
      unfolding Derives1_def using #(3-5) a_def by blast
    hence "Derivation cfg a ((fst d, snd d) # E) a'"
      using IH(1) by fastforce
    moreover have "Derivation cfg b F b'"
      using b_def IH(2) by blast
    ultimately show ?thesis
      using IH(3-5) by fastforce
  qed
qed


section \<open>Earley recognizer\<close>

subsection \<open>Earley Items\<close>

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

definition item_rule_head :: "'a item \<Rightarrow> 'a" where
  "item_rule_head x = rule_head (item_rule x)"

definition item_rule_body :: "'a item \<Rightarrow> 'a sentence" where
  "item_rule_body x = rule_body (item_rule x)"

definition item_\<alpha> :: "'a item \<Rightarrow> 'a sentence" where
  "item_\<alpha> x = take (item_dot x) (item_rule_body x)"

definition item_\<beta> :: "'a item \<Rightarrow> 'a sentence" where 
  "item_\<beta> x = drop (item_dot x) (item_rule_body x)"

definition is_complete :: "'a item \<Rightarrow> bool" where
  "is_complete x = (item_dot x \<ge> length (item_rule_body x))"

definition next_symbol :: "'a item \<Rightarrow> 'a option" where
  "next_symbol x = (if is_complete x then None else Some (item_rule_body x ! item_dot x))"

lemmas item_defs = item_rule_head_def item_rule_body_def item_\<alpha>_def item_\<beta>_def rule_head_def rule_body_def

definition is_finished :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item \<Rightarrow> bool" where
  "is_finished cfg inp x \<equiv>
    item_rule_head x = \<SS> cfg \<and>
    item_origin x = 0 \<and>
    item_end x = length inp \<and> 
    is_complete x"

definition earley_recognized :: "'a item set \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "earley_recognized I cfg inp = (\<exists>x \<in> I. is_finished cfg inp x)"

inductive_set Earley :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set"
  for \<G> :: "'a cfg" and \<omega> :: "'a sentence" where
  Init: "r \<in> set (\<RR> \<G>) \<Longrightarrow> fst r = \<SS> \<G>
    \<Longrightarrow> Item r 0 0 0 \<in> Earley \<G> \<omega>"
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

definition wf_item :: "'a cfg \<Rightarrow> 'a sentence => 'a item \<Rightarrow> bool" where 
  "wf_item cfg inp x = (
    item_rule x \<in> set (\<RR> cfg) \<and> 
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length inp)"

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

definition sound_item :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item \<Rightarrow> bool" where
  "sound_item \<G> \<omega> x = derives \<G> [item_rule_head x] (slice (item_origin x) (item_end x) \<omega> @ item_\<beta> x)"

lemma sound_Init:
  assumes "r \<in> set (\<RR> \<G>)" "fst r = \<SS> \<G>"
  shows "sound_item \<G> \<omega> (Item r 0 0 0)"
proof -
  let ?x = "Item r 0 0 0"
  have "(item_rule_head ?x, item_\<beta> ?x) \<in> set (\<RR> \<G>)"
    using assms(1) by (simp add: item_defs)
  hence "derives \<G> [item_rule_head ?x] (item_\<beta> ?x)"
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
  have "slice i j \<omega> @ item_\<beta> x = slice i (j+1) \<omega> @ item_\<beta>'"
    using * assms(1,2,4,5) by (auto simp: slice_append_nth wf_item_def)
  moreover have "derives \<G> [item_rule_head x] (slice i j \<omega> @ item_\<beta> x)"
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
  have "derives \<G> [item_rule_head y] (slice j k \<omega>)"
    using assms(4,6,7) by (auto simp: sound_item_def is_complete_def item_defs)
  then obtain E where E: "Derivation \<G> [item_rule_head y] E (slice j k \<omega>)"
    using derives_implies_Derivation by blast
  have "derives \<G> [item_rule_head x] (slice i j \<omega> @ item_\<beta> x)"
    using assms(1,3,4) by (auto simp: sound_item_def)
  moreover have 0: "item_\<beta> x = (item_rule_head y) # tl (item_\<beta> x)"
    using assms(8) apply (auto simp: next_symbol_def is_complete_def item_defs split: if_splits)
    by (metis drop_eq_Nil hd_drop_conv_nth leI list.collapse)
  ultimately obtain D where D: 
    "Derivation \<G> [item_rule_head x] D (slice i j \<omega> @ [item_rule_head y] @ (tl (item_\<beta> x)))"
    using derives_implies_Derivation by (metis append_Cons append_Nil)
  obtain F where F:
    "Derivation \<G> [item_rule_head x] F (slice i j \<omega> @ slice j k \<omega> @ tl (item_\<beta> x))"
    using Derivation_append_rewrite D E by blast
  moreover have "i \<le> j"
    using assms(1,2) wf_item_def by force
  moreover have "j \<le> k"
    using assms(4,5) wf_item_def by force
  ultimately have "derives \<G> [item_rule_head x] (slice i k \<omega> @ tl (item_\<beta> x))"
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

theorem soundness:
  assumes "earley_recognized (Earley \<G> \<omega>) \<G> \<omega>"
  shows "derives \<G> [\<SS> \<G>] \<omega>"
proof -
  obtain x where x: "x \<in> Earley \<G> \<omega>" "is_finished \<G> \<omega> x"
    using assms earley_recognized_def by blast
  hence "sound_item \<G> \<omega> x"
    using wf_Earley sound_Earley by blast
  thus ?thesis
    unfolding sound_item_def using x by (auto simp: is_finished_def is_complete_def item_defs)
qed


subsection \<open>Completeness\<close>

definition partially_completed :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set \<Rightarrow> ('a derivation \<Rightarrow> bool) \<Rightarrow> bool" where
  "partially_completed k \<G> \<omega> E P = (
    \<forall>r b i' i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length \<omega> \<and>
      x = Item r b i' i \<and> x \<in> E \<and> next_symbol x = Some a \<and>
      Derivation \<G> [a] D (slice i j \<omega>) \<and> P D \<longrightarrow>
      Item r (b+1) i' j \<in> E
  )"

lemma partially_completed_upto:
  assumes "j \<le> k" "k \<le> length \<omega>"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> I" "\<forall>x \<in> I. wf_item \<G> \<omega> x"
  assumes "Derivation \<G> (item_\<beta> x) D (slice j k \<omega>)"
  assumes "partially_completed k \<G> \<omega> I (\<lambda>D'. length D' \<le> length D)"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> I"
  using assms
proof (induction "item_\<beta> x" arbitrary: d i j k N \<alpha> x D)
  case Nil
  have "item_\<alpha> x = \<alpha>"
    using Nil(1,4) unfolding item_\<alpha>_def item_\<beta>_def item_rule_body_def rule_body_def by simp
  hence "x = Item (N,\<alpha>) (length \<alpha>) i j"
    using Nil.hyps Nil.prems(3-5) unfolding wf_item_def item_defs by auto
  have "Derivation \<G> [] D (slice j k \<omega>)"
    using Nil.hyps Nil.prems(6) by auto
  hence "slice j k \<omega> = []"
    using Derivation_from_empty by blast
  hence "j = k"
    unfolding slice_drop_take using Nil.prems(1,2) by simp
  thus ?case
    using \<open>x = Item (N, \<alpha>) (length \<alpha>) i j\<close> Nil.prems(4) by blast
next
  case (Cons b bs)
  obtain j' E F where *: 
    "Derivation \<G> [b] E (slice j j' \<omega>)"
    "Derivation \<G> bs F (slice j' k \<omega>)"
    "j \<le> j'" "j' \<le> k" "length E \<le> length D" "length F \<le> length D"
    using Derivation_concat_split[of \<G> "[b]" bs D "slice j k \<omega>"] slice_concat_Ex
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
  assumes "wf_cfg \<G>"
  shows "partially_completed k \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>_. True)"
  unfolding partially_completed_def
proof (standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix r b i' i j x a D
  assume
    "i \<le> j \<and> j \<le> k \<and> k \<le> length \<omega> \<and>
     x = Item r b i' i \<and> x \<in> Earley \<G> \<omega> \<and>
     next_symbol x = Some a \<and>
     Derivation \<G> [a] D (slice i j \<omega>) \<and> True"
  thus "Item r (b + 1) i' j \<in> Earley \<G> \<omega>"
  proof (induction "length D" arbitrary: r b i' i j x a D rule: nat_less_induct)
    case 1
    show ?case
    proof cases
      assume "D = []"
      hence "[a] = slice i j \<omega>"
        using "1.prems" by force
      moreover have "j \<le> length \<omega>"
        using le_trans "1.prems" by blast
      ultimately have "j = i+1"
        using slice_singleton by metis
      hence "i < length \<omega>"
        using \<open>j \<le> length \<omega>\<close> discrete by blast
      hence "\<omega>!i = a"
        using slice_nth \<open>[a] = slice i j \<omega>\<close> \<open>j = i + 1\<close> by fastforce
      hence "Item r (b + 1) i' j \<in> Earley \<G> \<omega>"
        using Earley.Scan "1.prems" \<open>i < length \<omega>\<close> \<open>j = i + 1\<close> by metis
      thus ?thesis
        by (simp add: \<open>j = i + 1\<close>)
    next
      assume "\<not> D = []"
      then obtain d D' where "D = d # D'"
        by (meson List.list.exhaust)
      then obtain \<alpha> where *: "Derives1 \<G> [a] (fst d) (snd d) \<alpha>" "Derivation \<G> \<alpha> D' (slice i j \<omega>)"
        using "1.prems" by auto
      hence rule: "(a, \<alpha>) \<in> set (\<RR> \<G>)" "fst d = 0" "snd d = (a ,\<alpha>)"
          using *(1) unfolding Derives1_def by (simp add: Cons_eq_append_conv)+
      show ?thesis
      proof cases
        assume "is_terminal \<G> a"
        have "is_nonterminal \<G> a"
          using rule by (simp add: assms)
        thus ?thesis
          using \<open>is_terminal \<G> a\<close> is_terminal_nonterminal by (metis assms)
      next
        assume "\<not> is_terminal \<G> a"
        define y where y_def: "y = Item (a ,\<alpha>) 0 i i"
        have "y \<in> Earley \<G> \<omega>"
          using y_def "1.prems" rule by (auto simp: item_defs Earley.Predict)
        have "i \<le> j"
          using "1.prems" by blast
        have "j \<le> length \<omega>"
          using "1.prems" by simp
        have "length D' < length D"
          using \<open>D = d # D'\<close> by fastforce

        have "\<forall>m<length D.
     \<forall>x. m = length x \<longrightarrow>
         (\<forall>xa xb xc xd xe xf xg.
             xd \<le> xe \<and> xe \<le> k \<and> k \<le> length \<omega> \<and> xf = Item xa xb xc xd \<and> xf \<in> Earley \<G> \<omega> \<and> next_symbol xf = Some xg
              \<and> Derivation \<G> [xg] x (slice xd xe \<omega>) \<and> True \<longrightarrow>
             Item xa (xb + 1) xc xe \<in> Earley \<G> \<omega>)"
          using "1.hyps" by blast
        hence "\<forall>m x.
      m < length D \<and> m = length x \<longrightarrow>
         (\<forall>xa xb xc xd xe xf xg.
             xd \<le> xe \<and> xe \<le> k \<and> k \<le> length \<omega> \<and> xf = Item xa xb xc xd \<and> xf \<in> Earley \<G> \<omega> \<and> next_symbol xf = Some xg
              \<and> Derivation \<G> [xg] x (slice xd xe \<omega>) \<and> True \<longrightarrow>
             Item xa (xb + 1) xc xe \<in> Earley \<G> \<omega>)"
          by blast
        hence "\<forall>m x.
      m \<le> length D' \<and> m = length x \<longrightarrow>
         (\<forall>xa xb xc xd xe xf xg.
             xd \<le> xe \<and> xe \<le> k \<and> k \<le> length \<omega> \<and> xf = Item xa xb xc xd \<and> xf \<in> Earley \<G> \<omega> \<and> next_symbol xf = Some xg
              \<and> Derivation \<G> [xg] x (slice xd xe \<omega>) \<and> True \<longrightarrow>
             Item xa (xb + 1) xc xe \<in> Earley \<G> \<omega>)"
          by (smt (verit, best) \<open>length D' < length D\<close> order_le_less_trans)
        hence "\<forall>x.
         (\<forall>xa xb xc xd xe xf xg.
             xd \<le> xe \<and> xe \<le> k \<and> k \<le> length \<omega> \<and> xf = Item xa xb xc xd \<and> xf \<in> Earley \<G> \<omega> \<and> next_symbol xf = Some xg
              \<and> Derivation \<G> [xg] x (slice xd xe \<omega>) \<and> length x \<le> length D' \<longrightarrow>
             Item xa (xb + 1) xc xe \<in> Earley \<G> \<omega>)"
          by fast
        hence "partially_completed k \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>E. length E \<le> length D')"
          unfolding partially_completed_def by blast
        hence 0: "partially_completed j \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>E. length E \<le> length D')"
          unfolding partially_completed_def using "1.prems" by force

        have 1: "Derivation \<G> (item_\<beta> y) D' (slice i j \<omega>)"
          using *(2) by (auto simp: item_defs y_def)
        have 0: "Item (a,\<alpha>) (length \<alpha>) i j \<in> Earley \<G> \<omega>"
          using partially_completed_upto by (metis "0" "1" "1.prems" \<open>j \<le> length \<omega>\<close> \<open>y \<in> Earley \<G> \<omega>\<close> wf_Earley y_def)

        have 2: "x = Item r b i' i" "x \<in> Earley \<G> \<omega>"
          using "1.prems" by blast+

        have "j \<le> k"
          using "1.prems" by blast
        have "next_symbol x = Some a"
          using "1.prems" by linarith
        thus ?thesis
          using Earley.Complete[OF 2 _ 0] by (auto simp: is_complete_def item_defs)
      qed
    qed
  qed
qed

lemma partially_completed_Earley:
  "wf_cfg \<G> \<Longrightarrow> partially_completed (length \<omega>) \<G> \<omega> (Earley \<G> \<omega>) (\<lambda>_. True)"
  by (simp add: partially_completed_Earley_k)

lemma Derivation_\<SS>1:
  assumes "Derivation \<G> [\<SS> \<G>] D \<omega>" "is_word \<G> \<omega>" "wf_cfg \<G>"
  shows "\<exists>\<alpha> E. Derivation \<G> \<alpha> E \<omega> \<and> (\<SS> \<G>,\<alpha>) \<in> set (\<RR> \<G>)"
proof (cases D)
  case Nil
  thus ?thesis
    using assms is_nonterminal_startsymbol is_terminal_nonterminal by (metis Derivation.simps(1) is_word_def list.set_intros(1))
next
  case (Cons d D)
  then obtain \<alpha> where "Derives1 \<G> [\<SS> \<G>] (fst d) (snd d) \<alpha>" "Derivation \<G> \<alpha> D \<omega>"
    using assms by auto
  hence "(\<SS> \<G>, \<alpha>) \<in> set (\<RR> \<G>)"
    unfolding Derives1_def
    by (metis List.append.right_neutral List.list.discI append_eq_Cons_conv append_is_Nil_conv nth_Cons_0 self_append_conv2)
  thus ?thesis
    using \<open>Derivation \<G> \<alpha> D \<omega>\<close> by auto
qed

theorem completeness:
  assumes "derives \<G> [\<SS> \<G>] \<omega>" "is_word \<G> \<omega>" "wf_cfg \<G>"
  shows "earley_recognized (Earley \<G> \<omega>) \<G> \<omega>"
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
  have 2: "Derivation \<G> (item_\<beta> x) D (slice 0 (length \<omega>) \<omega>)"
    using *(2) x_def by (simp add: item_defs)
  have "Item (\<SS> \<G>,\<alpha>) (length \<alpha>) 0 (length \<omega>) \<in> Earley \<G> \<omega>"
    using partially_completed_upto[OF _ _ _ _ _ 2 0] wf_Earley 1 x_def by auto
  then show ?thesis
    unfolding earley_recognized_def is_finished_def by (auto simp: is_complete_def item_defs, force)
qed

subsection \<open>Correctness\<close>

corollary correctness:
  assumes "wf_cfg cfg" "is_word cfg inp"
  shows "earley_recognized (Earley cfg inp) cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
  using assms soundness completeness by blast


subsection \<open>Finiteness\<close>

lemma finiteness_empty:
  "set (\<RR> cfg) = {} \<Longrightarrow> finite { x | x. wf_item cfg inp x }"
  unfolding wf_item_def by simp

fun item_intro :: "'a rule \<times> nat \<times> nat \<times> nat \<Rightarrow> 'a item" where
  "item_intro (rule, dot, origin, ends) = Item rule dot origin ends" 

lemma finiteness_nonempty:
  assumes "set (\<RR> cfg) \<noteq> {}"
  shows "finite { x | x. wf_item cfg inp x }"
proof -
  define M where "M = Max { length (rule_body r) | r. r \<in> set (\<RR> cfg) }"
  define Top where "Top = (set (\<RR> cfg) \<times> {0..M} \<times> {0..length inp} \<times> {0..length inp})"
  hence "finite Top"
    using finite_cartesian_product finite by blast
  have "inj_on item_intro Top"
    unfolding Top_def inj_on_def by simp
  hence "finite (item_intro ` Top)"
    using finite_image_iff \<open>finite Top\<close> by auto
  have "{ x | x. wf_item cfg inp x } \<subseteq> item_intro ` Top"
  proof standard
    fix x
    assume "x \<in> { x | x. wf_item cfg inp x }"
    then obtain rule dot origin endp where *: "x = Item rule dot origin endp"
      "rule \<in> set (\<RR> cfg)" "dot \<le> length (item_rule_body x)" "origin \<le> length inp" "endp \<le> length inp"
      unfolding wf_item_def using item.exhaust_sel le_trans by blast
    hence "length (rule_body rule) \<in> { length (rule_body r) | r. r \<in> set (\<RR> cfg) }"
      using *(1,2) item_rule_body_def by blast
    moreover have "finite { length (rule_body r) | r. r \<in> set (\<RR> cfg) }"
      using finite finite_image_set[of "\<lambda>x. x \<in> set (\<RR> cfg)"] by fastforce
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
  "finite { x | x. wf_item cfg inp x }"
  using finiteness_empty finiteness_nonempty by fastforce

theorem finiteness:
  "finite (Earley cfg inp)"
  using finiteness_UNIV_wf_item wf_Earley rev_finite_subset by (metis mem_Collect_eq subsetI)

end
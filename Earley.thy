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


section \<open>Additional Derivation Lemmas\<close>

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

definition is_opening :: "'a item \<Rightarrow> bool" where
  "is_opening x = (item_dot x = 0)"

definition prev_symbol :: "'a item \<Rightarrow> 'a option" where
  "prev_symbol x = (if is_opening x then None else Some ((item_rule_body x) ! (item_dot x - 1)))"

definition inc_item :: "'a item \<Rightarrow> nat \<Rightarrow> 'a item" where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

lemmas item_defs = item_rule_head_def item_rule_body_def item_\<alpha>_def item_\<beta>_def rule_head_def rule_body_def

definition bin :: "'a items \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"

definition wf_item :: "'a cfg \<Rightarrow> 'a sentence => 'a item \<Rightarrow> bool" where 
  "wf_item cfg inp x = (
    item_rule x \<in> set (\<RR> cfg) \<and> 
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length inp)"

definition wf_items :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> bool" where
  "wf_items cfg inp I = (\<forall>x \<in> I. wf_item cfg inp x)"


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
  "\<epsilon>_free cfg \<Longrightarrow> N \<in> set (\<NN> cfg) \<Longrightarrow> \<not> derives cfg [N] []"
  using \<epsilon>_free_impl_non_empty_sentence_deriv derives_implies_Derivation by (metis not_Cons_self2)


subsection \<open>Earley algorithm\<close>

definition Init :: "'a cfg \<Rightarrow> 'a items" where
  "Init cfg = { init_item r 0 | r. r \<in> set (\<RR> cfg) \<and> fst r = (\<SS> cfg) }"

definition Scan :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Scan k inp I = 
    { inc_item x (k+1) | x a.
        x \<in> bin I k \<and>
        inp!k = a \<and>
        k < length inp \<and>
        next_symbol x = Some a }"

definition Predict :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Predict k cfg I =
    { init_item r k | r x.
        r \<in> set (\<RR> cfg) \<and>
        x \<in> bin I k \<and>
        next_symbol x = Some (rule_head r) }"

definition Complete :: "nat \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Complete k I =
    { inc_item x k | x y.
        x \<in> bin I (item_origin y) \<and>
        y \<in> bin I k \<and>
        is_complete y \<and>
        next_symbol x = Some (item_rule_head y) }"

definition \<pi>_step :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "\<pi>_step k cfg inp I = I \<union> Scan k inp I \<union> Complete k I \<union> Predict k cfg I"

definition \<pi> :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "\<pi> k cfg inp I = limit (\<pi>_step k cfg inp) I"

fun \<I> :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items" where
  "\<I> 0 cfg inp = \<pi> 0 cfg inp (Init cfg)"
| "\<I> (Suc n) cfg inp = \<pi> (Suc n) cfg inp (\<I> n cfg inp)"

definition \<II> :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items" where
  "\<II> cfg inp = \<I> (length inp) cfg inp"

definition is_finished :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item \<Rightarrow> bool" where
  "is_finished cfg inp x \<longleftrightarrow> (
    item_rule_head x = \<SS> cfg \<and>
    item_origin x = 0 \<and>
    item_end x = length inp \<and> 
    is_complete x)"

definition earley_recognized :: "'a items \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "earley_recognized I cfg inp = (\<exists>x \<in> I. is_finished cfg inp x)"


subsection \<open>Wellformedness\<close>

lemma wf_items_Un:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp J \<Longrightarrow> wf_items cfg inp (I \<union> J)"
  unfolding wf_items_def by blast

lemmas wf_defs = wf_item_def wf_items_def

lemma wf_Init:
  "x \<in> Init cfg \<Longrightarrow> wf_item cfg inp x"
  unfolding Init_def wf_item_def init_item_def by auto

lemma wf_Scan:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (Scan k inp I)"
  unfolding Scan_def wf_defs bin_def inc_item_def is_complete_def item_rule_body_def next_symbol_def
  by (auto split: if_splits)

lemma wf_Predict:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (Predict k cfg I)"
  unfolding Predict_def wf_defs bin_def init_item_def by auto

lemma wf_Complete:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (Complete k I)"
  unfolding Complete_def wf_defs bin_def inc_item_def is_complete_def item_rule_body_def next_symbol_def
  by (auto split: if_splits; metis le_trans)

lemma wf_\<pi>_step:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (\<pi>_step k cfg inp I)"
  unfolding \<pi>_step_def using wf_Scan wf_Predict wf_Complete wf_items_Un by metis

lemma wf_funpower:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (funpower (\<pi>_step k cfg inp) n I)"
  using wf_\<pi>_step unfolding wf_items_def
  by (induction n) (auto, blast)

lemma wf_\<pi>:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (\<pi> k cfg inp I)"
  by (metis \<pi>_def elem_limit_simp wf_funpower wf_items_def)

lemma wf_\<pi>0:
  "wf_items cfg inp (\<pi> 0 cfg inp (Init cfg))"
  using wf_items_def wf_Init wf_\<pi> by metis

lemma wf_\<I>:
  "wf_items cfg inp (\<I> n cfg inp)"
  by (induction n) (auto simp: wf_\<pi>0 wf_\<pi>)

lemma wf_\<II>:
  "wf_items cfg inp (\<II> cfg inp)"
  unfolding \<II>_def using wf_\<I> by blast


subsection \<open>Soundness\<close>

definition sound_item :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item \<Rightarrow> bool" where
  "sound_item cfg inp x = derives cfg [item_rule_head x] (slice (item_origin x) (item_end x) inp @ item_\<beta> x)"

definition sound_items :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> bool" where
  "sound_items cfg inp I = (\<forall>x \<in> I. sound_item cfg inp x)"

lemmas sound_defs = sound_items_def sound_item_def

lemma sound_Init:
  "sound_items cfg inp (Init cfg)"
  unfolding sound_items_def
proof (standard)
  fix x
  assume *: "x \<in> Init cfg"
  hence "item_dot x = 0"
    by (smt (verit) Init_def init_item_def item.exhaust_sel item.inject mem_Collect_eq)
  hence "(item_rule_head x, item_\<beta> x) \<in> set (\<RR> cfg)"
    unfolding item_rule_head_def rule_head_def item_\<beta>_def item_rule_body_def rule_body_def
    using * wf_Init wf_item_def by fastforce
  hence "derives cfg [item_rule_head x] (item_\<beta> x)"
    using derives_if_valid_rule by metis
  moreover have "item_origin x = item_end x"
    by (metis * Ex_list_of_length nle_le wf_Init wf_item_def)
  ultimately show "sound_item cfg inp x"
    unfolding sound_item_def by (simp add: slice_empty)
qed

lemma sound_item_inc_item:
  assumes "wf_item cfg inp x" "sound_item cfg inp x"
  assumes "next_symbol x = Some a"
  assumes "k < length inp" "inp!k = a" "item_end x = k"
  shows "sound_item cfg inp (inc_item x (k+1))"
proof -
  define x' where [simp]: "x' = inc_item x (k+1)"
  obtain item_\<beta>' where *: "item_\<beta> x = a # item_\<beta>'"
    using assms(3) apply (auto simp: item_\<beta>_def is_complete_def next_symbol_def split: if_splits)
    by (metis Cons_nth_drop_Suc leI)
  have "slice (item_origin x) (item_end x) inp @ item_\<beta> x = slice (item_origin x') (item_end x') inp @ item_\<beta>'"
    using * assms(1,4-6) slice_append_nth wf_item_def by (auto simp: inc_item_def; blast)
  moreover have "item_\<beta>' = item_\<beta> x'"
    using * by (auto simp: inc_item_def item_\<beta>_def item_rule_body_def, metis List.list.sel(3) drop_Suc tl_drop)
  moreover have "derives cfg [item_rule_head x] (slice (item_origin x) (item_end x) inp @ item_\<beta> x)"
    using assms(1,2,6) sound_item_def by blast
  ultimately show ?thesis
    by (simp add: inc_item_def item_rule_head_def sound_item_def)
qed

lemma sound_Scan:
  "wf_items cfg inp I \<Longrightarrow> sound_items cfg inp I \<Longrightarrow> sound_items cfg inp (Scan k inp I)"
  unfolding Scan_def using sound_item_inc_item by (auto simp: wf_items_def sound_items_def bin_def; fast)

lemma sound_Predict:
  "sound_items cfg inp I \<Longrightarrow> sound_items cfg inp (Predict k cfg I)"
  unfolding Predict_def by (auto simp: sound_defs init_item_def derives_if_valid_rule slice_empty item_defs)

lemma sound_Complete:
  assumes "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (Complete k I)"
  unfolding sound_items_def
proof standard
  fix z
  assume "z \<in> Complete k I"
  show "sound_item cfg inp z"
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

    have "derives cfg [item_rule_head y] (slice (item_origin y) (item_end y) inp)"
      using *(3,4) sound_defs assms
      by (metis (no_types, lifting) append_Nil2 bin_def drop_eq_Nil is_complete_def item_\<beta>_def mem_Collect_eq)
    then obtain E where E: "Derivation cfg [item_rule_head y] E (slice (item_origin y) (item_end y) inp)"
      using derives_implies_Derivation by blast

    have "derives cfg [item_rule_head x] (slice (item_origin x) (item_origin y) inp @ item_\<beta> x)"
      using *(2) sound_defs assms sound_items_def by (metis (mono_tags, lifting) bin_def mem_Collect_eq)
    moreover have 0: "item_\<beta> x = (item_rule_head y) # tl (item_\<beta> x)"
      using *(5) by (auto simp: next_symbol_def item_\<beta>_def is_complete_def split: if_splits,
                     metis Cons_nth_drop_Suc drop_Suc drop_tl leI)
    ultimately obtain D where D: 
      "Derivation cfg [item_rule_head x] D (slice (item_origin x) (item_origin y) inp @
       [item_rule_head y] @ (tl (item_\<beta> x)))"
      using derives_implies_Derivation by (metis append_Cons append_Nil)

    have "wf_item cfg inp x"
      using *(2) assms(1) bin_def wf_items_def by (metis (mono_tags, lifting) mem_Collect_eq)
    obtain G where 
      "Derivation cfg [item_rule_head x] G (slice (item_origin x) (item_origin y) inp @
       slice (item_origin y) (item_end y) inp @ tl (item_\<beta> x))"
      using Derivation_append_rewrite D E by blast
    moreover have "item_origin x \<le> item_origin y"
      using *(2) \<open>wf_item cfg inp x\<close> wf_item_def by (auto simp: bin_def; force)
    moreover have "item_origin y \<le> item_end y"
      using *(3) wf_defs assms(1) by (auto simp: bin_def; blast)
    ultimately have "derives cfg [item_rule_head x] (slice (item_origin x) (item_end y) inp @ tl (item_\<beta> x))"
      by (metis Derivation_implies_derives append.assoc slice_concat)
    moreover have "tl (item_\<beta> x) = item_\<beta> z"
      using *(1,5) 0 by (auto simp: inc_item_def item_rule_body_def tl_drop drop_Suc item_\<beta>_def)
    ultimately show ?thesis
      using sound_item_def *(1,3) by (metis (mono_tags, lifting) bin_def inc_item_def item.sel(1,3,4) item_defs(1) mem_Collect_eq)
  qed
qed

lemma sound_\<pi>_step:
  "wf_items cfg inp I \<Longrightarrow> sound_items cfg inp I \<Longrightarrow> sound_items cfg inp (\<pi>_step k cfg inp I)"
  unfolding \<pi>_step_def using sound_Scan sound_Predict sound_Complete by (metis UnE sound_items_def)

lemma sound_funpower:
  "wf_items cfg inp I \<Longrightarrow> sound_items cfg inp I \<Longrightarrow> sound_items cfg inp (funpower (\<pi>_step k cfg inp) n I)"
  by (induction n) (auto simp: sound_\<pi>_step wf_\<pi>_step wf_funpower)

lemma sound_\<pi>:
  assumes "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (\<pi> k cfg inp I)"
  by (metis \<pi>_def assms elem_limit_simp sound_items_def sound_funpower)

lemma sound_\<pi>0:
  "sound_items cfg inp (\<pi> 0 cfg inp (Init cfg))"
  using sound_Init sound_\<pi> wf_Init wf_items_def by metis

lemma sound_\<I>:
  "sound_items cfg inp (\<I> k cfg inp)"
  apply (induction k)
  apply (auto simp: sound_\<pi>0)
  using sound_\<pi> wf_\<I> by force

lemma sound_\<II>:
  "sound_items cfg inp (\<II> cfg inp)"
  unfolding \<II>_def using sound_\<I> by blast

theorem soundness:
  "earley_recognized (\<II> cfg inp) cfg inp \<Longrightarrow> derives cfg [\<SS> cfg] inp"
  using earley_recognized_def sound_\<II> sound_defs
  by (metis drop_eq_Nil is_complete_def is_finished_def item_\<beta>_def self_append_conv slice_id)


subsection \<open>Monotonicity and Absorption\<close>

lemma \<pi>_step_empty:
  "\<pi>_step k cfg inp {} = {}"
  unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast

lemma \<pi>_step_setmonotone:
  "setmonotone (\<pi>_step k cfg inp)"
  by (simp add: Un_assoc \<pi>_step_def setmonotone_def)

lemma \<pi>_step_continuous:
  "continuous (\<pi>_step k cfg inp)"
  unfolding continuous_def
proof (standard, standard, standard)
  fix C :: "nat \<Rightarrow> 'a item set"
  assume "chain C"
  thus "chain (\<pi>_step k cfg inp \<circ> C)"
    unfolding chain_def \<pi>_step_def by (auto simp: Scan_def Predict_def Complete_def bin_def subset_eq)
next
  fix C :: "nat \<Rightarrow> 'a item set"
  assume *: "chain C"
  show "\<pi>_step k cfg inp (natUnion C) = natUnion (\<pi>_step k cfg inp \<circ> C)"
    unfolding natUnion_def
  proof standard
    show "\<pi>_step k cfg inp (\<Union> {C n |n. True}) \<subseteq> \<Union> {(\<pi>_step k cfg inp \<circ> C) n |n. True}"
    proof standard
      fix x
      assume #: "x \<in> \<pi>_step k cfg inp (\<Union> {C n |n. True})"
      show "x \<in> \<Union> {(\<pi>_step k cfg inp \<circ> C) n |n. True}"
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
                           Scan (item_end z) inp (C n) \<union> 
                           {inc_item i (item_end z) |i. 
                              i \<in> C n \<and> 
                              (\<exists>j. 
                                item_end i = item_origin j \<and>
                                j \<in> C n \<and> 
                                item_end j = item_end z \<and> 
                                is_complete j \<and>
                                next_symbol i = Some (item_rule_head j))} \<union>
                           Predict (item_end z) cfg (C n))
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
    show "\<Union> {(\<pi>_step k cfg inp \<circ> C) n |n. True} \<subseteq> \<pi>_step k cfg inp (\<Union> {C n |n. True})"
      unfolding \<pi>_step_def
      using * by (auto simp: Scan_def Predict_def Complete_def chain_def bin_def, metis+)
  qed
qed

lemma \<pi>_step_regular:
  "regular (\<pi>_step k cfg inp)"
  by (simp add: \<pi>_step_continuous \<pi>_step_setmonotone regular_def)

lemma \<pi>_idem:
  "\<pi> k cfg inp (\<pi> k cfg inp I) = \<pi> k cfg inp I"
  by (simp add: \<pi>_def \<pi>_step_regular limit_is_idempotent)

lemma Scan_bin_absorb:
  "Scan k inp (bin I k) = Scan k inp I"
  unfolding Scan_def bin_def by simp

lemma Predict_bin_absorb:
  "Predict k cfg (bin I k) = Predict k cfg I"
  unfolding Predict_def bin_def by simp

lemma Complete_bin_absorb:
  "Complete k (bin I k) \<subseteq> Complete k I"
  unfolding Complete_def bin_def by blast

lemma Scan_Un:
  "Scan k inp (I \<union> J) = Scan k inp I \<union> Scan k inp J"
  unfolding Scan_def bin_def by blast

lemma Predict_Un:
  "Predict k cfg (I \<union> J) = Predict k cfg I \<union> Predict k cfg J"
  unfolding Predict_def bin_def by blast

lemma Scan_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Scan k inp I \<subseteq> Scan k inp J"
  unfolding Scan_def bin_def by blast

lemma Predict_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Predict k cfg I \<subseteq> Predict k cfg J"
  unfolding Predict_def bin_def by blast

lemma Complete_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Complete k I \<subseteq> Complete k J"
  unfolding Complete_def bin_def by blast

lemma \<pi>_step_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi>_step k cfg inp I \<subseteq> \<pi>_step k cfg inp J"
  unfolding \<pi>_step_def using Scan_sub_mono Predict_sub_mono Complete_sub_mono by (metis sup.mono)

lemma funpower_sub_mono:
  "I \<subseteq> J \<Longrightarrow> funpower (\<pi>_step k cfg inp) n I \<subseteq> funpower (\<pi>_step k cfg inp) n J"
  by (induction n) (auto simp: \<pi>_step_sub_mono)

lemma \<pi>_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi> k cfg inp I \<subseteq> \<pi> k cfg inp J"
proof standard
  fix x
  assume "I \<subseteq> J" "x \<in> \<pi> k cfg inp I"
  then obtain n where "x \<in> funpower (\<pi>_step k cfg inp) n I"
    unfolding \<pi>_def limit_def natUnion_def by blast
  hence "x \<in> funpower (\<pi>_step k cfg inp) n J"
    using \<open>I \<subseteq> J\<close> funpower_sub_mono by blast
  thus "x \<in> \<pi> k cfg inp J"
    unfolding \<pi>_def limit_def natUnion_def by blast
qed

lemma Scan_\<pi>_step_mono:
  "Scan k inp I \<subseteq> \<pi>_step k cfg inp I"
  using \<pi>_step_def by blast

lemma Predict_\<pi>_step_mono:
  "Predict k cfg I \<subseteq> \<pi>_step k cfg inp I"
  using \<pi>_step_def by blast

lemma Complete_\<pi>_step_mono:
  "Complete k I \<subseteq> \<pi>_step k cfg inp I"
  using \<pi>_step_def by blast

lemma \<pi>_step_\<pi>_mono:
  "\<pi>_step k cfg inp I \<subseteq> \<pi> k cfg inp I"
proof -
  have "\<pi>_step k cfg inp I \<subseteq> funpower (\<pi>_step k cfg inp) 1 I"
    by simp
  thus ?thesis
    by (metis \<pi>_def limit_elem subset_eq)
qed

lemma Scan_\<pi>_mono:
  "Scan k inp  I \<subseteq> \<pi> k cfg inp I"
  using Scan_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma Predict_\<pi>_mono:
  "Predict k cfg I \<subseteq> \<pi> k cfg inp I"
  using Predict_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma Complete_\<pi>_mono:
  "Complete k I \<subseteq> \<pi> k cfg inp I"
  using Complete_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma \<pi>_mono:
  "I \<subseteq> \<pi> k cfg inp I"
  using \<pi>_step_\<pi>_mono \<pi>_step_def by blast

lemma Scan_bin_empty:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Scan k inp I) i = {}"
  unfolding Scan_def bin_def inc_item_def by fastforce

lemma Predict_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Predict k cfg I) i = {}"
  unfolding Predict_def bin_def init_item_def by auto

lemma Complete_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Complete k I) i = {}"
  unfolding Complete_def bin_def inc_item_def by auto

lemma \<pi>_step_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k + 1 \<Longrightarrow> bin (\<pi>_step k cfg inp I) i = bin I i"
  unfolding \<pi>_step_def using Scan_bin_empty Predict_bin_empty Complete_bin_empty
  unfolding bin_def using Un_iff empty_iff mem_Collect_eq by fastforce

lemma funpower_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (funpower (\<pi>_step k cfg inp) n I) i = bin I i"
  by (induction n) (auto simp: \<pi>_step_bin_absorb)

lemma \<pi>_bin_absorb:
  assumes "i \<noteq> k" "i \<noteq> k+1" 
  shows "bin (\<pi> k cfg inp I) i = bin I i"
proof (standard; standard)
  fix x 
  assume "x \<in> bin (\<pi> k cfg inp I) i"
  then obtain n where "x \<in> bin (funpower (\<pi>_step k cfg inp) n I) i"
    unfolding \<pi>_def limit_def natUnion_def by (auto simp: bin_def)
  then show "x \<in> bin I i"
    using funpower_bin_absorb assms by blast
next
  fix x
  assume "x \<in> bin I i"
  show "x \<in> bin (\<pi> k cfg inp I) i"
    using \<pi>_mono \<open>x \<in> bin I i\<close> by (metis (no_types, lifting) bin_def mem_Collect_eq subsetD)
qed


subsection \<open>Completeness\<close>

lemma Scan_\<I>:
  assumes "i+1 \<le> k" "k \<le> length inp" "x \<in> bin (\<I> k cfg inp) i" "next_symbol x = Some a" "inp!i = a"
  shows "inc_item x (i+1) \<in> \<I> k cfg inp"
  using assms
proof (induction k arbitrary: i x a)
  case 0
  have False
    using "0.prems"(1) by simp
  thus ?case
    by blast
next
  case (Suc k)
  have "bin (\<I> (k+1) cfg inp) i = bin (\<pi> (k+1) cfg inp (\<I> k cfg inp)) i"
    by simp
  also have "... = bin (\<I> k cfg inp) i"
    using \<pi>_bin_absorb Suc.prems(1) by (metis Suc_eq_plus1 add_le_same_cancel1 not_one_le_zero trans_le_add1)
  finally have "bin (\<I> (k+1) cfg inp) i = bin (\<I> k cfg inp) i" .
  hence *: "x \<in> bin (\<I> k cfg inp) i"
    using Suc.prems(3) by force
  show ?case
  proof cases
    assume "i+1 \<le> k"
    hence "inc_item x (i+1) \<in> \<I> k cfg inp"
      using Suc.IH Suc.prems(2,4,5) * by simp
    thus ?thesis
      using \<pi>_mono by force
  next
    assume "\<not> i+1 \<le> k"
    hence "i = k"
      using Suc.prems(1) by auto
    hence "inc_item x (i+1) \<in> Scan k inp (\<I> k cfg inp)"
      using Suc.prems(2,4,5) * Scan_def by force
    hence "inc_item x (i+1) \<in> \<pi> k cfg inp (\<I> k cfg inp)"
      using Scan_\<pi>_mono by blast
    hence "inc_item x (i+1) \<in> \<I> k cfg inp"
      using \<pi>_idem by (metis \<I>.elims)
    thus ?thesis
      using \<pi>_mono by force
  qed
qed

lemma Predict_\<I>:
  assumes "i \<le> k" "x \<in> bin (\<I> k cfg inp) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set (\<RR> cfg)"
  shows "init_item (N,\<alpha>) i \<in> \<I> k cfg inp"
  using assms
proof (induction k arbitrary: i x N \<alpha>)
  case 0
  hence "init_item (N,\<alpha>) i \<in> Predict 0 cfg (\<I> 0 cfg inp)"
    unfolding rule_head_def Predict_def by auto
  thus ?case
    using Predict_\<pi>_mono \<pi>_idem by fastforce
next
  case (Suc k)
  show ?case
  proof cases
    assume "i \<le> k"
    hence "init_item (N,\<alpha>) i \<in> \<I> k cfg inp"
      using Suc.IH \<pi>_bin_absorb Suc.prems(2-4) by (metis \<I>.simps(2) add.commute le_imp_less_Suc nless_le plus_1_eq_Suc)
    thus ?thesis
      using \<pi>_mono by fastforce
  next
    assume "\<not> i \<le> k"
    hence "init_item (N,\<alpha>) i \<in> Predict i cfg (\<I> (Suc k) cfg inp)"
      unfolding Predict_def rule_head_def using Suc.prems(2-4) by auto
    thus ?thesis
      using Predict_\<pi>_mono \<pi>_idem Suc.prems(1) \<open>\<not> i \<le> k\<close> by (metis le_SucE \<I>.simps(2) subsetD)
  qed
qed

lemma Complete_\<I>:
  assumes "i \<le> j" "j \<le> k" "x \<in> bin (\<I> k cfg inp) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set (\<RR> cfg)"
  assumes "i = item_origin y" "y \<in> bin (\<I> k cfg inp) j" "item_rule y = (N,\<alpha>)" "is_complete y"
  shows "inc_item x j \<in> \<I> k cfg inp"
  using assms
proof (induction k arbitrary: i j x N \<alpha> y)
  case 0
  hence "inc_item x 0 \<in> Complete 0 (\<I> 0 cfg inp)"
    unfolding Complete_def rule_head_def next_symbol_def item_rule_head_def by (auto split: if_splits; force)
  thus ?case
    using Complete_\<pi>_mono \<pi>_idem "0.prems"(2) by (metis le_0_eq \<I>.simps(1) subset_iff)
next
  case (Suc k)
  show ?case
  proof cases
    assume "j \<le> k"
    hence "inc_item x j \<in> \<I> k cfg inp"
      using Suc  \<pi>_bin_absorb Orderings.order_class.dual_order.eq_iff by (metis Suc_eq_plus1 \<I>.simps(2) not_less_eq_eq)
    thus ?thesis
      using \<pi>_mono by fastforce
  next
    assume "\<not> j \<le> k"
    hence "j = Suc k"
      using le_SucE Suc.prems(2) by blast
    hence "inc_item x (Suc k) \<in> Complete (Suc k) (\<I> (Suc k) cfg inp)"
      using Suc.prems(3-4,6-9) unfolding Complete_def rule_head_def item_rule_head_def by fastforce
    then show ?thesis
      using Complete_\<pi>_mono \<pi>_idem \<open>j = Suc k\<close> by fastforce
  qed
qed

definition partially_completed :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> ('a derivation \<Rightarrow> bool) \<Rightarrow> bool" where
  "partially_completed k cfg inp I P = (
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length inp \<and>
      x \<in> bin I i \<and> next_symbol x = Some a \<and>
      Derivation cfg [a] D (slice i j inp) \<and> P D \<longrightarrow>
      inc_item x j \<in> I
  )"

lemma fully_completed:
  assumes "j \<le> k" "k \<le> length inp"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> I" "wf_items cfg inp I"
  assumes "Derivation cfg (item_\<beta> x) D (slice j k inp)"
  assumes "partially_completed k cfg inp I (\<lambda>D'. length D' \<le> length D)"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> I"
  using assms
proof (induction "item_\<beta> x" arbitrary: d i j k N \<alpha> x D)
  case Nil
  have "item_\<alpha> x = \<alpha>"
    using Nil(1,4) unfolding item_\<alpha>_def item_\<beta>_def item_rule_body_def rule_body_def by simp
  hence "x = Item (N,\<alpha>) (length \<alpha>) i j"
    using Nil.hyps Nil.prems(3,4,5)
    unfolding wf_items_def wf_item_def rule_body_def item_rule_body_def item_defs(4) by auto
  have "Derivation cfg [] D (slice j k inp)"
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
    "Derivation cfg [b] E (slice j j' inp)"
    "Derivation cfg bs F (slice j' k inp)"
    "j \<le> j'" "j' \<le> k" "length E \<le> length D" "length F \<le> length D"
    using Derivation_concat_split[of cfg "[b]" bs D "slice j k inp"] slice_concat_Ex
    by (metis append_Cons append_Nil Cons.prems(1))
  have "x \<in> bin I j"
    using Cons.prems(3,4) by (auto simp: bin_def)
  moreover have "next_symbol x = Some b"
    using Cons unfolding item_defs(4) next_symbol_def is_complete_def by (auto, metis nth_via_drop)
  ultimately have "inc_item x j' \<in> I"
    using *(1,3-5) Cons.prems(2-4,7) partially_completed_def by metis
  moreover have "partially_completed k cfg inp I (\<lambda>D'. length D' \<le> length F)"
    using Cons.prems(7) *(6) unfolding partially_completed_def by fastforce
  moreover have "bs = item_\<beta> (Item (N,\<alpha>) (d+1) i j')"
    using Cons.hyps(2) Cons.prems(3) unfolding item_defs(4) item_rule_body_def 
    by (auto, metis List.list.sel(3) drop_Suc drop_tl)
  ultimately show ?case
    using Cons.hyps(1) *(2,4) Cons.prems(2,3,5) wf_items_def by (auto simp: inc_item_def)
qed

lemma partially_completed_\<I>:
  assumes "wf_cfg cfg"
  shows "partially_completed k cfg inp (\<I> k cfg inp) (\<lambda>_. True)"
  unfolding partially_completed_def
proof (standard, standard, standard, standard, standard, standard)
  fix x i a D j
  assume
    "i \<le> j \<and> j \<le> k \<and> k \<le> length inp \<and>
     x \<in> bin (\<I> k cfg inp) i \<and> next_symbol x = Some a \<and>
     Derivation cfg [a] D (slice i j inp) \<and> (\<lambda>_. True) D"
  thus "inc_item x j \<in> \<I> k cfg inp"
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
      hence "inc_item x (i+1) \<in> \<I> k cfg inp"
        using Scan_\<I> \<open>j = i + 1\<close> "1.prems" by fast
      thus ?thesis
        by (simp add: \<open>j = i + 1\<close> wf_Init wf_items_def)
    next
      assume "\<not> D = []"
      then obtain d D' where "D = d # D'"
        by (meson List.list.exhaust)
      then obtain b where *: "Derives1 cfg [a] (fst d) (snd d) b" "Derivation cfg b D' (slice i j inp)"
        using "1.prems" by auto
      show ?thesis
      proof cases
        assume "is_terminal cfg a"
        then obtain N \<alpha> where "[a] = [N]" "(N,\<alpha>) \<in> set (\<RR> cfg)"
          using *(1) unfolding Derives1_def by (metis Cons_eq_append_conv neq_Nil_conv)
         hence "is_nonterminal cfg a"
           by (simp add: assms)
         thus ?thesis
          using \<open>is_terminal cfg a\<close> is_terminal_nonterminal by (metis assms)
      next
        assume "\<not> is_terminal cfg a"
        then obtain N \<alpha> where #: "[a] = [N]" "b = \<alpha>" "(N,\<alpha>) \<in> set (\<RR> cfg)" "fst d = 0" "snd d = (N,\<alpha>)"
          using *(1) unfolding Derives1_def by (simp add: Cons_eq_append_conv)
        define y where y_def: "y = Item (N,\<alpha>) 0 i i"
        have "init_item (N, \<alpha>) i \<in> \<I> k cfg inp"
          using Predict_\<I> #(1,3) "1.prems" by (metis (no_types, lifting) le_trans list.inject)
        hence "y \<in> bin (\<I> k cfg inp) i"
          unfolding init_item_def using y_def by (simp add: bin_def wf_Init wf_items_def)
        have "length D' < length D"
          using \<open>D = d # D'\<close> by fastforce
        hence "partially_completed k cfg inp (\<I> k cfg inp) (\<lambda>E. length E \<le> length D')"
          unfolding partially_completed_def using "1.hyps" "1.prems" le_less_trans by blast
        hence "partially_completed j cfg inp (\<I> k cfg inp) (\<lambda>E. length E \<le> length D')"
          unfolding partially_completed_def using "1.prems" by force
        moreover have "Derivation cfg (item_\<beta> y) D' (slice i j inp)"
          using #(2) *(2) item_\<beta>_def item_rule_body_def rule_body_def y_def
          by (metis item.sel(1) item.sel(2) drop0 snd_conv)
        ultimately have 0: "Item (N,\<alpha>) (length \<alpha>) i j \<in> bin (\<I> k cfg inp) j"
          using fully_completed wf_\<I> "1.prems" wf_items_def \<open>y \<in> bin (\<I> k cfg inp) i\<close>
          apply (auto simp: bin_def y_def)
          using fully_completed le_trans partially_completed_def by (smt (verit, best) wf_\<I>)
        have 1: "x \<in> bin (\<I> k cfg inp) i"
          by (simp add: "1.prems")
        have "next_symbol x = Some N"
          using #(1) "1.prems" by fastforce
        thus ?thesis
          using "1.prems" Complete_\<I>[OF _ _ 1 _ _ _ 0] #(3) by (auto simp: is_complete_def item_rule_body_def rule_body_def)
      qed
    qed
  qed
qed

lemma partially_completed_\<II>:
  "wf_cfg cfg \<Longrightarrow> partially_completed (length inp) cfg inp (\<II> cfg inp) (\<lambda>_. True)"
  by (simp add: \<II>_def partially_completed_\<I>)

lemma Init_sub_\<I>:
  "Init cfg \<subseteq> \<I> k cfg inp"
  using \<pi>_mono by (induction k) (auto, blast, blast)

lemma Derivation_\<SS>1:
  assumes "Derivation cfg [\<SS> cfg] D inp" "is_word cfg inp" "wf_cfg cfg"
  shows "\<exists>\<alpha> E. Derivation cfg \<alpha> E inp \<and> (\<SS> cfg,\<alpha>) \<in> set (\<RR> cfg)"
proof (cases D)
  case Nil
  thus ?thesis
    using assms is_nonterminal_startsymbol is_terminal_nonterminal by (metis Derivation.simps(1) is_word_def list.set_intros(1))
next
  case (Cons d D)
  then obtain \<alpha> where "Derives1 cfg [\<SS> cfg] (fst d) (snd d) \<alpha>" "Derivation cfg \<alpha> D inp"
    using assms by auto
  hence "(\<SS> cfg, \<alpha>) \<in> set (\<RR> cfg)"
    unfolding Derives1_def
    by (metis List.append.right_neutral List.list.discI append_eq_Cons_conv append_is_Nil_conv nth_Cons_0 self_append_conv2)
  thus ?thesis
    using \<open>Derivation cfg \<alpha> D inp\<close> by auto
qed

theorem completeness:
  assumes "derives cfg [\<SS> cfg] inp" "is_word cfg inp" "wf_cfg cfg"
  shows "earley_recognized (\<II> cfg inp) cfg inp"
proof -
  obtain \<alpha> where *: "(\<SS> cfg,\<alpha>) \<in> set (\<RR> cfg)" "derives cfg \<alpha> inp"
    using Derivation_\<SS>1 assms Derivation_implies_derives derives_implies_Derivation by metis
  let ?x = "Item (\<SS> cfg,\<alpha>) 0 0 0"
  have "?x \<in> \<II> cfg inp" "wf_item cfg inp ?x"
    unfolding \<II>_def using *(1) Init_sub_\<I> Init_def wf_Init by (auto simp: init_item_def, fast, fast)
  moreover have "derives cfg (item_\<beta> ?x) inp"
    using *(2) item_defs(4) by (simp add: item_\<beta>_def item_rule_body_def rule_body_def)
  ultimately have "Item (\<SS> cfg,\<alpha>) (length \<alpha>) 0 (length inp) \<in> \<II> cfg inp"
    using partially_completed_\<II> fully_completed wf_\<II> derives_implies_Derivation assms slice_id
      slice_empty wf_item_def partially_completed_def
    by (smt (verit, ccfv_SIG) item.sel(4) nat_le_linear)
  then show ?thesis
    unfolding earley_recognized_def is_finished_def by (auto simp: is_complete_def item_defs, force)
qed

subsection \<open>Correctness\<close>

corollary correctness_set:
  assumes "wf_cfg cfg" "is_word cfg inp"
  shows "earley_recognized (\<II> cfg inp) cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
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
  "finite (\<II> cfg inp)"
  using finiteness_UNIV_wf_item wf_items_def wf_\<II> rev_finite_subset by (metis mem_Collect_eq subsetI)


end
theory Earley_Set
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

section \<open>Additional Derivation Lemmas\<close>

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


subsection \<open>Earley algorithm\<close>

definition Init :: "'a items" where
  "Init = { init_item r 0 | r. r \<in> set \<RR> \<and> fst r = \<SS> }"

definition Scan :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Scan k inp I = 
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

definition \<pi>_step :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "\<pi>_step k inp I = I \<union> Scan k inp I \<union> Complete k I \<union> Predict k I"

definition \<pi> :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "\<pi> k inp I = limit (\<pi>_step k inp) I"

fun \<I> :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a items" where
  "\<I> 0 inp = \<pi> 0 inp Init"
| "\<I> (Suc n) inp = \<pi> (Suc n) inp (\<I> n inp)"

definition \<II> :: "'a sentence \<Rightarrow> 'a items" where
  "\<II> inp = \<I> (length inp) inp"

definition is_finished :: "'a sentence \<Rightarrow> 'a item \<Rightarrow> bool" where
  "is_finished inp x \<longleftrightarrow> (
    item_rule_head x = \<SS> \<and>
    item_origin x = 0 \<and>
    item_end x = length inp \<and> 
    is_complete x)"

definition earley_recognized :: "'a sentence \<Rightarrow> bool" where
  "earley_recognized inp = (\<exists>x \<in> \<II> inp. is_finished inp x)"

subsection \<open>Wellformedness\<close>

lemma wf_items_Un:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp J \<Longrightarrow> wf_items \<RR> inp (I \<union> J)"
  unfolding wf_items_def by blast

lemmas wf_defs = wf_item_def wf_items_def

lemma wf_Init:
  "x \<in> Init \<Longrightarrow> wf_item \<RR> inp x"
  unfolding Init_def wf_item_def init_item_def by auto

lemma wf_Scan:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (Scan k inp I)"
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
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (\<pi>_step k inp I)"
  unfolding \<pi>_step_def using wf_Scan wf_Predict wf_Complete wf_items_Un by simp

lemma wf_funpower:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (funpower (\<pi>_step k inp) n I)"
  using wf_\<pi>_step unfolding wf_items_def
  by (induction n) auto

lemma wf_\<pi>:
  "wf_items \<RR> inp I \<Longrightarrow> wf_items \<RR> inp (\<pi> k inp I)"
  by (metis \<pi>_def elem_limit_simp wf_funpower wf_items_def)

lemma wf_\<pi>0:
  "wf_items \<RR> inp (\<pi> 0 inp Init)"
  using wf_items_def wf_Init wf_\<pi> by metis

lemma wf_\<I>:
  "wf_items \<RR> inp (\<I> n inp)"
  by (induction n) (auto simp: wf_\<pi>0 wf_\<pi>)

lemma wf_\<II>:
  "wf_items \<RR> inp (\<II> inp)"
  unfolding \<II>_def using wf_\<I> by blast

subsection \<open>Soundness\<close>

definition sound_item :: "'a sentence \<Rightarrow> 'a item \<Rightarrow> bool" where
  "sound_item inp x = derives [item_rule_head x] (slice (item_origin x) (item_end x) inp @ item_\<beta> x)"

definition sound_items :: "'a sentence \<Rightarrow> 'a items \<Rightarrow> bool" where
  "sound_items inp I = (\<forall>x \<in> I. sound_item inp x)"

lemmas sound_defs = sound_items_def sound_item_def

lemma sound_Init:
  "sound_items inp Init"
  unfolding sound_items_def
proof (standard)
  fix x
  assume *: "x \<in> Init"
  hence "item_dot x = 0"
    using Init_def by (auto, simp add: init_item_def)
  hence "(item_rule_head x, item_\<beta> x) \<in> set \<RR>"
    unfolding item_rule_head_def rule_head_def item_\<beta>_def item_rule_body_def rule_body_def
    using * wf_Init wf_item_def by fastforce
  hence "derives [item_rule_head x] (item_\<beta> x)"
    using derives_if_valid_rule by blast
  moreover have "item_origin x = item_end x"
    using * Init_def by (auto, simp add: init_item_def)
  ultimately show "sound_item inp x"
    unfolding sound_item_def by (simp add: slice_empty)
qed

lemma sound_item_inc_item:
  assumes "wf_item \<RR> inp x" "sound_item inp x"
  assumes "next_symbol x = Some a"
  assumes "k < length inp" "inp!k = a" "item_end x = k"
  shows "sound_item inp (inc_item x (k+1))"
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
  "wf_items \<RR> inp I \<Longrightarrow> sound_items inp I \<Longrightarrow> sound_items inp (Scan k inp I)"
  unfolding Scan_def using sound_item_inc_item by (auto simp: wf_items_def sound_items_def bin_def)

lemma sound_Predict:
  "sound_items inp I \<Longrightarrow> sound_items inp (Predict k I)"
  unfolding Predict_def by (auto simp: sound_defs init_item_def derives_if_valid_rule slice_empty item_defs)

lemma sound_Complete:
  assumes "wf_items \<RR> inp I" "sound_items inp I"
  shows "sound_items inp (Complete k I)"
  unfolding sound_items_def
proof standard
  fix z
  assume "z \<in> Complete k I"
  show "sound_item inp z"
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
  "wf_items \<RR> inp I \<Longrightarrow> sound_items inp I \<Longrightarrow> sound_items inp (\<pi>_step k inp I)"
  unfolding \<pi>_step_def using sound_Scan sound_Predict sound_Complete by (metis UnE sound_items_def)

lemma sound_funpower:
  "wf_items \<RR> inp I \<Longrightarrow> sound_items inp I \<Longrightarrow> sound_items inp (funpower (\<pi>_step k inp) n I)"
  by (induction n) (auto simp: sound_\<pi>_step wf_\<pi>_step wf_funpower)

lemma sound_\<pi>:
  assumes "wf_items \<RR> inp I" "sound_items inp I"
  shows "sound_items inp (\<pi> k inp I)"
  by (metis \<pi>_def assms elem_limit_simp sound_items_def sound_funpower)

lemma sound_\<pi>0:
  "sound_items inp (\<pi> 0 inp Init)"
  using sound_items_def sound_Init sound_\<pi> wf_Init wf_items_def by metis

lemma sound_\<I>:
  "sound_items inp (\<I> k inp)"
  apply (induction k)
  apply (auto simp: sound_\<pi>0)
  using sound_\<pi> wf_\<I> by force

lemma sound_\<II>:
  "sound_items inp (\<II> inp)"
  unfolding \<II>_def using sound_\<I> by blast

theorem soundness:
  "earley_recognized inp \<Longrightarrow> derives [\<SS>] inp"
  using earley_recognized_def sound_\<II> sound_defs
  apply (auto simp: is_complete_def is_finished_def item_\<beta>_def)
  by (metis drop_all self_append_conv slice_id)

subsection \<open>Monotonicity and Absorption\<close>

lemma \<pi>_step_empty:
  "\<pi>_step k inp {} = {}"
  unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast

lemma \<pi>_step_setmonotone:
  "setmonotone (\<pi>_step k inp)"
  by (simp add: Un_assoc \<pi>_step_def setmonotone_def)

lemma \<pi>_step_continuous:
  "continuous (\<pi>_step k inp)"
  unfolding continuous_def
proof (standard, standard, standard)
  fix C :: "nat \<Rightarrow> 'a item set"
  assume "chain C"
  thus "chain (\<pi>_step k inp \<circ> C)"
    unfolding chain_def \<pi>_step_def by (auto simp: Scan_def Predict_def Complete_def bin_def subset_eq)
next
  fix C :: "nat \<Rightarrow> 'a item set"
  assume *: "chain C"
  show "\<pi>_step k inp (natUnion C) = natUnion (\<pi>_step k inp \<circ> C)"
    unfolding natUnion_def
  proof standard
    show "\<pi>_step k inp (\<Union> {C n |n. True}) \<subseteq> \<Union> {(\<pi>_step k inp \<circ> C) n |n. True}"
    proof standard
      fix x
      assume #: "x \<in> \<pi>_step k inp (\<Union> {C n |n. True})"
      show "x \<in> \<Union> {(\<pi>_step k inp \<circ> C) n |n. True}"
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
    show "\<Union> {(\<pi>_step k inp \<circ> C) n |n. True} \<subseteq> \<pi>_step k inp (\<Union> {C n |n. True})"
      unfolding \<pi>_step_def
      using * by (auto simp: Scan_def Predict_def Complete_def chain_def bin_def, metis+)
  qed
qed

lemma \<pi>_step_regular:
  "regular (\<pi>_step k inp)"
  by (simp add: \<pi>_step_continuous \<pi>_step_setmonotone regular_def)

lemma \<pi>_idem:
  "\<pi> k inp (\<pi> k inp I) = \<pi> k inp I"
  by (simp add: \<pi>_def \<pi>_step_regular limit_is_idempotent)

lemma Scan_bin_absorb:
  "Scan k inp (bin I k) = Scan k inp I"
  unfolding Scan_def bin_def by simp

lemma Predict_bin_absorb:
  "Predict k (bin I k) = Predict k I"
  unfolding Predict_def bin_def by simp

lemma Complete_bin_absorb:
  "Complete k (bin I k) \<subseteq> Complete k I"
  unfolding Complete_def bin_def by blast

lemma Scan_Un:
  "Scan k inp (I \<union> J) = Scan k inp I \<union> Scan k inp J"
  unfolding Scan_def bin_def by blast

lemma Predict_Un:
  "Predict k (I \<union> J) = Predict k I \<union> Predict k J"
  unfolding Predict_def bin_def by blast

lemma Scan_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Scan k inp I \<subseteq> Scan k inp J"
  unfolding Scan_def bin_def by blast

lemma Predict_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Predict k I \<subseteq> Predict k J"
  unfolding Predict_def bin_def by blast

lemma Complete_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Complete k I \<subseteq> Complete k J"
  unfolding Complete_def bin_def by blast

lemma \<pi>_step_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi>_step k inp I \<subseteq> \<pi>_step k inp J"
  unfolding \<pi>_step_def using Scan_sub_mono Predict_sub_mono Complete_sub_mono by (meson Un_mono)

lemma funpower_sub_mono:
  "I \<subseteq> J \<Longrightarrow> funpower (\<pi>_step k inp) n I \<subseteq> funpower (\<pi>_step k inp) n J"
  by (induction n) (auto simp: \<pi>_step_sub_mono)

lemma \<pi>_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi> k inp I \<subseteq> \<pi> k inp J"
proof standard
  fix x
  assume "I \<subseteq> J" "x \<in> \<pi> k inp I"
  then obtain n where "x \<in> funpower (\<pi>_step k inp) n I"
    unfolding \<pi>_def limit_def natUnion_def by blast
  hence "x \<in> funpower (\<pi>_step k inp) n J"
    using \<open>I \<subseteq> J\<close> funpower_sub_mono by blast
  thus "x \<in> \<pi> k inp J"
    unfolding \<pi>_def limit_def natUnion_def by blast
qed

lemma Scan_\<pi>_step_mono:
  "Scan k inp I \<subseteq> \<pi>_step k inp I"
  using \<pi>_step_def by auto

lemma Predict_\<pi>_step_mono:
  "Predict k I \<subseteq> \<pi>_step k inp I"
  using \<pi>_step_def by auto

lemma Complete_\<pi>_step_mono:
  "Complete k I \<subseteq> \<pi>_step k inp I"
  using \<pi>_step_def by auto

lemma \<pi>_step_\<pi>_mono:
  "\<pi>_step k inp I \<subseteq> \<pi> k inp I"
proof -
  have "\<pi>_step k inp I \<subseteq> funpower (\<pi>_step k inp) 1 I"
    by simp
  thus ?thesis
    by (metis \<pi>_def limit_elem subset_eq)
qed

lemma Scan_\<pi>_mono:
  "Scan k inp  I \<subseteq> \<pi> k inp I"
  using Scan_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma Predict_\<pi>_mono:
  "Predict k I \<subseteq> \<pi> k inp I"
  using Predict_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma Complete_\<pi>_mono:
  "Complete k I \<subseteq> \<pi> k inp I"
  using Complete_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma \<pi>_mono:
  "I \<subseteq> \<pi> k inp I"
  using \<pi>_step_\<pi>_mono \<pi>_step_def by auto

lemma Scan_bin_empty:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Scan k inp I) i = {}"
  unfolding Scan_def bin_def inc_item_def by fastforce

lemma Predict_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Predict k I) i = {}"
  unfolding Predict_def bin_def init_item_def by auto

lemma Complete_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Complete k I) i = {}"
  unfolding Complete_def bin_def inc_item_def by auto

lemma \<pi>_step_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k + 1 \<Longrightarrow> bin (\<pi>_step k inp I) i = bin I i"
  unfolding \<pi>_step_def using Scan_bin_empty Predict_bin_empty Complete_bin_empty
  unfolding bin_def using Un_iff empty_iff mem_Collect_eq by fastforce

lemma funpower_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (funpower (\<pi>_step k inp) n I) i = bin I i"
  by (induction n) (auto simp: \<pi>_step_bin_absorb)

lemma \<pi>_bin_absorb:
  assumes "i \<noteq> k" "i \<noteq> k+1" 
  shows "bin (\<pi> k inp I) i = bin I i"
proof (standard; standard)
  fix x 
  assume "x \<in> bin (\<pi> k inp I) i"
  then obtain n where "x \<in> bin (funpower (\<pi>_step k inp) n I) i"
    unfolding \<pi>_def limit_def natUnion_def by (auto simp: bin_def)
  then show "x \<in> bin I i"
    using funpower_bin_absorb assms by blast
next
  fix x
  assume "x \<in> bin I i"
  show "x \<in> bin (\<pi> k inp I) i"
    using \<pi>_mono \<open>x \<in> bin I i\<close> by (auto simp: bin_def)
qed

subsection \<open>Completeness\<close>

lemma Scan_\<I>:
  assumes "i+1 \<le> k" "k \<le> length inp" "x \<in> bin (\<I> k inp) i" "next_symbol x = Some a" "inp!i = a"
  shows "inc_item x (i+1) \<in> \<I> k inp"
  using assms
proof (induction k arbitrary: i x a)
  case (Suc k)
  show ?case
  proof cases
    assume "i+1 \<le> k"
    hence "inc_item x (i+1) \<in> \<I> k inp"
      using Suc \<pi>_bin_absorb by simp
    thus ?thesis
      using \<pi>_mono unfolding Scan_def by force
  next
    assume "\<not> i+1 \<le> k"
    hence *: "i+1 = Suc k"
      using le_Suc_eq Suc.prems(1) by blast
    have "x \<in> bin (\<I> k inp) i"
      using Suc.prems(3) * \<pi>_bin_absorb by force
    hence "inc_item x (i+1) \<in> \<pi> i inp (\<I> k inp)"
      using * Suc.prems(2,4,5) Scan_\<pi>_mono unfolding Scan_def by force
    hence "inc_item x (i+1) \<in> \<pi> k inp (\<I> k inp)"
      using * by force
    hence "inc_item x (i+1) \<in> \<I> k inp"
      using \<pi>_idem by (metis local.\<I>.elims)
    thus ?thesis
      using \<pi>_mono by auto
  qed
qed simp

lemma Predict_\<I>:
  assumes "i \<le> k" "x \<in> bin (\<I> k inp) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set \<RR>"
  shows "init_item (N,\<alpha>) i \<in> \<I> k inp"
  using assms
proof (induction k arbitrary: i x N \<alpha>)
  case 0
  hence "init_item (N,\<alpha>) i \<in> Predict 0 (\<I> 0 inp)"
    unfolding rule_head_def Predict_def by auto
  thus ?case
    using Predict_\<pi>_mono \<pi>_idem by fastforce
next
  case (Suc k)
  show ?case
  proof cases
    assume "i \<le> k"
    hence "init_item (N,\<alpha>) i \<in> \<I> k inp"
      using Suc.IH \<pi>_bin_absorb Suc.prems(2-4) by force
    thus ?thesis
      using \<pi>_mono by auto
  next
    assume "\<not> i \<le> k"
    hence "init_item (N,\<alpha>) i \<in> Predict i (\<I> (Suc k) inp)"
      unfolding Predict_def rule_head_def using Suc.prems(2-4) by auto
    thus ?thesis
      using Predict_\<pi>_mono \<pi>_idem Suc.prems(1) \<open>\<not> i \<le> k\<close> by (metis le_SucE \<I>.simps(2) subsetD)
  qed
qed

lemma Complete_\<I>:
  assumes "i \<le> j" "j \<le> k" "x \<in> bin (\<I> k inp) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set \<RR>"
  assumes "i = item_origin y" "y \<in> bin (\<I> k inp) j" "item_rule y = (N,\<alpha>)" "is_complete y"
  shows "inc_item x j \<in> \<I> k inp"
  using assms
proof (induction k arbitrary: i j x N \<alpha> y)
  case 0
  hence "inc_item x 0 \<in> Complete 0 (\<I> 0 inp)"
    unfolding Complete_def rule_head_def next_symbol_def item_rule_head_def by (auto split: if_splits; force)
  thus ?case
    using Complete_\<pi>_mono \<pi>_idem "0.prems"(2) by (metis le_0_eq \<I>.simps(1) subset_iff)
next
  case (Suc k)
  show ?case
  proof cases
    assume "j \<le> k"
    hence "inc_item x j \<in> \<I> k inp"
      using Suc  \<pi>_bin_absorb Orderings.order_class.dual_order.eq_iff by force
    thus ?thesis
      using \<pi>_mono by fastforce
  next
    assume "\<not> j \<le> k"
    hence "j = Suc k"
      using le_SucE Suc.prems(2) by blast
    hence "inc_item x (Suc k) \<in> Complete (Suc k) (\<I> (Suc k) inp)"
      using Suc.prems(3-4,6-9) unfolding Complete_def rule_head_def item_rule_head_def by fastforce
    then show ?thesis
      using Complete_\<pi>_mono \<pi>_idem \<open>j = Suc k\<close> by fastforce
  qed
qed

definition partially_complete :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> ('a derivation \<Rightarrow> bool) \<Rightarrow> bool" where
  "partially_complete k inp I P = (
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
  assumes "partially_complete k inp I (\<lambda>D'. length D' \<le> length D)"
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
  moreover have "partially_complete k inp I (\<lambda>D'. length D' \<le> length F)"
    using Cons.prems(7) *(6) unfolding partially_complete_def by fastforce
  moreover have "bs = item_\<beta> (Item (N,\<alpha>) (d+1) i j')"
    using Cons.hyps(2) Cons.prems(3) unfolding item_defs(4) item_rule_body_def 
    by (auto, metis List.list.sel(3) drop_Suc drop_tl)
  ultimately show ?case
    using Cons.hyps(1) *(2,4) Cons.prems(2,3,5) wf_items_def by (auto simp: inc_item_def)
qed

lemma partially_complete_\<I>:
  "partially_complete k inp (\<I> k inp) (\<lambda>_. True)"
  unfolding partially_complete_def
proof (standard, standard, standard, standard, standard, standard)
  fix x i a D j
  assume
    "i \<le> j \<and> j \<le> k \<and> k \<le> length inp \<and>
     x \<in> bin (\<I> k inp) i \<and> next_symbol x = Some a \<and>
     Derivation [a] D (slice i j inp) \<and> (\<lambda>_. True) D"
  thus "inc_item x j \<in> \<I> k inp"
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
      hence "inc_item x (i+1) \<in> \<I> k inp"
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
        have "init_item (N, \<alpha>) i \<in> \<I> k inp"
          using Predict_\<I> #(1,3) "1.prems" by auto
        hence "y \<in> bin (\<I> k inp) i"
          unfolding init_item_def using y_def by (simp add: bin_def wf_Init wf_items_def)
        have "length D' < length D"
          using \<open>D = d # D'\<close> by fastforce
        hence "partially_complete k inp (\<I> k inp) (\<lambda>E. length E \<le> length D')"
          unfolding partially_complete_def using "1.hyps" "1.prems" le_less_trans by blast
        hence "partially_complete j inp (\<I> k inp) (\<lambda>E. length E \<le> length D')"
          unfolding partially_complete_def using "1.prems" by force
        moreover have "Derivation (item_\<beta> y) D' (slice i j inp)"
          using #(2) *(2) item_\<beta>_def item_rule_body_def rule_body_def y_def
          by (metis item.sel(1) item.sel(2) drop0 snd_conv)
        ultimately have 0: "Item (N,\<alpha>) (length \<alpha>) i j \<in> bin (\<I> k inp) j"
          using fully_complete wf_\<I> "1.prems" wf_items_def \<open>y \<in> bin (\<I> k inp) i\<close>
          apply (auto simp: bin_def y_def)
          by (smt (verit, best) fully_complete le_trans partially_complete_def)
        have 1: "x \<in> bin (\<I> k inp) i"
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
  "partially_complete (length inp) inp (\<II> inp) (\<lambda>_. True)"
  by (simp add: \<II>_def partially_complete_\<I>)

lemma Init_sub_\<I>:
  "Init \<subseteq> \<I> k inp"
  using \<pi>_mono by (induction k) (auto, blast)

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
  shows "earley_recognized inp"
proof -
  obtain \<alpha> where *: "(\<SS>,\<alpha>) \<in> set \<RR>" "derives \<alpha> inp"
    using Derivation_\<SS>1 assms Derivation_implies_derives derives_implies_Derivation by blast
  let ?x = "Item (\<SS>,\<alpha>) 0 0 0"
  have "?x \<in> \<II> inp" "wf_item \<RR> inp ?x"
    unfolding \<II>_def using *(1) Init_sub_\<I> Init_def wf_Init by (auto simp: init_item_def)
  moreover have "derives (item_\<beta> ?x) (slice 0 (length inp) inp)"
    using *(2) item_defs(4) by (simp add: item_\<beta>_def item_rule_body_def rule_body_def)
  ultimately have "Item (\<SS>,\<alpha>) (length \<alpha>) 0 (length inp) \<in> \<II> inp"
    using partially_complete_\<II> fully_complete unfolding partially_complete_def 
    using fully_complete wf_\<II> derives_implies_Derivation
    by (auto, metis Earley_Set.item.sel(4) le_refl slice_id wf_defs(1))
  then show ?thesis
    unfolding earley_recognized_def is_finished_def by (auto simp: is_complete_def item_defs, force)
qed

subsection \<open>Correctness\<close>

corollary correctness:
  assumes "set inp \<subseteq> set \<TT>"
  shows "earley_recognized inp \<longleftrightarrow> derives [\<SS>] inp"
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
  "finite (\<II> inp)"
  using finiteness_UNIV_wf_item wf_items_def wf_\<II> rev_finite_subset by (metis mem_Collect_eq subsetI)

end

end
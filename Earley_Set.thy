theory Earley_Set
  imports
    LocalLexing.Limit
    LocalLexing.CFG
    LocalLexing.Derivations
    "HOL-Library.While_Combinator" \<comment>\<open>TODO: Use?\<close>
begin

declare [[names_short]]

section \<open>Auxiliary lemmas\<close>

lemma (in CFG) is_sentence_simp:
  "is_sentence s \<longleftrightarrow> (\<forall>x \<in> set s. is_symbol x)"
  unfolding is_sentence_def by (simp add: list_all_iff)

lemma (in CFG) is_word_simp:
  "is_word s \<longleftrightarrow> (\<forall>x \<in> set s. is_terminal x)"
  unfolding is_word_def by (simp add: list_all_iff)

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
  by (induction a b xs rule: slice.induct) (auto simp: slice_drop_take, metis List.list.size(3) le_zero_eq take_eq_Nil)

lemma slice_shift:
  "slice (a+i) (b+i) xs = slice a b (slice i (length xs) xs)"
  unfolding slice_drop_take by (simp add: drop_take)

section \<open>Derivations\<close>

context CFG
begin

lemma Derives1_prepend:
  assumes "Derives1 u i r v" "is_sentence w"
  shows "Derives1 (w@u) (i + length w) r (w@v)"
proof -
  obtain x y N \<alpha> where *:
    "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
    "is_sentence x" "is_sentence y"
    "(N, \<alpha>) \<in> \<RR>" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by blast
  hence "w@u = w @ x @ [N] @ y" "w@v = w @ x @ \<alpha> @ y" "is_sentence (w@x)"
    using assms(2) is_sentence_concat by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="w@x"])
    apply (rule_tac exI[where x="y"])
    by simp
qed

lemma Derivation_prepend:
  "Derivation b D b' \<Longrightarrow> is_sentence a \<Longrightarrow> Derivation (a@b) (map (\<lambda>(i, r). (i + length a, r)) D) (a@b')"
  using Derives1_prepend by (induction D arbitrary: b b') (auto, blast)

lemma Derives1_append:
  assumes "Derives1 u i r v" "is_sentence w"
  shows "Derives1 (u@w) i r (v@w)"
proof -
  obtain x y N \<alpha> where *: 
    "u = x @ [N] @ y" "v = x @ \<alpha> @ y"
    "is_sentence x" "is_sentence y"
    "(N, \<alpha>) \<in> \<RR>" "r = (N, \<alpha>)" "i = length x"
    using assms Derives1_def by blast
  hence "u@w = x @ [N] @ y @ w" "v@w = x @ \<alpha> @ y @ w" "is_sentence (y@w)"
    using assms(2) is_sentence_concat by auto
  thus ?thesis
    unfolding Derives1_def using *
    apply (rule_tac exI[where x="x"])
    apply (rule_tac exI[where x="y@w"])
    by blast
qed

lemma Derivation_append:
  "Derivation a D a' \<Longrightarrow> is_sentence b \<Longrightarrow> Derivation (a@b) D (a'@b)"
  using Derives1_append by (induction D arbitrary: a a') (auto, blast)

lemma Derivation_append_rewrite:
  assumes "is_sentence b" "is_sentence d"
  assumes "Derivation a D (b @ c @ d) " "Derivation c E c'"
  shows "\<exists>F. Derivation a F (b @ c' @ d)"
  using assms Derivation_append Derivation_prepend Derivation_implies_append by fast

lemma derives1_if_valid_rule:
  "(N, \<alpha>) \<in> \<RR> \<Longrightarrow> derives1 [N] \<alpha>"
  unfolding derives1_def
  apply (rule_tac exI[where x="[]"])
  apply (rule_tac exI[where x="[]"])
  by simp

lemma derives_if_valid_rule:
  "(N, \<alpha>) \<in> \<RR> \<Longrightarrow> derives [N] \<alpha>"
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
    "a@b = x @ [N] @ y" "ab = x @ \<alpha> @ y" "is_sentence x" "is_sentence y"
    "(N,\<alpha>) \<in> \<RR>" "snd d = (N,\<alpha>)" "fst d = length x"
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
      unfolding Derives1_def using *(1) #(5-7) ab_def(2)
      by (metis Derives1_sentence1 is_sentence_concat length_drop)
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
      unfolding Derives1_def using #(3-7) a_def by (metis append_take_drop_id is_sentence_concat)
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

definition rule_head :: "rule \<Rightarrow> symbol" where
  "rule_head = fst"

definition rule_body :: "rule \<Rightarrow> symbol list" where
  "rule_body = snd"

datatype item = 
  Item 
    (item_rule: rule) 
    (item_dot : nat) 
    (item_origin : nat)
    (item_end : nat)

type_synonym items = "item set"

definition item_rule_head :: "item \<Rightarrow> symbol" where
  "item_rule_head x = rule_head (item_rule x)"

definition item_rule_body :: "item \<Rightarrow> sentence" where
  "item_rule_body x = rule_body (item_rule x)"

definition item_\<alpha> :: "item \<Rightarrow> sentence" where
  "item_\<alpha> x = take (item_dot x) (item_rule_body x)"

definition item_\<beta> :: "item \<Rightarrow> sentence" where 
  "item_\<beta> x = drop (item_dot x) (item_rule_body x)"

definition init_item :: "rule \<Rightarrow> nat \<Rightarrow> item" where
  "init_item r k = Item r 0 k k"

definition is_complete :: "item \<Rightarrow> bool" where
  "is_complete x = (item_dot x \<ge> length (item_rule_body x))"

definition next_symbol :: "item \<Rightarrow> symbol option" where
  "next_symbol x = (if is_complete x then None else Some ((item_rule_body x) ! (item_dot x)))"

definition inc_item :: "item \<Rightarrow> nat \<Rightarrow> item" where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

lemmas item_defs = item_rule_head_def item_rule_body_def item_\<alpha>_def item_\<beta>_def rule_head_def rule_body_def

definition bin :: "items \<Rightarrow> nat \<Rightarrow> items" where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"

subsection \<open>Earley algorithm\<close>

locale Earley = CFG +
  fixes doc :: "symbol list"
  fixes rules :: "rule list"
  assumes valid_doc: "set doc \<subseteq> \<TT>"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
begin

definition Init :: "items" where
  "Init = { init_item r 0 | r. r \<in> \<RR> \<and> fst r = \<SS> }"

definition Scan :: "nat \<Rightarrow> items \<Rightarrow> items" where
  "Scan k I = I \<union> 
    { inc_item x (k+1) | x a.
        x \<in> bin I k \<and>
        doc!k = a \<and>
        k < length doc \<and>
        next_symbol x = Some a }"

definition Predict :: "nat \<Rightarrow> items \<Rightarrow> items" where
  "Predict k I = I \<union>
    { init_item r k | r x.
        r \<in> \<RR> \<and>
        x \<in> bin I k \<and>
        next_symbol x = Some (rule_head r) }"

definition Complete :: "nat \<Rightarrow> items \<Rightarrow> items" where
  "Complete k I = I \<union>
    { inc_item x k | x y.
        x \<in> bin I (item_origin y) \<and>
        y \<in> bin I k \<and>
        is_complete y \<and>
        next_symbol x = Some (item_rule_head y) }"

definition \<pi> :: "nat \<Rightarrow> items \<Rightarrow> items" where
  "\<pi> k I = limit (Scan k \<circ> Complete k \<circ> Predict k) I"

fun \<I> :: "nat \<Rightarrow> items" where
  "\<I> 0 = \<pi> 0 Init"
| "\<I> (Suc n) = \<pi> (Suc n) (\<I> n)"

definition \<II> :: "items" where
  "\<II> = \<I> (length doc)"

definition is_finished :: "item \<Rightarrow> bool" where
  "is_finished x \<longleftrightarrow> (
    item_rule_head x = \<SS> \<and>
    item_origin x = 0 \<and>
    item_end x = length doc \<and> 
    is_complete x)"

definition earley_recognized :: "bool" where
  "earley_recognized = (\<exists> x \<in> \<II>. is_finished x)"

subsection \<open>Wellformedness\<close>

definition wf_item :: "item \<Rightarrow> bool" where 
  "wf_item x = (
    item_rule x \<in> \<RR> \<and> 
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length doc)"

definition wf_items :: "items \<Rightarrow> bool" where
  "wf_items I = (\<forall>x \<in> I. wf_item x)"

lemmas wf_defs = wf_item_def wf_items_def

lemma is_sentence_item_\<beta>:
  "wf_item x \<Longrightarrow> is_sentence (item_\<beta> x)"
  using wf_item_def is_sentence_simp item_\<beta>_def item_rule_body_def rule_\<alpha>_type rule_body_def 
  by (metis prod.collapse in_set_dropD)

lemma wf_Init:
  "x \<in> Init \<Longrightarrow> wf_item x"
  unfolding Init_def wf_item_def init_item_def by auto

lemma wf_Scan:
  "wf_items I \<Longrightarrow> wf_items (Scan k I)"
  unfolding Scan_def wf_defs bin_def inc_item_def is_complete_def item_rule_body_def next_symbol_def
  by (auto split: if_splits)

lemma wf_Predict:
  "wf_items I \<Longrightarrow> wf_items (Predict k I)"
  unfolding Predict_def wf_defs bin_def init_item_def by auto

lemma wf_Complete:
  "wf_items I \<Longrightarrow> wf_items (Complete k I)"
  unfolding Complete_def wf_defs bin_def inc_item_def is_complete_def item_rule_body_def next_symbol_def
  by (auto split: if_splits; metis le_trans)

lemma wf_funpower:
  "wf_items I \<Longrightarrow> wf_items (funpower (\<lambda>I. (Scan k \<circ> Complete k \<circ> Predict k) I) n I)"
  unfolding wf_items_def
  apply (induction n)
  apply (auto)
  apply (metis wf_Complete wf_Predict wf_Scan wf_items_def)+
  done

lemma wf_\<pi>:
  assumes "wf_items I"
  shows "wf_items (\<pi> k I)"
  by (metis \<pi>_def assms elem_limit_simp wf_funpower wf_items_def)

lemma wf_\<pi>0:
  "wf_items (\<pi> 0 Init)"
  using wf_items_def wf_Init wf_\<pi> by blast

lemma wf_\<I>:
  "wf_items (\<I> n)"
  by (induction n) (auto simp: wf_\<pi>0 wf_\<pi>)

lemma wf_\<II>:
  "wf_items \<II>"
  unfolding \<II>_def using wf_\<I> by blast

subsection \<open>Soundness\<close>

definition sound_item :: "item \<Rightarrow> bool" where
  "sound_item x = derives [item_rule_head x] (slice (item_origin x) (item_end x) doc @ item_\<beta> x)"

definition sound_items :: "items \<Rightarrow> bool" where
  "sound_items I = (\<forall>x \<in> I. sound_item x)"

lemmas sound_defs = sound_items_def sound_item_def

lemma sound_Init:
  "sound_items Init"
  unfolding sound_items_def
proof (standard)
  fix x
  assume *: "x \<in> Init"
  hence "item_dot x = 0"
    using Init_def init_item_def by force
  hence "(item_rule_head x, item_\<beta> x) \<in> \<RR>"
    unfolding item_rule_head_def rule_head_def item_\<beta>_def item_rule_body_def rule_body_def
    using * wf_Init wf_item_def by simp
  hence "derives [item_rule_head x] (item_\<beta> x)"
    using derives_if_valid_rule by blast
  moreover have "item_origin x = item_end x"
    using * Init_def init_item_def by force
  ultimately show "sound_item x"
    unfolding sound_item_def by (simp add: slice_empty)
qed

lemma sound_item_inc_item:
  assumes "wf_item x" "sound_item x"
  assumes "next_symbol x = Some a"
  assumes "k < length doc" "doc!k = a" "item_end x = k"
  shows "sound_item (inc_item x (k+1))"
proof -
  define x' where [simp]: "x' = inc_item x (k+1)"
  obtain item_\<beta>' where *: "item_\<beta> x = a # item_\<beta>'"
    using assms(3) next_symbol_def is_complete_def item_\<beta>_def by (auto split: if_splits, metis Cons_nth_drop_Suc leI)
  have "slice (item_origin x) (item_end x) doc @ item_\<beta> x = slice (item_origin x') (item_end x') doc @ item_\<beta>'"
    using * assms(1,4-6) slice_append_nth wf_item_def inc_item_def by auto
  moreover have "item_\<beta>' = item_\<beta> x'"
    using * by (auto simp: inc_item_def item_\<beta>_def item_rule_body_def, metis List.list.sel(3) drop_Suc tl_drop)
  moreover have "derives [item_rule_head x] (slice (item_origin x) (item_end x) doc @ item_\<beta> x)"
    using assms(1,2,6) sound_item_def by blast
  ultimately show ?thesis
    by (simp add: inc_item_def item_rule_head_def sound_item_def)
qed

lemma sound_Scan:
  "wf_items I \<Longrightarrow> sound_items I \<Longrightarrow> sound_items (Scan k I)"
  unfolding Scan_def using sound_item_inc_item by (auto simp: wf_items_def sound_items_def bin_def)

lemma sound_Predict:
  "sound_items I \<Longrightarrow> sound_items (Predict k I)"
  unfolding Predict_def using item_defs
  by (auto simp: sound_defs init_item_def rule_head_def derives_if_valid_rule slice_empty)

lemma sound_Complete:
  assumes "wf_items I" "sound_items I"
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

    have "derives [item_rule_head y] (slice (item_origin y) (item_end y) doc)"
      using *(3,4) sound_defs assms bin_def is_complete_def item_\<beta>_def by auto
    then obtain E where E: "Derivation [item_rule_head y] E (slice (item_origin y) (item_end y) doc)"
      using derives_implies_Derivation by blast

    have "derives [item_rule_head x] (slice (item_origin x) (item_origin y) doc @ item_\<beta> x)"
      using *(2) sound_defs assms bin_def sound_items_def by auto
    moreover have 0: "item_\<beta> x = (item_rule_head y) # tl (item_\<beta> x)"
      using *(5) by (auto simp: next_symbol_def item_\<beta>_def is_complete_def split: if_splits,
                     metis Cons_nth_drop_Suc drop_Suc drop_tl leI)
    ultimately obtain D where D: 
      "Derivation [item_rule_head x] D (slice (item_origin x) (item_origin y) doc @
       [item_rule_head y] @ (tl (item_\<beta> x)))"
      using derives_implies_Derivation by (metis append_Cons append_Nil)

    have "wf_item x"
      using *(2) assms(1) bin_def wf_items_def by fastforce
    hence "is_sentence (tl (item_\<beta> x))"
      using is_sentence_item_\<beta> is_sentence_cons 0 by metis
    moreover have "is_sentence (slice (item_origin x) (item_origin y) doc)"
      by (meson is_sentence_simp is_symbol_def is_terminal_def slice_subset subsetD valid_doc)
    ultimately obtain G where 
      "Derivation [item_rule_head x] G (slice (item_origin x) (item_origin y) doc @
       slice (item_origin y) (item_end y) doc @ tl (item_\<beta> x))"
      using Derivation_append_rewrite D E by blast
    moreover have "item_origin x \<le> item_origin y"
      using *(2) \<open>wf_item x\<close> bin_def wf_item_def by auto
    moreover have "item_origin y \<le> item_end y"
      using *(3) wf_defs assms(1) bin_def by auto
    ultimately have "derives [item_rule_head x] (slice (item_origin x) (item_end y) doc @ tl (item_\<beta> x))"
      by (metis Derivation_implies_derives append.assoc slice_concat)
    moreover have "tl (item_\<beta> x) = item_\<beta> z"
      using *(1,5) 0 item_\<beta>_def by (auto simp: inc_item_def item_rule_body_def tl_drop drop_Suc)
    ultimately show ?thesis
      using sound_item_def *(1,3) bin_def inc_item_def item_rule_head_def by simp
  qed
qed

lemma sound_funpower:
  "wf_items I \<Longrightarrow> sound_items I \<Longrightarrow> sound_items (funpower (\<lambda>I. (Scan k \<circ> Complete k \<circ> Predict k) I) n I)"
  by (induction n) (auto simp: sound_Scan sound_Complete sound_Predict wf_Complete wf_Predict wf_funpower)

lemma sound_\<pi>:
  assumes "wf_items I" "sound_items I"
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
  "earley_recognized \<Longrightarrow> derives [\<SS>] doc"
  using earley_recognized_def sound_\<II> sound_defs is_finished_def item_\<beta>_def by (auto simp: is_complete_def)

subsection \<open>Monotonicity and Absorption\<close>

lemma Predict_mk_regular1: 
  "\<exists> (P :: rule \<Rightarrow> item \<Rightarrow> bool) F. Predict k = mk_regular1 P F"
proof -
  let ?P = "\<lambda> r x::item. r \<in> \<RR> \<and> item_end x = k \<and> next_symbol x = Some(fst r)"
  let ?F = "\<lambda> r (x::item). init_item r k"
  show ?thesis
    apply (rule_tac x="?P" in exI)
    apply (rule_tac x="?F" in exI)
    apply (rule_tac ext)
    by (auto simp: mk_regular1_def bin_def rule_head_def Predict_def)
qed

lemma Complete_mk_regular2: 
  "\<exists> (P :: dummy \<Rightarrow> item \<Rightarrow> item \<Rightarrow> bool) F. Complete k = mk_regular2 P F"
proof -
  let ?P = "\<lambda> (r::dummy) x y. item_end x = item_origin y \<and> item_end y = k \<and> is_complete y \<and> 
     next_symbol x = Some (item_rule_head y)"
  let ?F = "\<lambda> (r::dummy) x y. inc_item x k"
  show ?thesis
    apply (rule_tac x="?P" in exI)
    apply (rule_tac x="?F" in exI)
    apply (rule_tac ext)
    by (auto simp add: mk_regular2_def bin_def Complete_def)
qed

lemma Scan_mk_regular1:
  "\<exists> (P :: symbol \<Rightarrow> item \<Rightarrow> bool) F. Scan k = mk_regular1 P F"
proof -
  let ?P = "\<lambda> (a::symbol) (x::item). doc!k = a \<and> item_end x = k \<and> k < length doc \<and> next_symbol x = Some a"
  let ?F = "\<lambda> (a::symbol) (x::item). inc_item x (k + 1)"
  show ?thesis
    apply (rule_tac x="?P" in exI)
    apply (rule_tac x="?F" in exI)
    apply (rule_tac ext)
    by (auto simp add: mk_regular1_def bin_def Scan_def)
qed

lemma Predict_regular: 
  "regular (Predict k)" 
  by (metis Predict_mk_regular1 regular1)
  
lemma Complete_regular: 
  "regular (Complete k)" 
  by (metis Complete_mk_regular2 regular2) 

lemma Scan_regular: 
  "regular (Scan k)"
  by (metis Scan_mk_regular1 regular1)

lemma \<pi>_step_regular: 
  "regular ((Scan k) o (Complete k) o (Predict k))"
  by (simp add: Complete_regular Predict_regular Scan_regular regular_comp)
  
lemma \<pi>_regular: 
  "regular (\<pi> k)"
  unfolding \<pi>_def by (simp add: \<pi>_step_regular regular_limit)

lemma \<pi>_idem:
  "\<pi> k (\<pi> k I) = \<pi> k I"
  by (simp add: \<pi>_def \<pi>_step_regular limit_is_idempotent)

lemma Scan_mono:
  "I \<subseteq> (Scan k I)"
  using Scan_def by blast

lemma Predict_mono:
  "I \<subseteq> (Predict k I)"
  using Predict_def by blast

lemma Complete_mono:
  "I \<subseteq> (Complete k I)"
  using Complete_def by blast

lemma Scan_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Scan k I \<subseteq> Scan k J"
  unfolding Scan_def bin_def by blast

lemma Predict_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Predict k I \<subseteq> Predict k J"
  unfolding Predict_def bin_def by blast

lemma Complete_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Complete k I \<subseteq> Complete k J"
  unfolding Complete_def bin_def by blast

lemma Scan_\<pi>1_mono:
  "Scan k I \<subseteq> (Scan k \<circ> Complete k \<circ> Predict k) I"
  by (metis Complete_mono Predict_mono Scan_sub_mono comp_def subset_trans)

lemma Predict_\<pi>1_mono:
  "Predict k I \<subseteq> (Scan k \<circ> Complete k \<circ> Predict k) I"
  using Complete_mono Scan_mono by fastforce

lemma Complete_\<pi>1_mono:
  "Complete k I \<subseteq> (Scan k \<circ> Complete k \<circ> Predict k) I"
  by (metis Complete_sub_mono Orderings.order_class.dual_order.trans Predict_mono Scan_mono comp_apply)

lemma \<pi>1_\<pi>_mono:
  "(Scan k \<circ> Complete k \<circ> Predict k) I \<subseteq> \<pi> k I"
proof -
  have "(Scan k \<circ> Complete k \<circ> Predict k) I \<subseteq> funpower (Scan k \<circ> Complete k \<circ> Predict k) 1 I"
    by simp
  thus ?thesis
    by (metis \<pi>_def limit_elem subset_eq)
qed

lemma Scan_\<pi>_mono:
  "Scan k I \<subseteq> \<pi> k I"
  by (meson Scan_\<pi>1_mono \<pi>1_\<pi>_mono subset_trans)

lemma Predict_\<pi>_mono:
  "Predict k I \<subseteq> \<pi> k I"
  by (meson Predict_\<pi>1_mono \<pi>1_\<pi>_mono subset_trans)

lemma Complete_\<pi>_mono:
  "Complete k I \<subseteq> \<pi> k I"
  by (meson Complete_\<pi>1_mono \<pi>1_\<pi>_mono subset_trans)

lemma \<pi>_mono:
  "I \<subseteq> \<pi> k I"
  by (meson Complete_\<pi>_mono Complete_mono order_trans)

lemma Scan_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Scan k I) i = bin I i"
  unfolding Scan_def bin_def inc_item_def by fastforce

lemma Predict_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Predict k I) i = bin I i"
  unfolding Predict_def bin_def init_item_def by auto

lemma Complete_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Complete k I) i = bin I i"
  unfolding Complete_def bin_def inc_item_def by auto

lemma funpower_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (funpower (Scan k \<circ> Complete k \<circ> Predict k) n I) i = bin I i"
  using Scan_bin_absorb Predict_bin_absorb Complete_bin_absorb by (induction n) auto

lemma \<pi>_bin_absorb:
  assumes "i \<noteq> k" "i \<noteq> k+1" 
  shows "bin (\<pi> k I) i = bin I i"
proof (standard; standard)
  fix x 
  assume "x \<in> bin (\<pi> k I) i"
  then obtain n where "x \<in> bin (funpower (Scan k \<circ> Complete k \<circ> Predict k) n I) i"
    unfolding \<pi>_def limit_def natUnion_def using bin_def by auto
  then show "x \<in> bin I i"
    using funpower_bin_absorb assms by blast
next
  fix x
  assume "x \<in> bin I i"
  show "x \<in> bin (\<pi> k I) i"
    using \<pi>_mono \<open>x \<in> bin I i\<close> bin_def by auto
qed

subsection \<open>Completeness\<close>

lemma Scan_\<I>:
  assumes "i+1 \<le> k" "k \<le> length doc" "x \<in> bin (\<I> k) i" "next_symbol x = Some a" "doc!i = a"
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
      using Scan_\<pi>_mono unfolding Scan_def by auto
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
  assumes "i \<le> k" "x \<in> bin (\<I> k) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> \<RR>"
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
  assumes "i \<le> j" "j \<le> k" "x \<in> bin (\<I> k) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> \<RR>"
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

definition partially_complete_len :: "nat \<Rightarrow> items \<Rightarrow> nat \<Rightarrow> bool" where
  "partially_complete_len k I l = (
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length doc \<and>
      x \<in> bin I i \<and> next_symbol x = Some a \<and>
      Derivation [a] D (slice i j doc) \<and> length D \<le> l \<longrightarrow>
      inc_item x j \<in> I)"

definition partially_complete :: "nat \<Rightarrow> items \<Rightarrow> bool" where
  "partially_complete k I = (
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length doc \<and>
      x \<in> bin I i \<and> next_symbol x = Some a \<and>
      Derivation [a] D (slice i j doc) \<longrightarrow>
      inc_item x j \<in> I
  )"

lemma partially_complete_imp:
  "partially_complete k I \<Longrightarrow> partially_complete_len k I l"
  unfolding partially_complete_def partially_complete_len_def by blast

lemma fully_complete:
  assumes "j \<le> k" "k \<le> length doc"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> I" "wf_item x"
  assumes "Derivation (item_\<beta> x) D (slice j k doc)"
  assumes "partially_complete_len k I (length D)" "wf_items I"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> I"
  using assms
proof (induction "item_\<beta> x" arbitrary: d i j k N \<alpha> x D)
  case Nil
  have "item_\<alpha> x = \<alpha>"
    using Nil(1,4) unfolding item_\<alpha>_def item_\<beta>_def item_rule_body_def rule_body_def 
    by (metis item.sel(1) drop_all_iff snd_conv take_all)
  hence "x = Item (N,\<alpha>) (length \<alpha>) i j"
    using Nil.hyps Nil.prems(3,5) unfolding wf_item_def rule_body_def item_rule_body_def item_defs(4)
    by (auto, metis drop_all_iff le_antisym)
  have "Derivation [] D (slice j k doc)"
    using Nil.hyps Nil.prems(6) by simp
  hence "slice j k doc = []"
    using Derivation_from_empty by blast
  hence "j = k"
    unfolding slice_drop_take using Nil.prems(1,2) by simp
  thus ?case
    using \<open>x = Item (N, \<alpha>) (length \<alpha>) i j\<close> Nil.prems(4) by blast
next
  case (Cons b bs)
  then obtain j' E F where *: 
    "Derivation [b] E (slice j j' doc)"
    "Derivation bs F (slice j' k doc)"
    "j \<le> j'" "j' \<le> k" "length E \<le> length D" "length F \<le> length D"
    using Derivation_concat_split[of "[b]" bs D "slice j k doc"] slice_concat_Ex
    by (metis append_Cons append_Nil Cons.prems(1))
  have "x \<in> bin I j"
    using bin_def Cons.prems(3,4) by auto
  moreover have "next_symbol x = Some b"
    using Cons unfolding item_defs(4) next_symbol_def is_complete_def by (auto, metis nth_via_drop)
  ultimately have "inc_item x j' \<in> I"
    using *(1,3-5) Cons.prems(2-4,7) partially_complete_len_def by blast
  moreover have "partially_complete_len k I (length F)"
    using Cons.prems(7) *(6) unfolding partially_complete_len_def by fastforce
  moreover have "bs = item_\<beta> (Item (N,\<alpha>) (d+1) i j')"
    using Cons.hyps(2) Cons.prems(3) unfolding item_defs(4) item_rule_body_def 
    by (auto, metis List.list.sel(3) drop_Suc drop_tl)
  ultimately show ?case
    using Cons.hyps(1) *(2,4) inc_item_def Cons.prems(2,3,8) wf_items_def by auto
qed

lemma partially_complete_\<I>:
  "partially_complete k (\<I> k)"
  unfolding partially_complete_def
proof (standard, standard, standard, standard, standard, standard)
  fix x i a D j
  assume
    "i \<le> j \<and> j \<le> k \<and> k \<le> length doc \<and>
     x \<in> bin (\<I> k) i \<and> next_symbol x = Some a \<and>
     Derivation [a] D (slice i j doc)"
  thus "inc_item x j \<in> \<I> k"
  proof (induction "length D" arbitrary: x i a j D rule: nat_less_induct)
    case 1
    show ?case
    proof cases
      assume "D = []"
      hence "[a] = slice i j doc"
        using "1.prems" by force
      moreover have "j \<le> length doc"
        using le_trans "1.prems" by blast
      ultimately have "j = i+1"
        using slice_singleton by metis
      hence "i < length doc"
        using \<open>j \<le> length doc\<close> discrete by blast
      hence "doc!i = a"
        using slice_nth \<open>[a] = slice i j doc\<close> \<open>j = i + 1\<close> by fastforce
      hence "inc_item x (i+1) \<in> \<I> k"
        using Scan_\<I> \<open>j = i + 1\<close> "1.prems" by blast
      thus ?thesis
        by (simp add: \<open>j = i + 1\<close> wf_Init wf_items_def)
    next
      assume "\<not> D = []"
      then obtain d D' where "D = d # D'"
        by (meson List.list.exhaust)
      then obtain b where *: "Derives1 [a] (fst d) (snd d) b" "Derivation b D' (slice i j doc)"
        using "1.prems" by auto
      show ?thesis
      proof cases
        assume "is_terminal a"
        then obtain N \<alpha> where "[a] = [N]" "(N,\<alpha>) \<in> \<RR>"
          using *(1) unfolding Derives1_def by (metis Cons_eq_append_conv neq_Nil_conv)
         hence "is_nonterminal a"
           by simp
         thus ?thesis
          using \<open>is_terminal a\<close> is_terminal_nonterminal by blast
      next
        assume "\<not> is_terminal a"
        then obtain N \<alpha> where #: "[a] = [N]" "b = \<alpha>" "(N,\<alpha>) \<in> \<RR>" "fst d = 0" "snd d = (N,\<alpha>)"
          using *(1) unfolding Derives1_def by (simp add: Cons_eq_append_conv)
        define y where y_def: "y = Item (N,\<alpha>) 0 i i"
        have "init_item (N, \<alpha>) i \<in> \<I> k"
          using Predict_\<I> #(1,3) "1.prems" by auto
        hence "y \<in> bin (\<I> k) i"
          unfolding init_item_def using y_def by (simp add: bin_def wf_Init wf_items_def)
        have "length D' < length D"
          using \<open>D = d # D'\<close> by fastforce
        hence "partially_complete_len k (\<I> k) (length D')"
          unfolding partially_complete_len_def using "1.hyps" "1.prems" le_less_trans by blast
        hence "partially_complete_len j (\<I> k) (length D')"
          unfolding partially_complete_len_def using "1.prems" by (meson Orderings.order_class.dual_order.trans)
        moreover have "Derivation (item_\<beta> y) D' (slice i j doc)"
          using #(2) *(2) item_\<beta>_def item_rule_body_def rule_body_def y_def by force
        ultimately have 0: "Item (N,\<alpha>) (length \<alpha>) i j \<in> bin (\<I> k) j"
          using fully_complete wf_\<I> "1.prems" wf_items_def \<open>y \<in> bin (\<I> k) i\<close> bin_def y_def by force
        have 1: "x \<in> bin (\<I> k) i"
          by (simp add: "1.prems")
        have "next_symbol x = Some N"
          using #(1) "1.prems" by fastforce
        thus ?thesis
          using "1.prems" Complete_\<I>[OF _ _ 1 _ _ _ 0] #(3) is_complete_def item_rule_body_def rule_body_def by auto
      qed
    qed
  qed
qed

lemma partially_complete_\<II>:
  "partially_complete (length doc) \<II>"
  by (simp add: \<II>_def partially_complete_\<I>)

lemma Init_sub_\<I>:
  "Init \<subseteq> \<I> k"
  using \<pi>_mono by (induction k) auto

lemma Derivation_\<SS>1:
  assumes "Derivation [\<SS>] D doc"
  shows "\<exists>\<alpha> E. Derivation \<alpha> E doc \<and> (\<SS>,\<alpha>) \<in> \<RR>"
proof (cases D)
  case Nil
  thus ?thesis
    using is_nonterminal_startsymbol is_terminal_def is_terminal_nonterminal valid_doc assms by force
next
  case (Cons d D)
  then obtain \<alpha> where "Derives1 [\<SS>] (fst d) (snd d) \<alpha>" "Derivation \<alpha> D doc"
    using assms by auto
  hence "(\<SS>, \<alpha>) \<in> \<RR>"
    unfolding Derives1_def
    by (metis List.append.right_neutral List.list.discI append_eq_Cons_conv append_is_Nil_conv nth_Cons_0 self_append_conv2)
  thus ?thesis
    using \<open>Derivation \<alpha> D doc\<close> by auto
qed

theorem completeness:
  assumes "derives [\<SS>] doc"
  shows "earley_recognized"
proof -
  obtain \<alpha> where *: "(\<SS>,\<alpha>) \<in> \<RR>" "derives \<alpha> doc"
    using Derivation_\<SS>1 assms Derivation_implies_derives derives_implies_Derivation by blast
  let ?x = "Item (\<SS>,\<alpha>) 0 0 0"
  have "?x \<in> \<II>" "wf_item ?x"
    unfolding \<II>_def using *(1) Init_sub_\<I> Init_def wf_Init init_item_def by auto
  moreover have "derives (item_\<beta> ?x) (slice 0 (length doc) doc)"
    using *(2) item_defs(4) by (simp add: item_rule_body_def rule_body_def)
  ultimately have "Item (\<SS>,\<alpha>) (length \<alpha>) 0 (length doc) \<in> \<II>"
    using fully_complete partially_complete_\<II> wf_\<II> partially_complete_imp derives_implies_Derivation
    by (metis Nat.bot_nat_0.extremum le_refl)
  then show ?thesis
    unfolding earley_recognized_def is_finished_def by (auto simp: is_complete_def item_defs, force)
qed

corollary correctness:
  "earley_recognized \<longleftrightarrow> derives [\<SS>] doc"
  using soundness completeness by blast

end

end
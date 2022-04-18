theory Earley_Set
  imports
    "HOL-Library.While_Combinator"
    LocalLexing.Limit \<comment>\<open>Use\<close>
    LocalLexing.ListTools \<comment>\<open>Use\<close>
    LocalLexing.InductRules \<comment>\<open>Use\<close>
    LocalLexing.CFG \<comment>\<open>Use\<close>
    LocalLexing.Derivations \<comment>\<open>Use\<close>
    LocalLexing.LocalLexing \<comment>\<open>Done\<close>
    LocalLexing.LLEarleyParsing \<comment>\<open>Done\<close>
    LocalLexing.Validity \<comment>\<open>Done\<close>
    LocalLexing.TheoremD2 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD4 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD5 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD6 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD7 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD8 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD9 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.Ladder \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD10 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD11 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD12 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD13 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.TheoremD14 \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.PathLemmas \<comment>\<open>TODO: Extract relevant lemmas?\<close>
    LocalLexing.MainTheorems \<comment>\<open>TODO: Extract relevant lemmas?\<close>
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

lemma slice_append:
  "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> slice a b xs @ slice b c xs = slice a c xs"
  apply (induction a b xs arbitrary: c rule: slice.induct)
  apply (auto simp: slice_append_aux)
  using Suc_le_D by fastforce

lemma slice_append_Ex: \<comment>\<open>TODO\<close>
  "a \<le> c \<Longrightarrow> slice a c xs = ys @ zs \<Longrightarrow> \<exists>b. ys = slice a b xs \<and> zs = slice b c xs \<and> a \<le> b \<and> b \<le> c"
  apply (induction a c xs arbitrary: ys zs rule: slice.induct)
  apply (auto)
  apply (smt (verit, ccfv_threshold) Cons_eq_append_conv Earley_Set.slice.simps(2) Earley_Set.slice.simps(3) Earley_Set.slice.simps(4) Nat.less_eq_nat.simps(1) Suc_le_mono)
  by (metis Earley_Set.slice.simps(4) Suc_le_mono)

lemma slice_append_nth:
  "a \<le> b \<Longrightarrow> b < length xs \<Longrightarrow> slice a b xs @ [xs!b] = slice a (b+1) xs"
  by (auto simp: slice_drop_take take_Suc_conv_app_nth)

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
  "b < length xs \<Longrightarrow> [x] = slice a b xs \<Longrightarrow> b = a + 1"
  by (induction a b xs arbitrary: x rule: slice.induct)
     (auto, metis drop0 gr_implies_not0 length_0_conv slice_drop_take take_eq_Nil)

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

fun iterate1n :: "(nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "iterate1n f 0 x = f 0 x"
| "iterate1n f (Suc n) x = f (Suc n) (iterate1n f n x)"

definition \<pi> :: "nat \<Rightarrow> items \<Rightarrow> items" where
  "\<pi> k I = limit (Scan k \<circ> Complete k \<circ> Predict k) I"

definition \<I> :: "nat \<Rightarrow> items" where
  "\<I> k = iterate1n \<pi> k Init"

definition \<II> :: "items" where
  "\<II> = \<I> (length doc)"

definition is_finished :: "item \<Rightarrow> bool" where
  "is_finished x \<longleftrightarrow> (
    item_rule_head x = \<SS> \<and>
    item_origin x = 0 \<and>
    item_end x = length doc \<and> 
    is_complete x)"

definition earley_recognized :: "bool"
where
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
  "wf_items (\<I> k)"
  unfolding \<I>_def by (induction k) (auto simp: wf_\<pi> wf_Init wf_\<pi>0)

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
    ultimately obtain D where D: "Derivation [item_rule_head x] D (slice (item_origin x) (item_origin y) doc @ [item_rule_head y] @ (tl (item_\<beta> x)))"
      using derives_implies_Derivation by (metis append_Cons append_Nil)

    have "wf_item x"
      using *(2) assms(1) bin_def wf_items_def by fastforce
    hence "is_sentence (tl (item_\<beta> x))"
      using is_sentence_item_\<beta> is_sentence_cons 0 by metis
    moreover have "is_sentence (slice (item_origin x) (item_origin y) doc)"
      by (meson is_sentence_simp is_symbol_def is_terminal_def slice_subset subsetD valid_doc)
    ultimately obtain G where "Derivation [item_rule_head x] G (slice (item_origin x) (item_origin y) doc @ slice (item_origin y) (item_end y) doc @ tl (item_\<beta> x))"
      using Derivation_append_rewrite D E by blast
    moreover have "item_origin x \<le> item_origin y"
      using *(2) \<open>wf_item x\<close> bin_def wf_item_def by auto
    moreover have "item_origin y \<le> item_end y"
      using *(3) wf_defs assms(1) bin_def by auto
    ultimately have "derives [item_rule_head x] (slice (item_origin x) (item_end y) doc @ tl (item_\<beta> x))"
      by (metis Derivation_implies_derives append.assoc slice_append)
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
  apply (auto simp: \<I>_def sound_\<pi>0)
  using \<I>_def sound_\<pi> wf_\<I> by force

lemma sound_\<II>:
  "sound_items \<II>"
  unfolding \<II>_def using sound_\<I> by blast

theorem soundness:
  "earley_recognized \<Longrightarrow> derives [\<SS>] doc"
  using earley_recognized_def sound_\<II> sound_defs is_finished_def item_\<beta>_def by (auto simp: is_complete_def)

subsection \<open>Completeness\<close>

definition partially_complete :: "nat \<Rightarrow> items \<Rightarrow> bool" where
  "partially_complete k I = (
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length doc \<and>
      x \<in> bin I i \<and>
      next_symbol x = Some a \<and>
      Derivation [a] D (slice i j doc) \<longrightarrow>
      inc_item x j \<in> I
  )"

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

lemma \<pi>_idempotent:
  "\<pi> k (\<pi> k I) = \<pi> k I"
  by (simp add: \<pi>_def \<pi>_step_regular limit_is_idempotent)

lemma X1:
  "I \<subseteq> Scan k I" "I \<subseteq> Complete k I" "I \<subseteq> Predict k I"
  using Scan_def Complete_def Predict_def by auto

lemma Q:
  "Scan k I \<subseteq> \<pi> k I"
proof standard
  fix x 
  assume "x \<in> Scan k I"
  thus "x \<in> \<pi> k I"
    sorry
qed

lemma Q''':
  "I \<subseteq> \<pi> k I"
  by (meson Orderings.order_class.dual_order.trans Q X1(1))

lemma Q'':
  "I \<subseteq> iterate1n \<pi> k I"
  using Q'''
  by (induction k arbitrary: I) (auto, blast)

lemma a0:
  "i < j \<Longrightarrow> \<pi> i (\<pi> j I) \<subseteq> \<pi> j (\<pi> i I)"
  sorry

lemma a1:
  "i+1 < j \<Longrightarrow> \<pi> i (\<pi> j I) \<supseteq> \<pi> j (\<pi> i I)"
  sorry

lemma Z'':
  "i \<le> j \<Longrightarrow> \<pi> i (iterate1n \<pi> j I) = iterate1n \<pi> j I"
proof (induction j arbitrary: i I)
  case 0
  then show ?case
    using \<pi>_idempotent by auto
next
  case (Suc j)
  then show ?case
  proof cases
    assume "i = Suc j"
    show ?thesis
      using \<open>i = Suc j\<close> \<pi>_idempotent by force
  next
    assume "\<not> i = Suc j"
    hence "i \<le> j"
      using le_Suc_eq Suc.prems by blast
    show ?thesis
    proof cases
      assume "i = j"
      show ?thesis
        by (metis Nat.nat.discI Q''' \<open>i \<le> j\<close> a0 diff_Suc_1 le_imp_less_Suc local.Suc.IH local.iterate1n.elims subset_antisym)
    next
      assume "\<not> i = j"
      hence "i < j"
        using \<open>i \<le> j\<close> by force
      show ?thesis
        by (metis Q''' Suc_inject Zero_not_Suc \<open>i \<le> j\<close> a0 le_imp_less_Suc local.Suc.IH local.iterate1n.elims subset_antisym)
    qed
  qed
qed


lemma iterate1n_idempotent:
  "i \<le> j \<Longrightarrow> iterate1n \<pi> i (iterate1n \<pi> j I) = iterate1n \<pi> j I"
  by (induction i arbitrary: j) (auto simp: Z'')

lemma Q':
  assumes "i < length doc" "doc!i = a"
  assumes "x \<in> bin I i" "next_symbol x = Some a"
  shows "inc_item x (i+1) \<in> \<pi> i I"
  using Q Scan_def assms bin_def by blast

lemma B:
  assumes "i+1 \<le> k" "k \<le> length doc"
  assumes "x \<in> bin I i" "next_symbol x = Some a" "doc!i = a"
  shows "inc_item x (i+1) \<in> iterate1n \<pi> k I"
  using assms
proof (induction k arbitrary: i x I a)
  case 0
  then show ?case
    by linarith
next
  case (Suc k)
  then show ?case
  proof cases
    assume "i+1 \<le> k"
    hence "inc_item x (i+1) \<in> iterate1n \<pi> k I"
      using Suc by simp
    thus ?thesis
      using Scan_def Q by fastforce
  next
    assume "\<not> i+1 \<le> k"
    hence "i+1 = Suc k"
      using le_Suc_eq Suc.prems(1) by blast
    have "x \<in> bin (iterate1n \<pi> k I) i"
      using Q'' bin_def local.Suc.prems(3) by auto
    hence "inc_item x (i+1) \<in> \<pi> i (iterate1n \<pi> k I)"
      using Q' \<open>i + 1 = Suc k\<close> Suc.prems(2,4,5) by auto
    hence "inc_item x (i+1) \<in> \<pi> k (iterate1n \<pi> k I)"
      using \<open>i + 1 = Suc k\<close> by force
    hence "inc_item x (i+1) \<in> iterate1n \<pi> k I"
      using \<pi>_idempotent by (metis local.iterate1n.elims)
    thus ?thesis
      using Q''' by auto
  qed
qed

lemma p0:
  "is_terminal a \<Longrightarrow> Derivation [a] D b \<Longrightarrow> b = [a]"
  by (metis CFG.CFG.is_word_def CFG_axioms List.list.discI List.list.pred_inject(2) is_word_Derivation list_all_simps(2) local.Derivation.elims(1))
  
lemma partially_complete_\<I>:
  "partially_complete k (\<I> k)"
  unfolding partially_complete_def
proof (standard, standard, standard, standard, standard, standard)
  fix x i a D j
  assume
    "i \<le> j \<and> j \<le> k \<and> k \<le> length doc \<and>
     x \<in> bin (\<I> k) i \<and>
     next_symbol x = Some a \<and>
     Derivation [a] D (slice i j doc)"
  thus "inc_item x j \<in> \<I> k"
  proof (induction D arbitrary: x i a j)
    case Nil
    then show ?case
      sorry
  next
    case (Cons d D)
    show ?case
      sorry
  qed
qed

lemma X: "derives [] \<alpha> \<Longrightarrow> \<alpha> = []"
  by (metis CFG.CFG.is_word_def CFG_axioms List.list.pred_inject(1) derives_implies_Derivation is_word_Derivation local.Derivation.simps(1))

lemma L0: "is_sentence a \<Longrightarrow> derives a b \<Longrightarrow> is_sentence b"
  by (metis Derives1_sentence2 derives1_implies_Derives1 derives_induct)

lemma L1: "is_sentence a \<Longrightarrow> is_sentence b \<Longrightarrow> derives a a' \<Longrightarrow> derives b b' \<Longrightarrow> derives (a@b) (a'@b')"
  by (meson Derivation_append Derivation_implies_append Derivation_implies_derives Derivation_prepend L0 derives_implies_Derivation)

lemma R:
  "Derivation (a@b) D c \<Longrightarrow> \<exists>E F a' b'. Derivation a E a' \<and> Derivation b F b' \<and> c = a' @ b'"
  sledgehammer
(*
| "Derivation a (d#D) b = (\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b)"

  "Derives1 u i r v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> is_sentence x
        \<and> is_sentence y
        \<and> (N, \<alpha>) \<in> \<RR>
        \<and> r = (N, \<alpha>) \<and> i = length x)"  
*)

lemma R':
  assumes "Derivation (a#as) D (slice i k doc)" "i \<le> k"
  shows "\<exists>E F j. Derivation [a] E (slice i j doc) \<and> Derivation as F (slice j k doc) \<and> i \<le> j \<and> j \<le> k"
proof -
  obtain E F a' as' where "Derivation [a] E a'" "Derivation as F as'" "slice i k doc = a' @ as'"
    using assms R by (metis append_Cons append_Nil)
  thus ?thesis
    using assms(2) slice_append_Ex by blast
qed

lemma partially_complete_\<II>:
  "partially_complete (length doc) \<II>"
  by (simp add: \<II>_def partially_complete_\<I>)

lemma fully_complete:
  assumes "i \<le> j" "j \<le> length doc"
  assumes "x \<in> bin \<II> i" "next_symbol x = Some a"
  assumes "Derivation [a] D (slice i j doc)"
  shows "inc_item x j \<in> \<II>"
  using assms partially_complete_\<II> unfolding partially_complete_def by blast

lemma core:
  assumes "j \<le> k" "k \<le> length doc"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> \<II>" "wf_item x"
  assumes "derives (item_\<beta> x) (slice j k doc)"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> \<II>"
  using assms
proof (induction "item_\<beta> x" arbitrary: d i j k N \<alpha> x)
  case Nil
  have "item_\<alpha> x = \<alpha>"
    using Nil(1) unfolding item_\<alpha>_def item_\<beta>_def item_rule_body_def rule_body_def
    by (metis Earley_Set.item.sel(1) drop_all_iff Nil.prems(3) snd_conv take_all)
  hence "x = Item (N,\<alpha>) (length \<alpha>) i j"
    using Nil(6) wf_item_def apply auto
    by (metis Earley_Set.item.sel(1) Earley_Set.item.sel(2) drop_all_iff item_defs(4) item_rule_body_def le_antisym local.Nil.hyps local.Nil.prems(3) rule_body_def snd_conv)
  have "derives [] (slice j k doc)"
    by (simp add: local.Nil.hyps local.Nil.prems(6))
  hence "slice j k doc = []"
    using X by blast
  hence "j = k"
    by (metis Groups.monoid_add_class.add.right_neutral Lattices.linorder_class.min.absorb2 List.list.size(3) le_add_diff_inverse length_drop length_take local.Nil.prems(1) local.Nil.prems(2) slice_drop_take)
  then show ?case
    using \<open>x = Item (N, \<alpha>) (length \<alpha>) i j\<close> assms(4)
    using local.Nil.prems(4) by blast
next
  case (Cons b bs)

  have 2: "next_symbol x = Some b"
    by (metis List.list.simps(3) drop_0 drop_all hd_drop_conv_nth is_complete_def item_defs(4) local.Cons.hyps(2) next_symbol_def not_le nth_Cons_0)
  obtain j' where 3: "derives [b] (slice j j' doc)" "derives bs (slice j' k doc)" "j \<le> j'" "j' \<le> k"
    using Cons(2) Cons(8) R'
    by (metis Derivation_implies_derives derives_implies_Derivation local.Cons.prems(1))
  have 1: "j' \<le> length doc"
    using "3"(4) local.Cons.prems(2) by auto
  have 4: "x \<in> bin \<II> j"
    using Earley_Set.item.sel(4) assms(4) bin_def local.Cons.prems(3)
    using local.Cons.prems(4) by blast
  have 5: "inc_item x j' \<in> \<II>"
    using fully_complete[OF 3(3) 1 4 2] using "3"(1) derives_implies_Derivation by blast
  have 6: "inc_item x j' = Item (N,\<alpha>) (d+1) i j'"
    by (simp add: inc_item_def local.Cons.prems(3))

  have 7: "bs = item_\<beta> (Item (N,\<alpha>) (d+1) i j')"
    by (metis Earley_Set.item.sel(1) Earley_Set.item.sel(2) Groups.monoid_add_class.add.right_neutral List.list.sel(3) One_nat_def add_Suc_right drop_Suc item_defs(4) item_rule_body_def local.Cons.hyps(2) local.Cons.prems(3) tl_drop)
  have 8: "k \<le> length doc"
    by (simp add: local.Cons.prems(2))
  have 9: "wf_item (Item (N, \<alpha>) (d + 1) i j')"
    using "5" "6" wf_\<II> wf_items_def by force
  have 11: "derives (item_\<beta> (Item (N, \<alpha>) (d + 1) i j')) (slice j' k doc)"
    using "3"(2) "7" by blast
  have "Item (N, \<alpha>) (length \<alpha>) i k \<in> \<II>"
    using Cons.hyps(1)[OF 7 3(4) 8 _ _ 9 11] using "5" "6" by auto
  then show ?case
    by blast
qed

lemma A:
  "Derivation [\<SS>] D doc \<Longrightarrow> \<exists>\<alpha> E. Derivation \<alpha> E doc \<and> (\<SS>,\<alpha>) \<in> \<RR>"
proof (induction D)
  case Nil
  then show ?case
    by (metis List.list.set_intros(1) is_nonterminal_startsymbol is_terminal_def is_terminal_nonterminal local.Derivation.simps(1) subsetD valid_doc)
next
  case (Cons d D)
  then show ?case
    apply (auto)
    by (smt (z3) Derives1_bound Derives1_def List.list.size(3) List.list.size(4) One_nat_def Suc_eq_plus1 append_Cons append_self_conv2 less_Suc_eq_le nth_Cons_0 self_append_conv slice_empty slice_id)
qed

lemma A':
  "derives [\<SS>] doc \<Longrightarrow> \<exists>N \<alpha>. derives \<alpha> doc \<and> (\<SS>,\<alpha>) \<in> \<RR>"
  using A by (meson Derivation_implies_derives derives_implies_Derivation)

theorem completeness:
  assumes "derives [\<SS>] doc"
  shows "earley_recognized"
proof -
  obtain \<alpha> where *: "(\<SS>,\<alpha>) \<in> \<RR>" "derives \<alpha> doc"
    using A' by (meson assms)
  let ?x = "Item (\<SS>,\<alpha>) 0 0 0"
  have "?x \<in> \<II>" "wf_item ?x"
    using Init_def Q'' \<I>_def \<II>_def init_item_def * 
    apply fastforce
    by (simp add: "*"(1) wf_item_def)
  moreover have "derives (item_\<beta> ?x) (slice 0 (length doc) doc)"
    by (simp add: *(2) item_defs(4) item_rule_body_def rule_body_def)
  ultimately have "Item (\<SS>,\<alpha>) (length \<alpha>) 0 (length doc) \<in> \<II>"
    using core by blast
  then show ?thesis
    unfolding earley_recognized_def is_finished_def
    by (auto simp: is_complete_def item_defs, force)
qed

text\<open>
  partially_complete k I = (
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length doc \<and>
      x \<in> bin I i \<and>
      next_symbol x = Some a \<and>
      Derivation [a] D (slice i j doc) \<longrightarrow>
      inc_item x j \<in> I

  \<II> = \<I> (length doc)

  partially_complete (length doc) I =
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> length doc \<and>
      x \<in> bin I i \<and>
      next_symbol x = Some a \<and>
      Derivation [a] D (slice i j doc) \<longrightarrow>
      inc_item x j \<in> I

  S -> \<alpha> ->* doc
  then obtain set of indices I s.t.
    (\<forall>i < length \<alpha>. derives ([\<alpha>!i]) (slice (I!i) (I!(i+1)) \<beta>)) \<and>
     length I = length \<alpha> + 1 \<and>
     I!0 = 0 \<and>
     I!(length \<alpha>) = length \<beta> \<and>
     sorted I

  let \<alpha> = a0..aN, let I = 0i1..iN(N+1)

  we have .a0..aN 0 0 in bin \<II> (I!0)
          next_symbol .a0..aN = a0
          derives [a0] (slice (I!0) (I!1) doc)
          I!0 <= I!1, I!1 <= length doc
  hence a0.a1..aN 0 (I!1) in \<II>

  (..)
\<close>

end

end
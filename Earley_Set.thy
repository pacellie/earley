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

lemma slice_nth:
  "a < length xs \<Longrightarrow> slice a (a+1) xs = [xs!a]"
  unfolding slice_drop_take
  by (metis Cons_nth_drop_Suc One_nat_def diff_add_inverse drop_take take_Suc_Cons take_eq_Nil)

lemma slice_append_nth:
  "a \<le> b \<Longrightarrow> b < length xs \<Longrightarrow> slice a b xs @ [xs!b] = slice a (b+1) xs"
  by (metis le_add1 slice_append slice_nth)

lemma slice_empty:
  "b \<le> a \<Longrightarrow> slice a b xs = []"
  by (simp add: slice_drop_take)

lemma slice_id[simp]:
  "slice 0 (length xs) xs = xs"
  by (simp add: slice_drop_take)

lemma slice_subset:
  "set (slice a b xs) \<subseteq> set xs"
  using slice_drop_take by (metis in_set_dropD in_set_takeD subsetI)

lemma slice_singleton: \<comment>\<open>TODO\<close>
  "b \<le> length xs \<Longrightarrow> [x] = slice a b xs \<Longrightarrow> b = a + 1"
  unfolding slice_drop_take
  by (metis Lattices.linorder_class.min.absorb2 List.list.simps(3) List.list.size(3) One_nat_def drop_all le_add_diff_inverse length_Cons length_drop length_take linear)

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

lemma wf_iterate1n_\<pi>:
  "wf_items I \<Longrightarrow> wf_items (iterate1n \<pi> k I)"
  using wf_\<pi> by (induction k arbitrary: I) auto

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

lemma X1: \<comment>\<open>TODO\<close>
  "I \<subseteq> Scan k I" "I \<subseteq> Complete k I" "I \<subseteq> Predict k I"
  using Scan_def Complete_def Predict_def by auto

lemma X1': \<comment>\<open>TODO\<close>
  "Scan k I \<subseteq> (Scan k \<circ> Complete k \<circ> Predict k) I"
  "Predict k I \<subseteq> (Scan k \<circ> Complete k \<circ> Predict k) I"
  "Complete k I \<subseteq> (Scan k \<circ> Complete k \<circ> Predict k) I"
    apply (smt (z3) Scan_def Un_iff X1(2) X1(3) bin_def comp_apply mem_Collect_eq subset_iff)
   apply (smt (z3) Scan_def Un_iff X1(2) X1(3) bin_def comp_apply mem_Collect_eq subset_iff)
  unfolding comp_apply using X1 Complete_def Predict_def bin_def by fastforce

lemma X2: \<comment>\<open>TODO\<close>
  "setmonotone (Scan k)" "setmonotone (Predict k)" "setmonotone (Complete k)"
  by (simp_all add: Scan_regular Predict_regular Complete_regular regular_implies_setmonotone)

lemma X3: \<comment>\<open>TODO\<close>
  "setmonotone (Scan k \<circ> Complete k \<circ> Predict k)"
  using X2 by (simp add: setmonotone_comp)

lemma X4: \<comment>\<open>TODO\<close>
  "setmonotone (\<pi> k)"
  by (simp add: \<pi>_regular regular_implies_setmonotone)

lemma X6: \<comment>\<open>TODO\<close>
  "(Scan k \<circ> Complete k \<circ> Predict k) I \<subseteq> funpower (Scan k \<circ> Complete k \<circ> Predict k) 1 I"
  by simp

lemma X5: \<comment>\<open>TODO\<close>
  "(Scan k \<circ> Complete k \<circ> Predict k) I \<subseteq> \<pi> k I"
  unfolding \<pi>_def unfolding limit_def natUnion_def
  by (metis (mono_tags, lifting) Sup_upper2 X6 mem_Collect_eq)

lemma Q: \<comment>\<open>TODO\<close>
  "Scan k I \<subseteq> \<pi> k I"
  "Predict k I \<subseteq> \<pi> k I"
  "Complete k I \<subseteq> \<pi> k I"
  using X1' X5 by blast+

lemma Q''': \<comment>\<open>TODO\<close>
  "I \<subseteq> \<pi> k I"
  by (meson Orderings.order_class.dual_order.trans Q X1(1))

lemma Q'': \<comment>\<open>TODO\<close>
  "I \<subseteq> iterate1n \<pi> k I"
  using Q'''
  by (induction k arbitrary: I) (auto, blast)

definition bins :: "items \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> items" where
  "bins I i j = { x | x k. x \<in> bin I k \<and> i \<le> k \<and> k \<le> j }"

definition bins_inf :: "items \<Rightarrow> nat \<Rightarrow> items" where
  "bins_inf I i = { x | x k. x \<in> bin I k \<and> i \<le> k }"

lemma bins_Un: \<comment>\<open>TODO\<close>
  "bins (I \<union> J) i j = bins I i j \<union> bins J i j"
  unfolding bins_def bin_def by blast

lemma bins_inf_Un: \<comment>\<open>TODO\<close>
  "bins_inf (I \<union> J) i = bins_inf I i \<union> bins_inf J i"
  unfolding bins_inf_def bin_def by blast

lemma bins_bins_inf_In: \<comment>\<open>TODO\<close>
  "bins (bins_inf I k) i j = bins I (max i k) j"
  unfolding bins_def bins_inf_def bin_def max_def by auto

lemma bins_inf_absorb: \<comment>\<open>TODO\<close>
  "i < j \<Longrightarrow> bins_inf (bins_inf I j) i = bins_inf I j"
  "i < j \<Longrightarrow> bins_inf (bins_inf I i) j = bins_inf I j"
  unfolding bins_inf_def bin_def by auto

lemma bins_absorb: \<comment>\<open>TODO\<close>
  "i' \<le> i \<Longrightarrow> j' \<ge> j \<Longrightarrow> bins (bins I i' j') i j = bins I i j"
  unfolding bins_def bin_def by auto

lemma bins_bins_inf_empty: \<comment>\<open>TODO\<close>
  "j < k \<Longrightarrow> bins (bins_inf I k) i j = {}"
  unfolding bins_def bins_inf_def bin_def by simp

lemma bins_inf_bins_empty: \<comment>\<open>TODO\<close>
  "j < k \<Longrightarrow> bins_inf (bins I i j) k = {}"
  unfolding bins_inf_def bins_def bin_def by simp

lemma u0: \<comment>\<open>TODO\<close>
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Scan k I) i = bin I i"
  unfolding Scan_def bin_def inc_item_def by fastforce

lemma u1: \<comment>\<open>TODO\<close>
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Predict k I) i = bin I i"
  unfolding Predict_def bin_def init_item_def by auto

lemma u2: \<comment>\<open>TODO\<close>
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Complete k I) i = bin I i"
  unfolding Complete_def bin_def inc_item_def by auto

lemma u3: \<comment>\<open>TODO\<close>
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin ((Scan k \<circ> Complete k \<circ> Predict k) I) i = bin I i"
  using u0 u1 u2 by simp

lemma u4: \<comment>\<open>TODO\<close>
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (funpower (Scan k \<circ> Complete k \<circ> Predict k) n I) i = bin I i"
  using u3 apply (induction n) apply auto done

lemma \<pi>_bin_absorb: \<comment>\<open>TODO\<close>
  assumes "i \<noteq> k" "i \<noteq> k+1" 
  shows "bin (\<pi> k I) i = bin I i"
proof (standard; standard)
  fix x 
  assume "x \<in> bin (\<pi> k I) i"
  then obtain n where "x \<in> bin (funpower (Scan k \<circ> Complete k \<circ> Predict k) n I) i"
    unfolding \<pi>_def limit_def natUnion_def using bin_def by auto
  then show "x \<in> bin I i"
    using u4 assms by blast
next
  fix x
  assume "x \<in> bin I i"
  show "x \<in> bin (\<pi> k I) i"
    using Q''' \<open>x \<in> bin I i\<close> bin_def by auto
qed

lemma v0: \<comment>\<open>TODO\<close>
  "I \<subseteq> J \<Longrightarrow> Scan k I \<subseteq> Scan k J"
  unfolding Scan_def bin_def by blast

lemma v1: \<comment>\<open>TODO\<close>
  "I \<subseteq> J \<Longrightarrow> Predict k I \<subseteq> Predict k J"
  unfolding Predict_def bin_def by blast

lemma v2: \<comment>\<open>TODO\<close>
  "I \<subseteq> J \<Longrightarrow> Complete k I \<subseteq> Complete k J"
  unfolding Complete_def bin_def by blast

lemma v3: \<comment>\<open>TODO\<close>
  "I \<subseteq> J \<Longrightarrow> (Scan k \<circ> Complete k \<circ> Predict k) I \<subseteq> (Scan k \<circ> Complete k \<circ> Predict k) J"
  by (simp add: v0 v1 v2)

lemma v4: \<comment>\<open>TODO\<close>
  "I \<subseteq> J \<Longrightarrow> funpower (Scan k \<circ> Complete k \<circ> Predict k) n I \<subseteq> funpower (Scan k \<circ> Complete k \<circ> Predict k) n J"
  using v3 by (induction n) auto

lemma \<pi>_sub: \<comment>\<open>TODO\<close>
  assumes "I \<subseteq> J"
  shows "\<pi> k I \<subseteq> \<pi> k J"
proof (standard)
  fix x 
  assume "x \<in> \<pi> k I"
  then obtain n where "x \<in> funpower (Scan k \<circ> Complete k \<circ> Predict k) n I"
    unfolding \<pi>_def limit_def natUnion_def using bin_def by auto
  then show "x \<in> \<pi> k J"
    using v4 by (metis (no_types, lifting) \<pi>_def assms elem_limit_simp subsetD)
qed

lemma w0:
  "Scan k I = bins_inf I (k+1) \<union> Scan k (bins I 0 k)"
  unfolding Scan_def bins_inf_def bins_def bin_def by auto

lemma w1:
  "Predict k I = bins_inf I (k+1) \<union> Predict k (bins I 0 k)"
  unfolding Predict_def bins_inf_def bins_def bin_def by auto

lemma w2:
  assumes "wf_items I" 
  shows "Complete k I = bins_inf I (k+1) \<union> Complete k (bins I 0 k)"
proof (standard; standard)
  fix x
  assume "x \<in> Complete k I"
  hence *: "x \<in> I \<or> x \<in> {u. \<exists>x y. u = inc_item x k \<and> x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> 
                                   is_complete y \<and> next_symbol x = Some (item_rule_head y)}"
    unfolding Complete_def by blast
  then show "x \<in> bins_inf I (k + 1) \<union> Complete k (bins I 0 k)"
  proof cases
    assume "x \<in> I"
    then show ?thesis
      by (smt (z3) Nat.bot_nat_0.extremum Suc_eq_plus1 Un_iff X1(2) bin_def bins_def bins_inf_def le_refl mem_Collect_eq not_less_eq_eq subset_eq)
  next
    assume "\<not> x \<in> I"
    hence "x \<in> {u. \<exists>x y. u = inc_item x k \<and> x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> 
                         is_complete y \<and> next_symbol x = Some (item_rule_head y)}"
      using "*" by linarith
    hence "x \<in> {u. \<exists>x y. u = inc_item x k \<and> x \<in> bin I (item_origin y) \<and> y \<in> bin (bins I 0 k) k \<and> 
                         is_complete y \<and> next_symbol x = Some (item_rule_head y)}"
      unfolding bins_def bin_def by blast
    hence "x \<in> {u. \<exists>x y. u = inc_item x k \<and> x \<in> bin (bins I 0 k) (item_origin y) \<and> y \<in> bin (bins I 0 k) k \<and> 
                         is_complete y \<and> next_symbol x = Some (item_rule_head y)}"
      unfolding bins_def bin_def using assms unfolding wf_items_def wf_item_def by blast
    then show ?thesis
      by (simp add: Complete_def)
  qed
next
  fix x
  assume *: "x \<in> bins_inf I (k + 1) \<union> Complete k (bins I 0 k)"
  show "x \<in> Complete k I"
  proof cases
    assume "x \<in> bins_inf I (k + 1)"
    hence "x \<in> I"
      unfolding bins_inf_def bin_def by blast
    show ?thesis
      using X1(2) \<open>x \<in> I\<close> by auto
  next
    assume "\<not> x \<in> bins_inf I (k + 1)"
    hence "x \<in> Complete k (bins I 0 k)"
      using * by blast
    moreover have "bins I 0 k \<subseteq> I"
      unfolding bins_def bin_def by blast
    ultimately show ?thesis
      by (meson subsetD v2)
  qed
qed

lemma w3:
  assumes "wf_items I"
  shows "(Scan k \<circ> Complete k \<circ> Predict k) I = bins_inf I (k+1) \<union> (Scan k \<circ> Complete k \<circ> Predict k) (bins I 0 k)"
proof (standard; standard)
  fix x
  assume "x \<in> (Scan k \<circ> Complete k \<circ> Predict k) I"

  have "(Scan k \<circ> Complete k \<circ> Predict k) I = Scan k (Complete k (bins_inf I (k+1) \<union> Predict k (bins I 0 k)))"
    by (metis comp_def w1)
  also have "... = Scan k (Complete k (Predict k (bins I 0 k)))"
    sorry
  also have "... = Scan k (bins_inf (Predict k (bins I 0 k)) (k+1) \<union> Complete k (bins (Predict k (bins I 0 k)) 0 k))"
    by (metis assms subset_eq sup_ge2 w1 w2 wf_Predict wf_items_def)
  also have "... = Scan k (Complete k (bins (Predict k (bins I 0 k)) 0 k))"
    sorry
  also have "... = Scan k (Complete k (Predict k (bins I 0 k)))"
    sorry
  also have "... = bins_inf (Complete k (Predict k (bins I 0 k))) (k+1) \<union> Scan k (bins (Complete k (Predict k (bins I 0 k))) 0 k)"
    by (meson w0)
(*  "Scan k I = bins_inf I (k+1) \<union> Scan k (bins I 0 k)" *)

  show "x \<in> bins_inf I (k + 1) \<union> (Scan k \<circ> Complete k \<circ> Predict k) (bins I 0 k)"
  proof cases
    assume "x \<in> Predict k I"
    show ?thesis
      by (metis Un_iff X1'(2) \<open>x \<in> Predict k I\<close> subset_eq w1)
  next
    assume "\<not> x \<in> Predict k I"
    hence "x \<in> (Scan k (Complete k (bins_inf I (k+1) \<union> Predict k (bins I 0 k))))"
      by (metis \<open>x \<in> (Scan k \<circ> Complete k \<circ> Predict k) I\<close> comp_def w1
    thus ?thesis
      sledgehammer
next
  fix x 
  assume "x \<in> bins_inf I (k + 1) \<union> (Scan k \<circ> Complete k \<circ> Predict k) (bins I 0 k)"
  show "x \<in> (Scan k \<circ> Complete k \<circ> Predict k) I"
    by (metis Un_iff X1(1) X1(2) \<open>x \<in> bins_inf I (k + 1) \<union> (Scan k \<circ> Complete k \<circ> Predict k) (bins I 0 k)\<close> comp_apply subsetD sup_ge2 v0 v2 w1)
qed

lemma bins_\<pi>_absorb: \<comment>\<open>TODO\<close>
  assumes "i \<le> j" "j < k"
  shows "bins (\<pi> k I) i j = bins I i j"
proof -
  have "bins (\<pi> k I) i j = { x | x l. x \<in> bin (\<pi> k I) l \<and> i \<le> l \<and> l \<le> j }"
    unfolding bins_def by blast
  also have "... = { x | x l. x \<in> bin I l \<and> i \<le> l \<and> l \<le> j }"
  proof (standard; standard)
    fix x
    assume "x \<in> { x | x l. x \<in> bin (\<pi> k I) l \<and> i \<le> l \<and> l \<le> j }"
    then obtain l where "x \<in> bin (\<pi> k I) l" "i \<le> l" "l \<le> j"
      by blast
    moreover have "l \<noteq> k" "l \<noteq> k+1"
      using assms(2) calculation(3) leD by linarith+
    ultimately show "x \<in> { x | x l. x \<in> bin I l \<and> i \<le> l \<and> l \<le> j }"
      using \<pi>_bin_absorb by blast
  next
    fix x
    assume "x \<in> { x | x l. x \<in> bin I l \<and> i \<le> l \<and> l \<le> j }"
    then obtain l where "x \<in> bin I l" "i \<le> l" "l \<le> j"
      by blast
    moreover have "l \<noteq> k" "l \<noteq> k+1"
      using assms(2) calculation(3) leD by linarith+
    ultimately show "x \<in> { x | x l. x \<in> bin (\<pi> k I) l \<and> i \<le> l \<and> l \<le> j }"
      using \<pi>_bin_absorb by blast
  qed
  finally show ?thesis
    using bins_def by force
qed

lemma bins_\<pi>_absorb2: \<comment>\<open>TODO\<close>
  assumes "i < j"
  shows "bins (\<pi> i (bins I 0 i)) 0 j = \<pi> i (bins I 0 i)"
proof (standard; standard)
  fix x
  assume "x \<in> bins (\<pi> i (bins I 0 i)) 0 j"
  hence "x \<in> { x | x l. x \<in> bin (\<pi> i (bins I 0 i)) l \<and> l \<le> j }"
    unfolding bins_def by blast
  then show "x \<in> \<pi> i (bins I 0 i)"
    unfolding bin_def by blast
next
  fix x
  assume *: "x \<in> \<pi> i (bins I 0 i)"

  have "\<And>l. i+1 < l \<Longrightarrow> bin (\<pi> i (bins I 0 i)) l = {}"
  proof (standard; standard)
    fix l x
    assume "i+1 < l" "x \<in> bin (\<pi> i (bins I 0 i)) l"
    hence "l \<noteq> i" "l \<noteq> i+1"
      by blast+
    hence "x \<in> bin (bins I 0 i) l"
      using \<pi>_bin_absorb \<open>x \<in> bin (\<pi> i (bins I 0 i)) l\<close> by blast
    then show "x \<in> {}"
      unfolding bins_def bin_def using \<open>i+1 < l\<close> by simp
  qed

  obtain l where "x \<in> bin (\<pi> i (bins I 0 i)) l"
    using "*" bin_def by auto
  have "l \<le> i+1"
    using \<open>\<And>l. i + 1 < l \<Longrightarrow> bin (\<pi> i (bins I 0 i)) l = {}\<close> \<open>x \<in> bin (\<pi> i (bins I 0 i)) l\<close> not_le_imp_less by auto

  then show "x \<in> bins (\<pi> i (bins I 0 i)) 0 j"
    using \<open>x \<in> bin (\<pi> i (bins I 0 i)) l\<close> assms bins_def by auto
qed

lemma bins_inf_\<pi>_absorb: \<comment>\<open>TODO\<close>
  assumes "i+1 < j"
  shows "bins_inf (\<pi> i I) j = bins_inf I j"
proof (standard; standard)
  fix x
  assume "x \<in> bins_inf (\<pi> i I) j"
  show "x \<in> bins_inf I j"
    using \<open>x \<in> bins_inf (\<pi> i I) j\<close> \<pi>_bin_absorb assms bins_inf_def by auto
next
  fix x
  assume "x \<in> bins_inf I j"
  show "x \<in> bins_inf (\<pi> i I) j"
    by (metis Lattices.semilattice_sup_class.sup.orderE Q''' UnI2 \<open>x \<in> bins_inf I j\<close> bins_inf_Un)
qed

lemma w4:
  assumes "wf_items I"
  shows "funpower (Scan k \<circ> Complete k \<circ> Predict k) n I = bins_inf I (k+1) \<union> funpower (Scan k \<circ> Complete k \<circ> Predict k) n (bins I 0 k)"
proof (induction n arbitrary: I)
  case 0
  have "bins_inf I (k + 1) \<union> funpower (Scan k \<circ> Complete k \<circ> Predict k) 0 (bins I 0 k) = 
    bins_inf I (k+1) \<union> bins I 0 k"
    by simp
  also have "... = I"
    unfolding bins_inf_def bins_def bin_def by auto
  finally show ?case
    by force
next
  case (Suc n)
  let ?f = "(Scan k \<circ> Complete k \<circ> Predict k)"

  have "funpower ?f (Suc n) I = ?f (funpower ?f n I)"
    by simp
  also have "... = ?f (bins_inf I (k + 1) \<union> funpower ?f n (bins I 0 k))"
    by (metis local.Suc.IH)
  also have "... \<subseteq> bins_inf I (k+1) \<union> ?f (funpower ?f n (bins I 0 k))"
    sorry
  also have "... = bins_inf I (k + 1) \<union> funpower ?f (Suc n) (bins I 0 k)"
    by auto
  finally have 0: "funpower ?f (Suc n) I \<subseteq> bins_inf I (k + 1) \<union> funpower ?f (Suc n) (bins I 0 k)" .

  have 1: "funpower ?f (Suc n) I \<supseteq> bins_inf I (k + 1) \<union> funpower ?f (Suc n) (bins I 0 k)"
    by (smt (z3) LocalLexing.funpower.simps(2) X3 le_sup_iff local.Suc.IH subset_setmonotone sup_ge2 v3)

  show ?case
    using 0 1 by blast
  qed

lemma \<pi>_bins_split: \<comment>\<open>TODO\<close>
  assumes "wf_items I"
  shows "\<pi> k I = bins_inf I (k+1) \<union> \<pi> k (bins I 0 k)"
proof (standard; standard)
  fix x 
  assume "x \<in> \<pi> k I"
  then obtain n where "x \<in> funpower (Scan k \<circ> Complete k \<circ> Predict k) n I"
    unfolding \<pi>_def limit_def natUnion_def using bin_def by auto
  then show "x \<in> bins_inf I (k + 1) \<union> \<pi> k (bins I 0 k)"
    using w4 assms by (metis UnE UnI1 UnI2 \<pi>_def limit_elem)
next
  fix x
  assume "x \<in> bins_inf I (k + 1) \<union> \<pi> k (bins I 0 k)"
  show "x \<in> \<pi> k I"
    by (smt (z3) Orderings.order_class.dual_order.trans Q(3) Un_subset_iff X1(2) \<open>x \<in> bins_inf I (k + 1) \<union> \<pi> k (bins I 0 k)\<close> \<pi>_idempotent \<pi>_sub assms subsetD w2)
qed

lemma a0: \<comment>\<open>TODO\<close>
  assumes "wf_items I"
  shows "i < j \<Longrightarrow> \<pi> i (\<pi> j I) \<subseteq> \<pi> j (\<pi> i I)"
proof standard
  fix x
  assume *: "i < j" "x \<in> \<pi> i (\<pi> j I)"

  have "\<pi> i (\<pi> j I) = \<pi> i (bins_inf I (j+1) \<union> \<pi> j (bins I 0 j))"
    using \<pi>_bins_split assms by metis
  also have "... = bins_inf (bins_inf I (j+1) \<union> \<pi> j (bins I 0 j)) (i+1) \<union>  
                   \<pi> i (bins (bins_inf I (j+1) \<union> \<pi> j (bins I 0 j)) 0 i)"
    using \<pi>_bins_split assms wf_\<pi> by presburger
  also have "... = bins_inf (bins_inf I (j+1)) (i+1) \<union> bins_inf (\<pi> j (bins I 0 j)) (i+1) \<union>
                   \<pi> i (bins (bins_inf I (j+1) \<union> \<pi> j (bins I 0 j)) 0 i)"
    using bins_inf_Un by blast
  also have "... = bins_inf I (j+1) \<union> bins_inf (\<pi> j (bins I 0 j)) (i+1) \<union>
                   \<pi> i (bins (bins_inf I (j+1) \<union> \<pi> j (bins I 0 j)) 0 i)"
    using bins_inf_absorb *(1) by force
  also have "... = bins_inf I (j+1) \<union> bins_inf (\<pi> j (bins I 0 j)) (i+1) \<union>
                   \<pi> i (bins (bins_inf I (j+1)) 0 i \<union> bins (\<pi> j (bins I 0 j)) 0 i)"
    using bins_Un by simp
  also have "... = bins_inf I (j+1) \<union> bins_inf (\<pi> j (bins I 0 j)) (i+1) \<union>
                   \<pi> i (bins (\<pi> j (bins I 0 j)) 0 i)"
    using bins_bins_inf_empty *(1) by simp
  also have "... = bins_inf I (j+1) \<union> bins_inf (\<pi> j (bins I 0 j)) (i+1) \<union>
                   \<pi> i (bins (bins I 0 j) 0 i)"
    using bins_\<pi>_absorb *(1) by simp
  also have "... = bins_inf I (j+1) \<union> bins_inf (\<pi> j (bins I 0 j)) (i+1) \<union> \<pi> i (bins I 0 i)"
    using bins_absorb *(1) by force
  finally have 0: "\<pi> i (\<pi> j I) = bins_inf I (j+1) \<union> bins_inf (\<pi> j (bins I 0 j)) (i+1) \<union> \<pi> i (bins I 0 i)" .

  have "\<pi> j (\<pi> i I) = \<pi> j (bins_inf I (i+1) \<union> \<pi> i (bins I 0 i))"
    using assms by (metis \<pi>_bins_split)
  also have "... = bins_inf (bins_inf I (i+1) \<union> \<pi> i (bins I 0 i)) (j+1) \<union>
                   \<pi> j (bins (bins_inf I (i+1) \<union> \<pi> i (bins I 0 i)) 0 j)"
    using \<pi>_bins_split assms wf_\<pi> by simp
  also have "... = bins_inf (bins_inf I (i+1)) (j+1) \<union> bins_inf (\<pi> i (bins I 0 i)) (j+1) \<union>
                   \<pi> j (bins (bins_inf I (i+1) \<union> \<pi> i (bins I 0 i)) 0 j)"
    using bins_inf_Un by blast
  also have "... = bins_inf I (j+1) \<union> bins_inf (\<pi> i (bins I 0 i)) (j+1) \<union>
                   \<pi> j (bins (bins_inf I (i+1) \<union> \<pi> i (bins I 0 i)) 0 j)"
    by (simp add: *(1) bins_inf_absorb)
  also have "... = bins_inf I (j+1) \<union> bins_inf (bins I 0 i) (j+1) \<union>
                   \<pi> j (bins (bins_inf I (i+1) \<union> \<pi> i (bins I 0 i)) 0 j)"
    using bins_inf_\<pi>_absorb *(1) by simp
  also have "... = bins_inf I (j+1) \<union> \<pi> j (bins (bins_inf I (i+1) \<union> \<pi> i (bins I 0 i)) 0 j)"
    using bins_inf_bins_empty *(1) by simp
  also have "... = bins_inf I (j+1) \<union> \<pi> j (bins (bins_inf I (i+1)) 0 j \<union> bins (\<pi> i (bins I 0 i)) 0 j)"
    using bins_Un by auto
  also have "... = bins_inf I (j+1) \<union> \<pi> j (bins I (i+1) j \<union> bins (\<pi> i (bins I 0 i)) 0 j)"
    using bins_bins_inf_In by simp
  also have "... = bins_inf I (j+1) \<union> \<pi> j (bins I (i+1) j \<union> \<pi> i (bins I 0 i))"
    using *(1) bins_\<pi>_absorb2 by presburger
  finally have 1: "\<pi> j (\<pi> i I) = bins_inf I (j+1) \<union> \<pi> j (bins I (i+1) j \<union> \<pi> i (bins I 0 i))" .

  consider (A) "x \<in> bins_inf I (j+1)" | (B) "x \<in> bins_inf (\<pi> j (bins I 0 j)) (i+1)" | (C) "x \<in> \<pi> i (bins I 0 i)"
    using "*"(2) 0 by fastforce
  then show "x \<in> \<pi> j (\<pi> i I)"
  proof cases
    case A
    then show ?thesis
      using 1 by blast
  next
    case B
    have "\<pi> i (bins I 0 i) \<supseteq> bins I 0 i"
      by (simp add: Q''')
    hence "\<pi> j (bins I (i+1) j \<union> \<pi> i (bins I 0 i)) \<supseteq> \<pi> j (bins I (i+1) j \<union> bins I 0 i)"
      using \<pi>_sub by (meson Orderings.order_class.order.trans le_sup_iff sup_ge1 sup_ge2)
    moreover have "bins I (i+1) j \<union> bins I 0 i = bins I 0 j"
      unfolding bins_def bin_def using *(1) Orderings.order_class.order.trans by force
    ultimately have "\<pi> j (bins I (i+1) j \<union> \<pi> i (bins I 0 i)) \<supseteq> \<pi> j (bins I 0 j)"
      by simp
    then show ?thesis
      using B 1 unfolding bins_inf_def bin_def by blast
  next
    case C
    then show ?thesis
      by (simp add: 1 X4 elem_setmonotone)
  qed
qed

lemma a1: \<comment>\<open>TODO\<close>
  "i+1 < j \<Longrightarrow> \<pi> i (\<pi> j I) \<supseteq> \<pi> j (\<pi> i I)"
  sorry

lemma Z'': \<comment>\<open>TODO\<close>
  "i \<le> j \<Longrightarrow> wf_items I \<Longrightarrow> \<pi> i (iterate1n \<pi> j I) = iterate1n \<pi> j I"
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
        using Nat.nat.discI Q''' \<open>i \<le> j\<close> a0 diff_Suc_1 le_imp_less_Suc local.Suc.IH local.iterate1n.elims subset_antisym
              local.Suc.prems by (smt (z3) local.iterate1n.simps(2) wf_iterate1n_\<pi>)
    next
      assume "\<not> i = j"
      hence "i < j"
        using \<open>i \<le> j\<close> by force
      show ?thesis
        using Q''' Suc_inject Zero_not_Suc \<open>i \<le> j\<close> a0 le_imp_less_Suc local.Suc.IH local.iterate1n.elims subset_antisym
              local.Suc.prems by (smt (z3) local.iterate1n.simps(2) wf_iterate1n_\<pi>)
    qed
  qed
qed

lemma iterate1n_idempotent: \<comment>\<open>TODO\<close>
  "i \<le> j \<Longrightarrow> wf_items I \<Longrightarrow> iterate1n \<pi> i (iterate1n \<pi> j I) = iterate1n \<pi> j I"
  by (induction i arbitrary: j) (auto simp: Z'')

lemma Q': \<comment>\<open>TODO\<close>
  assumes "i < length doc" "doc!i = a"
  assumes "x \<in> bin I i" "next_symbol x = Some a"
  shows "inc_item x (i+1) \<in> \<pi> i I"
  using Q Scan_def assms bin_def by blast

lemma B: \<comment>\<open>TODO\<close>
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
      using Q'' bin_def Suc.prems(3) by auto
    hence "inc_item x (i+1) \<in> \<pi> i (iterate1n \<pi> k I)"
      using Q' \<open>i + 1 = Suc k\<close> Suc.prems(2,4,5) by auto
    hence "inc_item x (i+1) \<in> \<pi> k (iterate1n \<pi> k I)"
      using \<open>i + 1 = Suc k\<close> by force
    hence "inc_item x (i+1) \<in> iterate1n \<pi> k I"
      using \<pi>_idempotent by (metis iterate1n.elims)
    thus ?thesis
      using Q''' by auto
  qed
qed

lemma C: \<comment>\<open>TODO\<close>
  assumes "i \<le> k" "x \<in> bin I i" "next_symbol x = Some N" "(N,\<alpha>) \<in> \<RR>"
  shows "init_item (N,\<alpha>) i \<in> iterate1n \<pi> k I"
  using assms
proof (induction k arbitrary: i x I N \<alpha>)
  case 0
  have "iterate1n \<pi> 0 I = \<pi> 0 I"
    by simp
  have "init_item (N, \<alpha>) i \<in> Predict 0 I"
    unfolding Predict_def using 0 using rule_head_def by fastforce
  then show ?case
    using Q \<open>iterate1n \<pi> 0 I = \<pi> 0 I\<close> by blast
next
  case (Suc k)
  then show ?case
  proof cases
    assume "i \<le> k"
    show ?thesis
      by (metis Q''' \<open>i \<le> k\<close> local.Suc.IH local.Suc.prems(2) local.Suc.prems(3) local.Suc.prems(4) local.iterate1n.simps(2) subsetD)
  next
    assume "\<not> i \<le> k"
    hence "i = Suc k"
      using le_SucE local.Suc.prems(1) by blast
    moreover have "x \<in> bin (iterate1n \<pi> k I) i"
      using Q'' bin_def local.Suc.prems(2) by auto
    ultimately have "init_item (N,\<alpha>) i \<in> Predict i (iterate1n \<pi> k I)"
      unfolding Predict_def rule_head_def
      using local.Suc.prems(3) local.Suc.prems(4) by fastforce
    show ?thesis
      using Q \<open>i = Suc k\<close> \<open>init_item (N, \<alpha>) i \<in> Predict i (iterate1n \<pi> k I)\<close> by force
  qed
qed

lemma D: \<comment>\<open>TODO\<close>
  assumes "i \<le> j" "j \<le> k" "x \<in> bin I i" "next_symbol x = Some N" "(N,\<alpha>) \<in> \<RR>" "i = item_origin y"
  assumes "y \<in> bin I j" "item_rule y = (N,\<alpha>)" "next_symbol y = None"
  shows "inc_item x j \<in> iterate1n \<pi> k I"
  using assms
proof (induction k arbitrary: i j x I N \<alpha> y)
  case 0
  have "j = 0"
    using "local.0.prems"(2) by auto
  hence "inc_item x 0 \<in> Complete 0 I"
    unfolding Complete_def using 0
    by (smt (verit, best) Option.option.discI UnI2 fst_conv item_defs(1) mem_Collect_eq next_symbol_def rule_head_def)
  then show ?case
    using Q(3) \<open>j = 0\<close> by auto
next
  case (Suc k)
  show ?case
  proof cases
    assume "j \<le> k"
    have "inc_item x j \<in> iterate1n \<pi> k I"
      using Suc.IH[OF _ \<open>j \<le> k\<close>] Suc.prems by blast
    then show ?thesis
      by (simp add: X4 elem_setmonotone)
  next
    assume "\<not> j \<le> k"
    hence "j = Suc k"
      using le_Suc_eq local.Suc.prems(2) by presburger
    have 0: "x \<in> bin (iterate1n \<pi> k I) (item_origin y)"
      using Q'' bin_def local.Suc.prems(3) local.Suc.prems(6) by auto
    moreover have 1: "y \<in> bin (iterate1n \<pi> k I) j"
      using Suc.prems(7) Q'' bin_def by auto
    moreover have "is_complete y"
      by (metis Option.option.distinct(1) local.Suc.prems(9) next_symbol_def)
    moreover have "next_symbol x = Some (item_rule_head y)"
      by (simp add: item_rule_head_def local.Suc.prems(4) local.Suc.prems(8) rule_head_def)
    ultimately have "inc_item x j \<in> Complete j (iterate1n \<pi> k I)"
      unfolding Complete_def by blast
    then show ?thesis
      using Q(3) \<open>j = Suc k\<close> by auto
  qed
qed

lemma p0: \<comment>\<open>TODO\<close>
  "is_terminal a \<Longrightarrow> Derivation [a] D b \<Longrightarrow> b = [a]"
  by (metis CFG.CFG.is_word_def CFG_axioms List.list.discI List.list.pred_inject(2) is_word_Derivation list_all_simps(2) local.Derivation.elims(1))

lemma X: \<comment>\<open>TODO\<close>
  "derives [] \<alpha> \<Longrightarrow> \<alpha> = []"
  by (metis CFG.CFG.is_word_def CFG_axioms List.list.pred_inject(1) derives_implies_Derivation is_word_Derivation local.Derivation.simps(1))

lemma L0: \<comment>\<open>TODO\<close>
  "is_sentence a \<Longrightarrow> derives a b \<Longrightarrow> is_sentence b"
  by (metis Derives1_sentence2 derives1_implies_Derives1 derives_induct)

lemma L1: \<comment>\<open>TODO\<close>
  "is_sentence a \<Longrightarrow> is_sentence b \<Longrightarrow> derives a a' \<Longrightarrow> derives b b' \<Longrightarrow> derives (a@b) (a'@b')"
  by (meson Derivation_append Derivation_implies_append Derivation_implies_derives Derivation_prepend L0 derives_implies_Derivation)

lemma R: \<comment>\<open>TODO\<close>
  "Derivation (a@b) D c \<Longrightarrow> \<exists>E F a' b'. Derivation a E a' \<and> Derivation b F b' \<and> c = a' @ b' \<and> length E \<le> length D \<and> length F \<le> length D"
proof (induction D arbitrary: a b)
  case Nil
  thus ?case
    by (metis local.Derivation.simps(1) order_refl)
next
  case (Cons d D)
  then obtain ab where *: "Derives1 (a@b) (fst d) (snd d) ab" "Derivation ab D c"
    by auto
  then obtain x y N \<alpha> where 
    "a@b = x @ [N] @ y" "ab = x @ \<alpha> @ y" "is_sentence x" "is_sentence y"
    "(N,\<alpha>) \<in> \<RR>" "snd d = (N,\<alpha>)" "fst d = length x"
    using * unfolding Derives1_def by blast
  show ?case
  proof (cases "length a \<le> length x")
    case True
    hence "a@b = take (length a) x @ drop (length a) x @ [N] @ y"
      by (simp add: \<open>a @ b = x @ [N] @ y\<close>)
    hence "a = take (length a) x" "b = drop (length a) x @ [N] @ y"
      by (meson True \<open>a @ b = x @ [N] @ y\<close> append_eq_append_conv_if)+
    hence "ab = take (length a) x @ drop (length a) x @ \<alpha> @ y"
      by (metis True \<open>ab = x @ \<alpha> @ y\<close> append_eq_append_conv_if)
    then obtain E F a' b' where 
      "Derivation (take (length a) x) E a'"
      "Derivation (drop (length a) x @ \<alpha> @ y) F b'"
      "c = a' @ b'"
      "length E \<le> length D"
      "length F \<le> length D"
      using Cons *(2) by blast
    have "Derivation a E a'"
      using \<open>Derivation (take (length a) x) E a'\<close> \<open>a = take (length a) x\<close> by fastforce
    have "Derives1 b (fst d - length a) (snd d) (drop (length a) x @ \<alpha> @ y)"
      unfolding Derives1_def
      by (metis *(1) Derives1_sentence1 \<open>(N, \<alpha>) \<in> \<RR>\<close> \<open>b = drop (length a) x @ [N] @ y\<close> \<open>fst d = length x\<close> \<open>snd d = (N, \<alpha>)\<close> is_sentence_concat length_drop)
    hence "Derivation b ((fst d - length a, snd d) # F) b'"
      using \<open>Derivation (drop (length a) x @ \<alpha> @ y) F b'\<close> \<open>c = a' @ b'\<close> by force
    have "length ((fst d - length a, snd d) # F) \<le> length (d # D)" "length E \<le> length (d # D)"
      by (auto simp add: \<open>length F \<le> length D\<close> \<open>length E \<le> length D\<close> le_SucI)
    then show ?thesis
      using \<open>Derivation a E a'\<close> \<open>Derivation b ((fst d - length a, snd d) # F) b'\<close> \<open>c = a' @ b'\<close> by blast
  next
    case False
    hence "a@b = x @ [N] @ take (length a - length x - 1) y @ drop (length a - length x - 1) y"
      by (simp add: \<open>a @ b = x @ [N] @ y\<close>)
    hence "a = x @ [N] @ take (length a - length x - 1) y"
      by (smt (z3) False Groups.ab_semigroup_add_class.add.commute Groups.cancel_comm_monoid_add_class.diff_cancel List.list.size(3) List.list.size(4) One_nat_def \<open>a @ b = x @ [N] @ y\<close> append_eq_conv_conj le_cases3 le_diff_iff' not_less_eq_eq plus_1_eq_Suc take_all_iff take_append)
    hence "b = drop (length a - length x - 1) y"
      by (metis List.append.assoc \<open>a @ b = x @ [N] @ y\<close> append_take_drop_id same_append_eq)
    hence "ab = x @ \<alpha> @ take (length a - length x - 1) y @ drop (length a - length x - 1) y"
      using \<open>ab = x @ \<alpha> @ y\<close> by force
    then obtain E F a' b' where
      "Derivation (x @ \<alpha> @ take (length a - length x - 1) y) E a'"
      "Derivation (drop (length a - length x - 1) y) F b'"
      "c = a' @ b'"
      "length E \<le> length D"
      "length F \<le> length D"
      using Cons.IH[of "x @ \<alpha> @ take (length a - length x - 1) y" "drop (length a - length x - 1) y"] *(2) by auto
    hence "Derivation b F b'"
      using \<open>b = drop (length a - length x - 1) y\<close> by blast
    have "Derives1 a (fst d) (snd d) (x @ \<alpha> @ take (length a - length x - 1) y)"
      unfolding Derives1_def
      by (metis \<open>(N, \<alpha>) \<in> \<RR>\<close> \<open>a = x @ [N] @ take (length a - length x - 1) y\<close> \<open>fst d = length x\<close> \<open>is_sentence x\<close> \<open>is_sentence y\<close> \<open>snd d = (N, \<alpha>)\<close> append_take_drop_id is_sentence_concat)
    hence "Derivation a ((fst d, snd d) # E) a'"
      using \<open>Derivation (x @ \<alpha> @ take (length a - length x - 1) y) E a'\<close> by fastforce
    have "length ((fst d, snd d) # E) \<le> length (d # D)" "length F \<le> length (d # D)"
      by (auto simp: \<open>length E \<le> length D\<close> \<open>length F \<le> length D\<close> le_SucI)
    then show ?thesis
      using \<open>Derivation a ((fst d, snd d) # E) a'\<close> \<open>Derivation b F b'\<close> \<open>c = a' @ b'\<close> by blast
  qed
qed

lemma R': \<comment>\<open>TODO\<close>
  assumes "Derivation (a#as) D (slice i k doc)" "i \<le> k"
  shows "\<exists>E F j. Derivation [a] E (slice i j doc) \<and> Derivation as F (slice j k doc) \<and> i \<le> j \<and> j \<le> k \<and> length E \<le> length D \<and> length F \<le> length D"
proof -
  obtain E F a' as' where "Derivation [a] E a'" "Derivation as F as'" "slice i k doc = a' @ as'" "length E \<le> length D" "length F \<le> length D"
    using assms R by (metis append_Cons append_Nil)
  thus ?thesis
    using assms(2) slice_append_Ex by blast
qed

definition partially_complete' :: "nat \<Rightarrow> items \<Rightarrow> nat \<Rightarrow> bool" where
  "partially_complete' k I l = (
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length doc \<and>
      x \<in> bin I i \<and> next_symbol x = Some a \<and>
      Derivation [a] D (slice i j doc) \<and> length D \<le> l \<longrightarrow>
      inc_item x j \<in> I)"

lemma core: \<comment>\<open>TODO\<close>
  assumes "j \<le> k" "k \<le> length doc"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> I" "wf_item x"
  assumes "Derivation (item_\<beta> x) D (slice j k doc)"
  assumes "partially_complete' k I (length D)" "wf_items I"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> I"
  using assms
proof (induction "item_\<beta> x" arbitrary: d i j k N \<alpha> x D)
  case Nil
  have "item_\<alpha> x = \<alpha>"
    using Nil(1) unfolding item_\<alpha>_def item_\<beta>_def item_rule_body_def rule_body_def
    by (metis Earley_Set.item.sel(1) drop_all_iff Nil.prems(3) snd_conv take_all)
  hence "x = Item (N,\<alpha>) (length \<alpha>) i j"
    using Nil(6) wf_item_def apply auto
    by (metis Earley_Set.item.sel(1) Earley_Set.item.sel(2) drop_all_iff item_defs(4) item_rule_body_def le_antisym local.Nil.hyps local.Nil.prems(3) rule_body_def snd_conv)
  have "Derivation [] D (slice j k doc)"
    by (simp add: local.Nil.hyps local.Nil.prems(6))
  hence "slice j k doc = []"
    using Derivation_implies_derives X by blast
  hence "j = k"
    by (metis Groups.monoid_add_class.add.right_neutral Lattices.linorder_class.min.absorb2 List.list.size(3) le_add_diff_inverse length_drop length_take local.Nil.prems(1) local.Nil.prems(2) slice_drop_take)
  then show ?case
    using \<open>x = Item (N, \<alpha>) (length \<alpha>) i j\<close> assms(4)
    using local.Nil.prems(4) by blast
next
  case (Cons b bs)

  have 2: "next_symbol x = Some b"
    by (metis List.list.simps(3) drop_0 drop_all hd_drop_conv_nth is_complete_def item_defs(4) local.Cons.hyps(2) next_symbol_def not_le nth_Cons_0)
  obtain j' E F  where 3: "Derivation [b] E (slice j j' doc)" "Derivation bs F (slice j' k doc)" "j \<le> j'" "j' \<le> k" "length E \<le> length D" "length F \<le> length D"
    using Cons(2) Cons(8) by (metis R' local.Cons.prems(1))
  have 1: "j' \<le> length doc"
    using "3"(4) local.Cons.prems(2) by auto
  have 4: "x \<in> bin I j"
    using Earley_Set.item.sel(4) assms(4) bin_def Cons.prems(3)
    using local.Cons.prems(4) by blast
  have 5: "inc_item x j' \<in> I"
    using "2" "3"(1) "3"(3) "3"(4) "3"(5) "4" local.Cons.prems(2) local.Cons.prems(7) partially_complete'_def by blast
  have 6: "inc_item x j' = Item (N,\<alpha>) (d+1) i j'"
    by (simp add: inc_item_def local.Cons.prems(3))

  have 7: "bs = item_\<beta> (Item (N,\<alpha>) (d+1) i j')"
    by (metis Earley_Set.item.sel(1) Earley_Set.item.sel(2) Groups.monoid_add_class.add.right_neutral List.list.sel(3) One_nat_def add_Suc_right drop_Suc item_defs(4) item_rule_body_def local.Cons.hyps(2) local.Cons.prems(3) tl_drop)
  have 8: "k \<le> length doc"
    by (simp add: local.Cons.prems(2))
  have 9: "wf_item (Item (N, \<alpha>) (d + 1) i j')"
    using 5 6 assms(8) wf_items_def by force
  have 11: "Derivation (item_\<beta> (Item (N, \<alpha>) (d + 1) i j')) F (slice j' k doc)"
    using 3(2) "7" by blast
  have 12: "partially_complete' k I (length F)"
    by (meson "3"(6) le_trans local.Cons.prems(7) partially_complete'_def)
  have "Item (N, \<alpha>) (length \<alpha>) i k \<in> I"
    using Cons.hyps(1)[OF 7 3(4) 8 _ _ 9] 11 using 5 6 assms(8) Cons.prems(7) "12" by force
  then show ?case
    by blast
qed

lemma partially_complete_\<I>: \<comment>\<open>TODO\<close>
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
        using "local.1.prems" by force
      moreover have "j \<le> length doc"
        using le_trans "local.1.prems" by blast
      ultimately have "j = i+1"
        using slice_singleton by metis
      hence "i < length doc"
        using \<open>j \<le> length doc\<close> discrete by blast
      hence "doc!i = a"
        using slice_nth \<open>[a] = slice i j doc\<close> \<open>j = i + 1\<close> by fastforce
      hence "inc_item x (i+1) \<in> iterate1n \<pi> k (\<I> k)"
        using B \<open>j = i + 1\<close> "1.prems" by blast
      then show ?thesis
        by (simp add: \<I>_def \<open>j = i + 1\<close> iterate1n_idempotent wf_Init wf_items_def)
    next
      assume "\<not> D = []"
      then obtain d D' where "D = d # D'"
        by (meson List.list.exhaust)
      then obtain b where *: "Derives1 [a] (fst d) (snd d) b" "Derivation b D' (slice i j doc)"
        using "1.prems" local.Derivation.simps(2) by blast
      show ?thesis
      proof cases
        assume "is_terminal a"
        then obtain N \<alpha> where "[a] = [N]" "(N,\<alpha>) \<in> \<RR>"
          using *(1) unfolding Derives1_def by (metis Cons_eq_append_conv neq_Nil_conv)
         hence "is_nonterminal a"
           by simp
        then show ?thesis
          using \<open>is_terminal a\<close> is_terminal_nonterminal by blast
      next
        assume "\<not> is_terminal a"
        then obtain N \<alpha> where "[a] = [N]" "b = \<alpha>" "(N,\<alpha>) \<in> \<RR>" "fst d = 0" "snd d = (N,\<alpha>)"
          using *(1) unfolding Derives1_def by (simp add: Cons_eq_append_conv)
        define y where y_def: "y = Item (N,\<alpha>) 0 i i"
        have "init_item (N, \<alpha>) i \<in> iterate1n \<pi> k (\<I> k)"
          using C[of i k x "\<I> k" N \<alpha>] \<open>(N, \<alpha>) \<in> \<RR>\<close> \<open>[a] = [N]\<close> "local.1.prems" by fastforce
        hence "y \<in> bin (\<I> k) i"
          unfolding init_item_def using y_def by(simp add: \<I>_def bin_def iterate1n_idempotent wf_Init wf_items_def)

        have "length D' < length D"
          using \<open>D = d # D'\<close> by fastforce
        have "partially_complete' k (\<I> k) (length D')"
          by (meson "local.1.hyps" \<open>length D' < length D\<close> le_less_trans partially_complete'_def)

        have 4: "i \<le> j"
          using "local.1.prems" order_trans by blast
        have 5: "j \<le> length doc"
          using "local.1.prems" order_trans by blast
        have 6: "y \<in> \<I> k"
          using \<open>y \<in> bin (\<I> k) i\<close> bin_def by force
        have 7: "wf_item y"
          using "6" wf_\<I> wf_items_def by blast

        have 1: "Item (N,\<alpha>) (length \<alpha>) i j \<in> \<I> k"
          using core[OF 4 5 y_def 6 7]
          by (smt (verit, best) "*"(2) "local.1.prems" Earley_Set.Earley.wf_\<I> Earley_Set.item.sel(1) Earley_Set.item.sel(2) Earley_axioms Orderings.order_class.order.trans \<open>b = \<alpha>\<close> \<open>partially_complete' k (\<I> k) (length D')\<close> drop0 item_defs(4) item_rule_body_def partially_complete'_def rule_body_def snd_conv y_def)

        have 0: "x \<in> bin (\<I> k) i"
          by (simp add: "local.1.prems")
        have 2: "next_symbol x = Some N"
          using \<open>[a] = [N]\<close> "local.1.prems" by blast
        have 3: "item_rule (Item (N,\<alpha>) (length \<alpha>) i j) = (N, \<alpha>)"
          by simp
        have "inc_item x j \<in> iterate1n \<pi> k (\<I> k)"
          using D[OF _ _ 0 2 _ _  _ 3] 1
          by (simp add: \<open>(N, \<alpha>) \<in> \<RR>\<close> bin_def is_complete_def item_rule_body_def "local.1.prems" next_symbol_def rule_body_def)
        then show ?thesis
          using \<I>_def iterate1n_idempotent wf_Init wf_items_def by force
      qed
    qed
  qed
qed

lemma partially_complete_\<II>: \<comment>\<open>TODO\<close>
  "partially_complete (length doc) \<II>"
  by (simp add: \<II>_def partially_complete_\<I>)

lemma fully_complete: \<comment>\<open>TODO\<close>
  assumes "i \<le> j" "j \<le> length doc"
  assumes "x \<in> bin \<II> i" "next_symbol x = Some a"
  assumes "Derivation [a] D (slice i j doc)"
  shows "inc_item x j \<in> \<II>"
  using assms partially_complete_\<II> unfolding partially_complete_def by blast

lemma core2: \<comment>\<open>TODO\<close>
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

lemma A: \<comment>\<open>TODO\<close>
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

lemma A': \<comment>\<open>TODO\<close>
  "derives [\<SS>] doc \<Longrightarrow> \<exists>N \<alpha>. derives \<alpha> doc \<and> (\<SS>,\<alpha>) \<in> \<RR>"
  using A by (meson Derivation_implies_derives derives_implies_Derivation)

theorem completeness: \<comment>\<open>TODO\<close>
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
    using core2 by blast
  then show ?thesis
    unfolding earley_recognized_def is_finished_def
    by (auto simp: is_complete_def item_defs, force)
qed

corollary correctness:
  "earley_recognized \<longleftrightarrow> derives [\<SS>] doc"
  using soundness completeness by blast

end

end
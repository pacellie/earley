theory Earley_Set
  imports
    "HOL-Library.While_Combinator"
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
  assumes nonempty_derives: "N \<in> \<N> \<Longrightarrow> \<not> derives [N] []"
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

fun iterate1 :: "(nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "iterate1 f 0 x = f 0 x"
| "iterate1 f (Suc n) x = f (Suc n) (iterate1 f n x)"

definition limit :: "(nat \<Rightarrow> 'a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit f x = \<Union> { iterate1 f n x | n. True }"

definition \<pi> :: "nat \<Rightarrow> items \<Rightarrow> items" where
  "\<pi> k I = limit (\<lambda>_ I. (Scan k \<circ> Complete k \<circ> Predict k) I) I"

definition \<I> :: "nat \<Rightarrow> items" where
  "\<I> k = iterate1 \<pi> k Init"

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

lemma wf_iterate:
  "wf_items I \<Longrightarrow> wf_items (iterate1 (\<lambda>_. Scan k \<circ> Complete k \<circ> Predict k) n I)"
  unfolding wf_items_def
  apply (induction n)
  apply (auto)
  apply (metis wf_Complete wf_Predict wf_Scan wf_items_def)+
  done

lemma wf_\<pi>:
  assumes "wf_items I"
  shows "wf_items (\<pi> k I)"
proof -
  {
    fix x
    assume "x \<in> \<pi> k I"
    then obtain n where "x \<in> iterate1 ((\<lambda>_ I. Scan k \<circ> Complete k \<circ> Predict k) I) n I"
      using \<pi>_def limit_def by fast
    hence "wf_item x"
      using assms wf_items_def wf_iterate by metis
  }
  thus ?thesis
    using wf_items_def by blast
qed

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

lemma sound_iterate:
  "wf_items I \<Longrightarrow> sound_items I \<Longrightarrow> sound_items (iterate1 (\<lambda>_. Scan k \<circ> Complete k \<circ> Predict k) n I)"
  by (induction n) (auto simp: sound_Scan sound_Complete sound_Predict wf_Complete wf_Predict wf_iterate)

lemma sound_\<pi>:
  assumes "wf_items I" "sound_items I"
  shows "sound_items (\<pi> k I)"
proof -
  {
    fix x
    assume "x \<in> \<pi> k I"
    then obtain n where "x \<in> iterate1 ((\<lambda>_ I. Scan k \<circ> Complete k \<circ> Predict k) I) n I"
      using \<pi>_def limit_def by fast
    hence "sound_item x"
      using assms sound_items_def sound_iterate by metis
  }
  thus ?thesis
    using sound_items_def by blast
qed

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

\<comment>\<open>TODO\<close>

subsection \<open>Completeness\<close>

definition partially_scanned :: "state \<Rightarrow> bool" where
  "partially_scanned s = (
    \<forall>m n r k i x.
      m+1 < length (bins s) \<and>
      n < length (items (bins s ! m)) \<and>
      Item r k i = items (bins s ! m) ! n \<and>
      next_symbol (Item r k i) = Some x \<and>
      doc!m = x \<and>
      (m < bin s \<or> (m = bin s \<and> n < index s)) \<longrightarrow>
    Item r (k+1) i \<in> set (items (bins s ! (m+1)))
  )"

definition complete_state :: "state \<Rightarrow> bool" where
  "complete_state s = (
    \<forall>m n r k i j x D.
      m < length (bins s) \<and>
      j \<le> m \<and>
      n < length (items (bins s ! j)) \<and>
      Item r k i = items (bins s ! j) ! n \<and>
      next_symbol (Item r k i) = Some x \<and>
      Derivation [x] D (slice j m doc) \<and>
      (m < bin s \<or> (m = bin s \<and> n < index s)) \<longrightarrow>
    Item r (k+1) i \<in> set (items (bins s ! m))
  )"

subsubsection \<open>Auxiliary lemmas\<close>

lemma m_lt_bin_bins_id:
  assumes "m < bin s"
  shows "bins s ! m = bins (earley_step s) ! m"
  using assms unfolding earley_step_def
  by (auto simp: Let_def bins_append_def scan_def predict_def complete_def split: option.split)

lemma bin_append_monotonic:
  "set (items b) \<subseteq> set (items (bin_append b is))"
  unfolding bin_append_def by simp

lemma bins_append_monotonic:
  "i < length bs \<Longrightarrow> set (items (bs!i)) \<subseteq> set (items (bins_append bs k is ! i))"
  unfolding bins_append_def using bin_append_monotonic
  by (metis nth_list_update_eq nth_list_update_neq order_refl)

lemma bin_append_union:
  "set (items (bin_append b is)) = set (items b) \<union> set is"
  unfolding bin_append_def by auto

lemma bins_append_union:
  "k < length bs \<Longrightarrow> set (items (bins_append bs k is ! k)) = set (items (bs ! k)) \<union> set is"
  unfolding bins_append_def using bin_append_union by simp

lemma bin_items_monotonic:
  "m < length (bins s) \<Longrightarrow> set (items (bins s ! m)) \<subseteq> set (items (bins (earley_step s) ! m))"
  unfolding earley_step_def using bins_append_monotonic
  by (auto simp: scan_def predict_def complete_def bins_append_def Let_def split: option.split)

lemma length_step_id:
  "length (bins s) = length (bins (earley_step s))"
  unfolding earley_step_def by (auto simp: Let_def split: option.split)

lemma bins_append_indexing_id:
  "m < length bs \<Longrightarrow> n < length (items (bs!m)) \<Longrightarrow> items (bins_append bs k is ! m) ! n = items (bs ! m) ! n"
  unfolding bins_append_def bin_append_def
  by (metis Earley.bin.sel append_same_eq list_update_append1 list_update_id nth_list_update nth_list_update_neq)

lemma m_eq_bin_bins_id:
  assumes "m = bin s" "n < length (items (bins s ! m))"
  shows "(items (bins s ! m)) ! n = (items (bins (earley_step s) ! m)) ! n"
  using assms unfolding earley_step_def
  apply (auto simp: Let_def split: option.splits)
  apply (metis bins_append_def bins_append_indexing_id complete_def list_update_beyond not_le)
   apply (simp add: bins_append_def scan_def)
  by (metis bins_append_def bins_append_indexing_id list_update_beyond not_le_imp_less predict_def)

lemma partially_scanned_earley_step:
  assumes "partially_scanned s" "wf_state s"
  shows "partially_scanned (earley_step s)"
  unfolding partially_scanned_def
proof (standard, standard, standard, standard, standard, standard, standard)
  fix m n r i k x
  assume *: "m+1 < length (bins (earley_step s)) \<and>
             n < length (items (bins (earley_step s) ! m)) \<and>
             Item r k i = items (bins (earley_step s) ! m) ! n \<and>
             next_symbol (Item r k i) = Some x \<and>
             doc!m = x \<and>
             (m < bin (earley_step s) \<or> (m = bin (earley_step s) \<and> n < index (earley_step s)))"

  hence 0: "m+1 < length (bins s)"
    using length_step_id by auto

  show "Item r (k+1) i \<in> set (items (bins (earley_step s) ! (m+1)))"
  proof cases
    assume "m < bin s"
    thus ?thesis
      using assms(1) * 0 unfolding partially_scanned_def by (smt (z3) bin_items_monotonic m_lt_bin_bins_id subsetD)
  next
    assume "\<not> m < bin s"
    hence "m = bin s"
      by (metis (no_types, lifting) * Earley.state.sel(2) Earley.state.sel(3) Suc_eq_plus1 earley_step_def gr_implies_not0 less_antisym)
    show ?thesis
    proof cases
      assume "n < index s"
      have "n < length (items (bins s ! m))"
        using \<open>m = bin s\<close> \<open>n < index s\<close> assms(2) bin_size_def wf_state_def by auto
      thus ?thesis
        by (smt (verit, ccfv_SIG) "*" "0" \<open>m = bin s\<close> \<open>n < index s\<close> assms(1) bin_items_monotonic less_or_eq_imp_le m_eq_bin_bins_id partially_scanned_def subsetD)
    next 
      assume "\<not> n < index s"
      hence "n \<ge> index s"
        by simp
      show ?thesis
      proof cases
        assume "index s = bin_size ((bins s)!(bin s))"
        show ?thesis
          using "*" \<open>\<not> n < index s\<close> \<open>index s = bin_size (bins s ! bin s)\<close> \<open>m = bin s\<close> bin_size_def earley_step_def by auto
      next
        assume "\<not> index s = bin_size ((bins s)!(bin s))"
        hence "index s < length (items (bins s ! m))"
          using \<open>m = bin s\<close> assms(2) bin_size_def wf_state_def by auto
        have "n = index s"
          by (metis (no_types, lifting) "*" Earley.state.sel(2) Earley.state.sel(3) Suc_eq_plus1 \<open>\<not> m < bin s\<close> \<open>index s \<le> n\<close> \<open>index s \<noteq> bin_size (bins s ! bin s)\<close> earley_step_def le_less_Suc_eq)

        define item where "item = (items ((bins s)!(bin s)))!index s"

        have "n < length (items (bins s ! m))"
          using \<open>index s < length (items (bins s ! m))\<close> \<open>n = index s\<close> by auto
        hence "items (bins s ! m) ! n = items (bins (earley_step s) ! m) ! n"
          using m_eq_bin_bins_id \<open>m = bin s\<close> \<open>n = index s\<close> by blast
        hence "item = Item r k i"
          by (simp add: "*" \<open>m = bin s\<close> \<open>n = index s\<close> item_def)
        have "is_terminal x"
          by (metis "*" add_less_cancel_right assms(2) is_terminal_def length_step_id nth_mem subset_code(1) valid_doc wf_state_def)

        have "bins (earley_step s) = scan x item (bins s) (bin s)"
          unfolding earley_step_def apply (auto simp: Let_def split: option.splits)
          apply (auto simp: \<open>index s \<noteq> bin_size (bins s ! bin s)\<close> item_def)
          apply (metis "*" Option.option.discI \<open>item = Item r k i\<close> item_def)
          using "*" \<open>item = Item r k i\<close> item_def apply force+
          by (metis "*" Option.option.inject \<open>is_terminal x\<close> \<open>item = Item r k i\<close> item_def)

        have "m < length doc"
          by (metis "*" add_le_cancel_right assms(2) length_step_id verit_comp_simplify1(3) wf_state_def)
        hence "scan x item (bins s) m = bins_append (bins s) (m + 1) [inc_item item]"
          unfolding scan_def using * by simp
        have "inc_item item \<in> set (items ((bins_append (bins s) (m+1) [inc_item item]) !(m+1)))"
          using "0" bins_append_union by auto
        moreover have "inc_item item = Item r (k+1) i"
          unfolding inc_item_def by (simp add: \<open>item = Item r k i\<close>)
        ultimately have "Item r (k+1) i \<in> set (items ((scan x item (bins s) m) ! (m+1)))"
          using \<open>scan x item (bins s) m = bins_append (bins s) (m + 1) [inc_item item]\<close> by simp
        thus ?thesis
          by (simp add: \<open>bins (earley_step s) = scan x item (bins s) (bin s)\<close> \<open>m = bin s\<close>)
      qed
    qed
  qed
qed

subsubsection \<open>Initial completeness\<close>

subsubsection \<open>Earley step completeness\<close>

lemma complete_state_earley_step:
  assumes "wf_state s" "sound_state s" "complete_state s" "partially_scanned s"
  shows "complete_state (earley_step s)"
  unfolding complete_state_def
proof (standard, standard, standard, standard, standard, standard, standard, standard, standard)
  fix m n r k i j x D
  assume *: "m < length (bins (earley_step s)) \<and>
             j \<le> m \<and>
             n < length (items (bins (earley_step s) ! j)) \<and>
             Item r k i = items (bins (earley_step s) ! j) ! n \<and>
             next_symbol (Item r k i) = Some x \<and>
             Derivation [x] D (slice j m doc) \<and>
             (m < bin (earley_step s) \<or> m = bin (earley_step s) \<and> n < index (earley_step s))"
  show "Item r (k + 1) i \<in> set (items (bins (earley_step s) ! m))" using *
  proof (induction D arbitrary: m n r k i j x)
    case Nil
    show ?case
    proof cases
      assume "m < length (bins s)"
      show ?thesis
        sledgehammer
    next
      assume "\<not> m < length (bins s)"
      show ?thesis
        sorry
    qed
  next
    case (Cons d D)
    show ?case
      sorry
  qed
qed

subsubsection \<open>Earley completeness\<close>

lemma complete_state_earley:
  "wf_state s \<Longrightarrow> sound_state s \<Longrightarrow> complete_state s \<Longrightarrow> partially_scanned s \<Longrightarrow> complete_state (earley s)"
  by (induction s rule: earley.induct) (auto simp: Let_def wf_state_earley_step sound_state_earley_step complete_state_earley_step partially_scanned_earley_step)

lemma
  assumes "derives \<alpha> \<beta>"
  shows "\<exists>\<BB>. (\<forall>i < length \<alpha>. \<exists>j < length \<BB>. derives ([\<alpha>!i]) (\<BB>!j)) \<and> \<beta> = concat \<BB>"
  sorry

theorem completeness:
  assumes "derives [\<SS>] doc"
  shows "earley_recognized"
  sorry

end

end
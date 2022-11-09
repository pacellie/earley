theory Earley_List
  imports 
    Earley_Set
begin

section \<open>Earley recognizer with traces\<close>

subsection \<open>List auxilaries\<close>

fun filter_with_index' :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index' _ _ [] = []"
| "filter_with_index' i P (x#xs) = (
    if P x then (x,i) # filter_with_index' (i+1) P xs
    else filter_with_index' (i+1) P xs)"

definition filter_with_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index P xs = filter_with_index' 0 P xs"

lemma filter_with_index'_P:
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> P x"
  by (induction xs arbitrary: i) (auto split: if_splits)

lemma filter_with_index_P:
  "(x, n) \<in> set (filter_with_index P xs) \<Longrightarrow> P x"
  by (metis filter_with_index'_P filter_with_index_def)

lemma filter_with_index'_cong_filter:
  "map fst (filter_with_index' i P xs) = filter P xs"
  by (induction xs arbitrary: i) auto

lemma filter_with_index_cong_filter:
  "map fst (filter_with_index P xs) = filter P xs"
  by (simp add: filter_with_index'_cong_filter filter_with_index_def)

lemma size_index_filter_with_index':
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> n \<ge> i"
  by (induction xs arbitrary: i) (auto simp: Suc_leD split: if_splits)

lemma index_filter_with_index'_lt_length:
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> n-i < length xs"
  by (induction xs arbitrary: i)(auto simp: less_Suc_eq_0_disj split: if_splits; metis Suc_diff_Suc leI)+

lemma index_filter_with_index_lt_length:
  "(x, n) \<in> set (filter_with_index P xs) \<Longrightarrow> n < length xs"
  by (metis filter_with_index_def index_filter_with_index'_lt_length minus_nat.diff_0)

lemma filter_with_index'_nth:
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> xs ! (n-i) = x"
proof (induction xs arbitrary: i)
  case (Cons y xs)
  show ?case
  proof (cases "x = y")
    case True
    thus ?thesis
      using Cons by (auto simp: nth_Cons' split: if_splits)
  next
    case False
    hence "(x, n) \<in> set (filter_with_index' (i+1) P xs)"
      using Cons.prems by (cases xs) (auto split: if_splits)
    hence "n \<ge> i + 1" "xs ! (n - i - 1) = x"
      by (auto simp: size_index_filter_with_index' Cons.IH)
    thus ?thesis
      by simp
  qed
qed simp

lemma filter_with_index_nth:
  "(x, n) \<in> set (filter_with_index P xs) \<Longrightarrow> xs ! n = x"
  by (metis diff_zero filter_with_index'_nth filter_with_index_def)


subsection \<open>Definitions\<close>

datatype pointer =
  Null
  | Pre nat
  | PreRed "(nat \<times> nat \<times> nat)" "(nat \<times> nat \<times> nat) list"

datatype 'a entry =
  Entry
    (item : "'a item")
    (pointer : pointer)

type_synonym 'a bin = "'a entry list"
type_synonym 'a bins = "'a bin list"

definition items :: "'a bin \<Rightarrow> 'a item list" where
  "items b = map item b"

definition pointers :: "'a bin \<Rightarrow> pointer list" where
  "pointers b = map pointer b"

definition bins_eq_items :: "'a bins \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "bins_eq_items bs0 bs1 \<longleftrightarrow> map items bs0 = map items bs1"

definition bins_items :: "'a bins \<Rightarrow> 'a items" where
  "bins_items bs = \<Union> { set (items (bs ! k)) | k. k < length bs }"

definition bin_items_upto :: "'a bin \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin_items_upto b i = { items b ! j | j. j < i \<and> j < length (items b) }"

definition bins_items_upto :: "'a bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bins_items_upto bs k i = \<Union> { set (items (bs ! l)) | l. l < k } \<union> bin_items_upto (bs ! k) i"

definition wf_bin_items :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a item list \<Rightarrow> bool" where
  "wf_bin_items cfg inp k xs = (\<forall>x \<in> set xs. wf_item cfg inp x \<and> item_end x = k)"

definition wf_bin :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a bin \<Rightarrow> bool" where
  "wf_bin cfg inp k b \<longleftrightarrow> distinct (items b) \<and> wf_bin_items cfg inp k (items b)"

definition wf_bins :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "wf_bins cfg inp bs \<longleftrightarrow> (\<forall>k < length bs. wf_bin cfg inp k (bs ! k))"

definition nonempty_derives :: "'a cfg \<Rightarrow> bool" where
  "nonempty_derives cfg = (\<forall>N. N \<in> set (\<NN> cfg) \<longrightarrow> \<not> derives cfg [N] [])"


subsection \<open>Main algorithm\<close>

definition Init_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "Init_it cfg inp = (
    let rs = filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg) in
    let b0 = map (\<lambda>r. (Entry (init_item r 0) Null)) rs in
    let bs = replicate (length inp + 1) ([]) in
    bs[0 := b0])"

definition Scan_it :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a  \<Rightarrow> 'a item \<Rightarrow> nat \<Rightarrow> 'a entry list" where
  "Scan_it k inp a x pre = (
    if inp!k = a then
      let x' = inc_item x (k+1) in
      [Entry x' (Pre pre)]
    else [])"

definition Predict_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a \<Rightarrow> 'a entry list" where
  "Predict_it k cfg X = (
    let rs = filter (\<lambda>r. rule_head r = X) (\<RR> cfg) in
    map (\<lambda>r. (Entry (init_item r k) Null)) rs)"

definition Complete_it :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a entry list" where
  "Complete_it k y bs red = (
    let orig = bs ! (item_origin y) in
    let is = filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items orig) in
    map (\<lambda>(x, pre). (Entry (inc_item x k) (PreRed (item_origin y, pre, red) []))) is)"

fun bin_upd :: "'a entry \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "bin_upd e' [] = [e']"
| "bin_upd e' (e#es) = (
    case (e', e) of
      (Entry x (PreRed px xs), Entry y (PreRed py ys)) \<Rightarrow> 
        if x = y then Entry x (PreRed px (py#xs@ys)) # es
        else e # bin_upd e' es
      | _ \<Rightarrow> 
        if item e' = item e then e # es
        else e # bin_upd e' es)"

fun bin_upds :: "'a entry list \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "bin_upds [] b = b"
| "bin_upds (e#es) b = bin_upds es (bin_upd e b)"

definition bins_upd :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a entry list \<Rightarrow> 'a bins" where
  "bins_upd bs k es = bs[k := bin_upds es (bs!k)]"

partial_function (tailrec) \<pi>_it' :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a bins" where
  "\<pi>_it' k cfg inp bs i = (
    if i \<ge> length (items (bs ! k)) then bs
    else
      let x = items (bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow>
            if is_terminal cfg a then
              if k < length inp then bins_upd bs (k+1) (Scan_it k inp a x i)
              else bs
            else bins_upd bs k (Predict_it k cfg a)
        | None \<Rightarrow> bins_upd bs k (Complete_it k x bs i)
      in \<pi>_it' k cfg inp bs' (i+1))"

declare \<pi>_it'.simps[code]

definition \<pi>_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a bins" where
  "\<pi>_it k cfg inp bs = \<pi>_it' k cfg inp bs 0"

fun \<I>_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "\<I>_it 0 cfg inp = \<pi>_it 0 cfg inp (Init_it cfg inp)"
| "\<I>_it (Suc n) cfg inp = \<pi>_it (Suc n) cfg inp (\<I>_it n cfg inp)"

definition \<II>_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "\<II>_it cfg inp = \<I>_it (length inp) cfg inp"


subsection \<open>Bin lemmas\<close>

lemma length_bins_upd[simp]:
  "length (bins_upd bs k es) = length bs"
  unfolding bins_upd_def by simp

lemma length_bin_upd:
  "length (bin_upd e b) \<ge> length b"
  by (induction e b rule: bin_upd.induct) (auto split: pointer.splits entry.splits)

lemma length_bin_upds:
  "length (bin_upds es b) \<ge> length b"
  by (induction es arbitrary: b) (auto, meson le_trans length_bin_upd)

lemma length_items_pointers_eq:
  "length (items b) = length (pointers b)"
  by (simp add: items_def pointers_def)

lemma length_nth_bin_bins_upd:
  "length (bins_upd bs k es ! n) \<ge> length (bs ! n)"
  unfolding bins_upd_def using length_bin_upds
  by (metis linorder_not_le list_update_beyond nth_list_update_eq nth_list_update_neq order_refl)

lemma nth_idem_bins_upd:
  "k \<noteq> n \<Longrightarrow> bins_upd bs k es ! n = bs ! n"
  unfolding bins_upd_def by simp

lemma items_nth_idem_bin_upd:
  "n < length b \<Longrightarrow> items (bin_upd e b) ! n = items b ! n"
  by (induction b arbitrary: e n) (auto simp: items_def less_Suc_eq_0_disj split!: entry.split pointer.split)

lemma items_nth_idem_bin_upds:
  "n < length b \<Longrightarrow> items (bin_upds es b) ! n = items b ! n"
  by (induction es arbitrary: b) 
    (auto, metis items_def items_nth_idem_bin_upd length_bin_upd nth_map order.strict_trans2)

lemma items_nth_idem_bins_upd:
  "n < length (bs ! k) \<Longrightarrow> items (bins_upd bs k es ! k) ! n = items (bs ! k) ! n"
  unfolding bins_upd_def using items_nth_idem_bin_upds
  by (metis linorder_not_less list_update_beyond nth_list_update_eq)

lemma bin_items_upto_eq_set_items:
  "i \<ge> length b \<Longrightarrow> bin_items_upto b i = set (items b)"
  by (auto simp: bin_items_upto_def items_def, metis in_set_conv_nth nth_map order_le_less order_less_trans)

lemma bins_items_upto_empty:
  "bins_items_upto bs 0 0 = {}"
  unfolding bins_items_upto_def bin_items_upto_def by simp

lemma set_items_bin_upd:
  "set (items (bin_upd e b)) = set (items b) \<union> {item e}"
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> b = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = Entry x (PreRed xp xs)" "b = Entry y (PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons.IH by (auto simp: items_def)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item b"
      hence "bin_upd e (b # bs) = b # bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * by (auto simp: items_def)
    next
      assume *: "\<not> item e = item b"
      hence "bin_upd e (b # bs) = b # bin_upd e bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons.IH by (auto simp: items_def)
    qed
  qed
qed (auto simp: items_def)

lemma set_items_bin_upds:
  "set (items (bin_upds es b)) = set (items b) \<union> set (items es)"
  using set_items_bin_upd by (induction es arbitrary: b) (auto simp: items_def, blast, force+)

lemma bins_bins_upd:
  assumes "k < length bs"
  shows "bins_items (bins_upd bs k es) = bins_items bs \<union> set (items es)"
proof -
  let ?bs = "bins_upd bs k es"
  have "bins_items (bins_upd bs k es) = \<Union> {set (items (?bs ! k)) |k. k < length ?bs}"
    unfolding bins_items_def by blast
  also have "... = \<Union> {set (items (bs ! l)) |l. l < length bs \<and> l \<noteq> k} \<union> set (items (?bs ! k))"
    unfolding bins_upd_def using assms by (auto, metis nth_list_update)
  also have "... = \<Union> {set (items (bs ! l)) |l. l < length bs \<and> l \<noteq> k} \<union> set (items (bs ! k)) \<union> set (items es)"
    using set_items_bin_upds[of es "bs!k"] by (simp add: assms bins_upd_def sup_assoc)
  also have "... = \<Union> {set (items (bs ! k)) |k. k < length bs} \<union> set (items es)"
    using assms by blast
  also have "... = bins_items bs \<union> set (items es)"
    unfolding bins_items_def by blast
  finally show ?thesis .
qed

lemma kth_bin_sub_bins:
  "k < length bs \<Longrightarrow> set (items (bs ! k)) \<subseteq> bins_items bs"
  unfolding bins_items_def bins_items_upto_def bin_items_upto_def by blast+

lemma bin_items_upto_Cons_0:
  "bin_items_upto (e#es) 0 = {}"
  by (auto simp: bin_items_upto_def)

lemma bin_items_upto_Cons:
  assumes "0 < n"
  shows "bin_items_upto (e#es) n = { item e } \<union> bin_items_upto es (n-1)"
proof -
  have "bin_items_upto (e#es) n = { items (e#es) ! j | j. j < n \<and> j < length (items (e#es)) }"
    unfolding bin_items_upto_def by blast
  also have "... = { item e } \<union> { items es ! j | j. j < (n-1) \<and> j < length (items es) }"
    using assms by (cases n) (auto simp: items_def nth_Cons', metis One_nat_def Zero_not_Suc diff_Suc_1 not_less_eq nth_map)
  also have "... = { item e } \<union> bin_items_upto es (n-1)"
    unfolding bin_items_upto_def by blast
  finally show ?thesis .
qed

lemma bin_items_upto_nth_idem_bin_upd:
  "n < length b \<Longrightarrow> bin_items_upto (bin_upd e b) n = bin_items_upto b n"
proof (induction b arbitrary: e n)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> b = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = Entry x (PreRed xp xs)" "b = Entry y (PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons bin_items_upto_Cons_0
      by (cases n) (auto simp: items_def bin_items_upto_Cons, blast+)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item b"
      hence "bin_upd e (b # bs) = b # bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * by (auto simp: items_def)
    next
      assume *: "\<not> item e = item b"
      hence "bin_upd e (b # bs) = b # bin_upd e bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons bin_items_upto_Cons_0
        by (cases n) (auto simp: items_def bin_items_upto_Cons, blast+)
    qed
  qed
qed (auto simp: items_def)

lemma bin_items_upto_nth_idem_bin_upds:
  "n < length b \<Longrightarrow> bin_items_upto (bin_upds es b) n = bin_items_upto b n"
  using bin_items_upto_nth_idem_bin_upd length_bin_upd
  apply (induction es arbitrary: b) apply auto
  using order.strict_trans2 order.strict_trans1 by blast+

lemma bins_items_upto_kth_nth_idem:
  assumes "l < length bs" "k \<le> l" "n < length (bs ! k)"
  shows "bins_items_upto (bins_upd bs l es) k n = bins_items_upto bs k n"
proof -
  let ?bs = "bins_upd bs l es"
  have "bins_items_upto ?bs k n = \<Union> {set (items (?bs ! l)) |l. l < k} \<union> bin_items_upto (?bs ! k) n"
    unfolding bins_items_upto_def by blast
  also have "... = \<Union> {set (items (bs ! l)) |l. l < k} \<union> bin_items_upto (?bs ! k) n"
    unfolding bins_upd_def using assms(1,2) by auto
  also have "... = \<Union> {set (items (bs ! l)) |l. l < k} \<union> bin_items_upto (bs ! k) n"
    unfolding bins_upd_def using assms(1,3) bin_items_upto_nth_idem_bin_upds
    by (metis (no_types, lifting) nth_list_update)
  also have "... = bins_items_upto bs k n"
    unfolding bins_items_upto_def by blast
  finally show ?thesis .
qed

lemma bins_items_upto_sub_bins_items:
  "k < length bs \<Longrightarrow> bins_items_upto bs k n \<subseteq> bins_items bs"
  unfolding bins_items_def bins_items_upto_def bin_items_upto_def using less_trans by (auto, blast)

lemma bins_items_upto_Suc_Un:
  "n < length (bs ! k) \<Longrightarrow> bins_items_upto bs k (n+1) = bins_items_upto bs k n \<union> { items (bs ! k) ! n }"
  unfolding bins_items_upto_def bin_items_upto_def using less_Suc_eq by (auto simp: items_def, metis nth_map)

lemma bins_items_upto_Suc_eq:
  "n \<ge> length (bs ! k) \<Longrightarrow> bins_items_upto bs k (n+1) = bins_items_upto bs k n"
  unfolding bins_items_upto_def bin_items_upto_def by (auto; metis dual_order.strict_trans1 items_def length_map)

lemma bins_bin_exists:
  "x \<in> bins_items bs \<Longrightarrow> \<exists>k < length bs. x \<in> set (items (bs ! k))"
  unfolding bins_items_def by blast

lemma distinct_bin_upd:
  "distinct (items b) \<Longrightarrow> distinct (items (bin_upd e b))"
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> b = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = Entry x (PreRed xp xs)" "b = Entry y (PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons
      apply (auto simp: items_def)
      by (metis Un_insert_right entry.sel(1) imageI items_def list.set_map list.simps(15) set_ConsD set_items_bin_upd sup_bot_right)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item b"
      hence "bin_upd e (b # bs) = b # bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons.prems by (auto simp: items_def)
    next
      assume *: "\<not> item e = item b"
      hence "bin_upd e (b # bs) = b # bin_upd e bs"
        using False by (auto split: pointer.splits entry.splits)
      moreover have "distinct (items (bin_upd e bs))"
        using Cons by (auto simp: items_def)
      ultimately show ?thesis
        using * Cons.prems set_items_bin_upd
        by (metis Un_insert_right distinct.simps(2) insertE items_def list.simps(9) sup_bot_right)
    qed
  qed
qed (auto simp: items_def)

lemma distinct_bin_upds:
  "distinct (items b)  \<Longrightarrow> distinct (items (bin_upds es b))"
  by (induction es arbitrary: b) (auto simp: distinct_bin_upd)

lemma distinct_bins_upd:
  "distinct (items (bs ! k)) \<Longrightarrow> distinct (items (bins_upd bs k ips ! k))"
  by (metis bins_upd_def distinct_bin_upds leI list_update_beyond nth_list_update)

lemma wf_bins_kth_bin:
  "wf_bins cfg inp bs \<Longrightarrow> k < length bs \<Longrightarrow> x \<in> set (items (bs ! k)) \<Longrightarrow> wf_item cfg inp x \<and> item_end x = k"
  using wf_bin_def wf_bins_def wf_bin_items_def by blast

lemma wf_bin_bin_upd:
  assumes "wf_bin cfg inp k b" "wf_item cfg inp (item e) \<and> item_end (item e) = k"
  shows "wf_bin cfg inp k (bin_upd e b)"
  using assms
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> b = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = Entry x (PreRed xp xs)" "b = Entry y (PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons distinct_bin_upd wf_bin_def wf_bin_items_def set_items_bin_upd
      by (smt (verit, best) Un_insert_right insertE sup_bot.right_neutral)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item b"
      hence "bin_upd e (b # bs) = b # bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons.prems by (auto simp: items_def)
    next
      assume *: "\<not> item e = item b"
      hence "bin_upd e (b # bs) = b # bin_upd e bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons.prems set_items_bin_upd distinct_bin_upd wf_bin_def wf_bin_items_def
        by (smt (verit, best) Un_insert_right insertE sup_bot_right)
    qed
  qed
qed (auto simp: items_def wf_bin_def wf_bin_items_def)

lemma wf_bin_bin_upds:
  assumes "wf_bin cfg inp k b" "distinct (items es)"
  assumes "\<forall>x \<in> set (items es). wf_item cfg inp x \<and> item_end x = k"
  shows "wf_bin cfg inp k (bin_upds es b)"
  using assms by (induction es arbitrary: b) (auto simp: wf_bin_bin_upd items_def)

lemma wf_bins_bins_upd:
  assumes "wf_bins cfg inp bs" "distinct (items es)"
  assumes "\<forall>x \<in> set (items es). wf_item cfg inp x \<and> item_end x = k"
  shows "wf_bins cfg inp (bins_upd bs k es)"
  unfolding bins_upd_def using assms wf_bin_bin_upds wf_bins_def
  by (metis length_list_update nth_list_update_eq nth_list_update_neq)

lemma wf_bins_impl_wf_items:
  "wf_bins cfg inp bs \<Longrightarrow> wf_items cfg inp (bins_items bs)"
  unfolding wf_bins_def wf_bin_def wf_items_def wf_bin_items_def bins_items_def by auto

lemma bin_upd_eq_items:
  "item e \<in> set (items b) \<Longrightarrow> set (items (bin_upd e b)) = set (items b)"
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> b = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = Entry x (PreRed xp xs)" "b = Entry y (PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons set_items_bin_upd by (metis Un_insert_right insert_absorb sup_bot_right)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item b"
      hence "bin_upd e (b # bs) = b # bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons.prems by (auto simp: items_def)
    next
      assume *: "\<not> item e = item b"
      hence "bin_upd e (b # bs) = b # bin_upd e bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons.prems set_items_bin_upd by (metis Un_insert_right insert_absorb sup_bot_right)
    qed
  qed
qed (auto simp: items_def)

lemma bin_upds_eq_items:
  "set (items es) \<subseteq> set (items b) \<Longrightarrow> set (items (bin_upds es b)) = set (items b)"
  apply (induction es arbitrary: b)
  apply (auto simp: set_items_bin_upd set_items_bin_upds)
  apply (simp add: items_def)
  by (metis Un_iff Un_subset_iff items_def list.simps(9) set_subset_Cons)

lemma bins_upd_eq_items:
  "set (items es) \<subseteq> set (items (bs!k)) \<Longrightarrow> bins_items (bins_upd bs k es) = bins_items bs"
  using bins_bins_upd kth_bin_sub_bins bins_upd_def
  by (metis (no_types, opaque_lifting) dual_order.trans linorder_not_le list_update_beyond sup.orderE)

lemma bin_eq_items_bin_upd:
  "item e \<in> set (items b) \<Longrightarrow> items (bin_upd e b) = items b"
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> b = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = Entry x (PreRed xp xs)" "b = Entry y (PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons by (auto simp: items_def)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item b"
      hence "bin_upd e (b # bs) = b # bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons.prems by (auto simp: items_def)
    next
      assume *: "\<not> item e = item b"
      hence "bin_upd e (b # bs) = b # bin_upd e bs"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using * Cons by (auto simp: items_def)
    qed
  qed
qed (auto simp: items_def)

lemma bin_eq_items_bin_upds:
  assumes "set (items es) \<subseteq> set (items b)"
  shows "items (bin_upds es b) = items b"
  using assms
proof (induction es arbitrary: b)
  case (Cons e es)
  have "items (bin_upds es (bin_upd e b)) = items (bin_upd e b)"
    using Cons bin_upds_eq_items set_items_bin_upd set_items_bin_upds
    by (metis Un_upper2 bin_upds.simps(2) sup.coboundedI1)
  moreover have "items (bin_upd e b) = items b"
    using bin_eq_items_bin_upd Cons.prems by (auto simp: items_def)
  ultimately show ?case
    by simp
qed (auto simp: items_def)
  
lemma bins_eq_items_bins_upd:
  assumes "set (items es) \<subseteq> set (items (bs!k))"
  shows "bins_eq_items (bins_upd bs k es) bs"
  unfolding bins_upd_def using assms bin_eq_items_bin_upds bins_eq_items_def
  by (metis list_update_id map_update)

lemma bins_eq_items_imp_eq_bins_items:
  "bins_eq_items bs bs' \<Longrightarrow> bins_items bs = bins_items bs'"
  unfolding bins_eq_items_def bins_items_def items_def
  by (metis (no_types, lifting) length_map nth_map)

lemma bin_eq_items_dist_bin_upd_bin:
  assumes "items a = items b"
  shows "items (bin_upd e a) = items (bin_upd e b)"
  using assms
proof (induction a arbitrary: e b)
  case (Cons a as)
  obtain b' bs where bs: "b = b' # bs" "item a = item b'" "items as = items bs"
    using Cons.prems by (auto simp: items_def)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> a = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where #: "e = Entry x (PreRed xp xs)" "a = Entry y (PreRed yp ys)"
      by blast
    show ?thesis
    proof cases
      assume *: "x = y"
      hence "items (bin_upd e (a # as)) = x # items as"
        using # by (auto simp: items_def)
      moreover have "items (bin_upd e (b' # bs)) = x # items bs"
        using bs # * by (auto simp: items_def split: pointer.splits entry.splits)
      ultimately show ?thesis
        using bs by simp
    next
      assume *: "\<not> x = y"
      hence "items (bin_upd e (a # as)) = y # items (bin_upd e as)"
        using # by (auto simp: items_def)
      moreover have "items (bin_upd e (b' # bs)) = y # items (bin_upd e bs)"
        using bs # * by (auto simp: items_def split: pointer.splits entry.splits)
      ultimately show ?thesis
        using bs Cons.IH by simp
    qed
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item a"
      hence "items (bin_upd e (a # as)) = item a # items as"
        using False by (auto simp: items_def split: pointer.splits entry.splits)
      moreover have "items (bin_upd e (b' # bs)) = item b' # items bs"
        using bs False * by (auto simp: items_def split: pointer.splits entry.splits)
      ultimately show ?thesis
        using bs by simp
    next
      assume *: "\<not> item e = item a"
      hence "items (bin_upd e (a # as)) = item a # items (bin_upd e as)"
        using False by (auto simp: items_def split: pointer.splits entry.splits)
      moreover have "items (bin_upd e (b' # bs)) = item b' # items (bin_upd e bs)"
        using bs False * by (auto simp: items_def split: pointer.splits entry.splits)
      ultimately show ?thesis
        using bs Cons by simp
    qed
  qed
qed (auto simp: items_def)

lemma bin_eq_items_dist_bin_upds_bin:
  assumes "items a = items b"
  shows "items (bin_upds es a) = items (bin_upds es b)"
  using assms
proof (induction es arbitrary: a b)
  case (Cons e es)
  hence "items (bin_upds es (bin_upd e a)) = items (bin_upds es (bin_upd e b))"
    using bin_eq_items_dist_bin_upd_bin by blast
  thus ?case
    by simp
qed simp

lemma bin_eq_items_dist_bin_upd_entry:
  assumes "item e = item e'"
  shows "items (bin_upd e b) = items (bin_upd e' b)"
  using assms
proof (induction b arbitrary: e e')
  case (Cons a as)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> a = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where #: "e = Entry x (PreRed xp xs)" "a = Entry y (PreRed yp ys)"
      by blast
    show ?thesis
    proof cases
      assume *: "x = y"
      thus ?thesis
        using # Cons.prems by (auto simp: items_def split: pointer.splits entry.splits)
    next
      assume *: "\<not> x = y"
      thus ?thesis
        using # Cons.prems
        by (auto simp: items_def split!: pointer.splits entry.splits, metis Cons.IH Cons.prems items_def)+
    qed
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item a"
      thus ?thesis
        using Cons.prems by (auto simp: items_def split: pointer.splits entry.splits)
    next
      assume *: "\<not> item e = item a"
      thus ?thesis
        using Cons.prems
        by (auto simp: items_def split!: pointer.splits entry.splits, metis Cons.IH Cons.prems items_def)+
    qed
  qed
qed (auto simp: items_def)

lemma bin_eq_items_dist_bin_upds_entries:
  assumes "items es = items es'"
  shows "items (bin_upds es b) = items (bin_upds es' b)"
  using assms
proof (induction es arbitrary: es' b)
  case (Cons e es)
  then obtain e' es'' where "item e = item e'" "items es = items es''" "es' = e' # es''"
    by (auto simp: items_def)
  hence "items (bin_upds es (bin_upd e b)) = items (bin_upds es'' (bin_upd e' b))"
    using Cons.IH
    by (metis bin_eq_items_dist_bin_upd_entry bin_eq_items_dist_bin_upds_bin)
  thus ?case
    by (simp add: \<open>es' = e' # es''\<close>)
qed (auto simp: items_def)

lemma bins_eq_items_dist_bins_upd:
  assumes "bins_eq_items as bs" "items aes = items bes" "k < length as"
  shows "bins_eq_items (bins_upd as k aes) (bins_upd bs k bes)"
proof -
  have "k < length bs"
    using assms(1,3) bins_eq_items_def map_eq_imp_length_eq by metis
  hence "items (bin_upds (as!k) aes) = items (bin_upds (bs!k) bes)"
    using bin_eq_items_dist_bin_upds_entries bin_eq_items_dist_bin_upds_bin bins_eq_items_def assms
    by (metis (no_types, lifting) nth_map)
  thus ?thesis
    using \<open>k < length bs\<close> assms bin_eq_items_dist_bin_upds_bin bin_eq_items_dist_bin_upds_entries
      bins_eq_items_def bins_upd_def by (smt (verit) map_update nth_map)
qed

subsection \<open>Well-formed bins\<close>

lemma distinct_Scan_it:
  "distinct (items (Scan_it k inp a x pre))"
  unfolding Scan_it_def by (auto simp: items_def)

lemma distinct_Predict_it:
  "wf_cfg cfg \<Longrightarrow> distinct (items (Predict_it k cfg X))"
  unfolding Predict_it_def wf_cfg_defs by (auto simp: init_item_def rule_head_def distinct_map inj_on_def items_def)

lemma inj_on_inc_item:
  "\<forall>x \<in> A. item_end x = l \<Longrightarrow> inj_on (\<lambda>x. inc_item x k) A"
  unfolding inj_on_def inc_item_def by (simp add: item.expand)
  
lemma distinct_Complete_it:
  assumes "wf_bins cfg inp bs" "item_origin y < length bs"
  shows "distinct (items (Complete_it k y bs red))"
proof -
  let ?orig = "bs ! (item_origin y)"
  let ?is = "filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"
  let ?is' = "map (\<lambda>(x, pre). (Entry (inc_item x k) (PreRed (item_origin y, pre, red) []))) ?is"
  have wf: "wf_bin cfg inp (item_origin y) ?orig"
    using assms wf_bins_def by blast
  have 0: "\<forall>x \<in> set (map fst ?is). item_end x = (item_origin y)"
    using wf wf_bin_def wf_bin_items_def filter_is_subset filter_with_index_cong_filter by (metis in_mono)
  hence "distinct (items ?orig)"
    using wf unfolding wf_bin_def by blast
  hence "distinct (map fst ?is)"
    using filter_with_index_cong_filter distinct_filter by metis
  moreover have "items ?is' = map (\<lambda>x. inc_item x k) (map fst ?is)"
    by (induction ?is) (auto simp: items_def)
  moreover have "inj_on (\<lambda>x. inc_item x k) (set (map fst ?is))"
    using inj_on_inc_item 0 by blast
  ultimately have "distinct (items ?is')"
    using distinct_map by metis
  thus ?thesis
    unfolding Complete_it_def by simp
qed

lemma wf_bins_Scan_it':
  assumes "wf_bins cfg inp bs" "k < length bs" "x \<in> set (items (bs ! k))"
  assumes "k < length inp" "next_symbol x \<noteq> None" "y = inc_item x (k+1)"
  shows "wf_item cfg inp y \<and> item_end y = k+1"
  using assms wf_bins_kth_bin[OF assms(1-3)]
  unfolding wf_item_def inc_item_def next_symbol_def is_complete_def item_rule_body_def
  by (auto split: if_splits)

lemma wf_bins_Scan_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "x \<in> set (items (bs ! k))" "k < length inp" "next_symbol x \<noteq> None"
  shows "\<forall>y \<in> set (items (Scan_it k inp a x pre)). wf_item cfg inp y \<and> item_end y = (k+1)"
  using wf_bins_Scan_it'[OF assms] by (simp add: Scan_it_def items_def)

lemma wf_bins_Predict_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "k \<le> length inp" "wf_cfg cfg"
  shows "\<forall>y \<in> set (items (Predict_it k cfg X)). wf_item cfg inp y \<and> item_end y = k"
  using assms by (auto simp: Predict_it_def wf_item_def wf_bins_def wf_bin_def init_item_def wf_cfg_defs items_def)

lemma wf_item_inc_item:
  assumes "wf_item cfg inp x" "next_symbol x = Some a" "item_origin x \<le> k" "k \<le> length inp"
  shows "wf_item cfg inp (inc_item x k) \<and> item_end (inc_item x k) = k"
  using assms by (auto simp: wf_item_def inc_item_def item_rule_body_def next_symbol_def is_complete_def split: if_splits)

lemma wf_bins_Complete_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "y \<in> set (items (bs ! k))"
  shows "\<forall>x \<in> set (items (Complete_it k y bs red)). wf_item cfg inp x \<and> item_end x = k"
proof -
  let ?orig = "bs ! (item_origin y)"
  let ?is = "filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"
  let ?is' = "map (\<lambda>(x, pre). (Entry (inc_item x k) (PreRed (item_origin y, pre, red) []))) ?is"
  {
    fix x
    assume *: "x \<in> set (map fst ?is)"
    have "item_end x = item_origin y"
      using * assms wf_bins_kth_bin wf_item_def filter_with_index_cong_filter
      by (metis dual_order.strict_trans2 filter_is_subset subsetD)
    have "wf_item cfg inp x"
      using * assms wf_bins_kth_bin wf_item_def filter_with_index_cong_filter
      by (metis dual_order.strict_trans2 filter_is_subset subsetD)
    moreover have "next_symbol x = Some (item_rule_head y)"
      using * filter_set filter_with_index_cong_filter member_filter by metis
    moreover have "item_origin x \<le> k"
      using \<open>item_end x = item_origin y\<close> \<open>wf_item cfg inp x\<close> assms wf_bins_kth_bin wf_item_def
      by (metis dual_order.order_iff_strict dual_order.strict_trans1)
    moreover have "k \<le> length inp"
      using assms wf_bins_kth_bin wf_item_def by blast
    ultimately have "wf_item cfg inp (inc_item x k)" "item_end (inc_item x k) = k"
      by (simp_all add: wf_item_inc_item)
  }
  hence "\<forall>x \<in> set (items ?is'). wf_item cfg inp x \<and> item_end x = k"
    by (auto simp: items_def rev_image_eqI)
  thus ?thesis
    unfolding Complete_it_def by presburger
qed

lemma Ex_wf_bins:
  "\<exists>n bs inp cfg. n \<le> length inp \<and> length bs = Suc (length inp) \<and> wf_cfg cfg \<and> wf_bins cfg inp bs"
  apply (rule exI[where x="0"])
  apply (rule exI[where x="[[]]"])
  apply (rule exI[where x="[]"])
  apply (auto simp: wf_bins_def wf_bin_def wf_cfg_defs wf_bin_items_def items_def split: prod.splits)
  by (metis cfg.sel distinct.simps(1) empty_iff empty_set inf_bot_right list.set_intros(1))

definition wellformed_bins :: "(nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins) set" where
  "wellformed_bins = { 
    (k, cfg, inp, bs) | k cfg inp bs.
      k \<le> length inp \<and>
      length bs = length inp + 1 \<and>
      wf_cfg cfg \<and>
      wf_bins cfg inp bs
  }"

typedef 'a wf_bins = "wellformed_bins::(nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins) set"
  morphisms from_wf_bins to_wf_bins
  using Ex_wf_bins by (auto simp: wellformed_bins_def)

lemma wellformed_bins_elim:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "k \<le> length inp \<and> k < length bs \<and> length bs = length inp + 1 \<and> wf_cfg cfg \<and> wf_bins cfg inp bs"
  using assms(1) from_wf_bins wellformed_bins_def by (smt (verit) Suc_eq_plus1 less_Suc_eq_le mem_Collect_eq prod.sel(1) snd_conv)

lemma wellformed_bins_intro:
  assumes "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
  shows "(k, cfg, inp, bs) \<in> wellformed_bins"
  by (simp add: assms wellformed_bins_def)

lemma wellformed_bins_Complete_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = None"
  shows "(k, cfg, inp, bins_upd bs k (Complete_it k x bs red)) \<in> wellformed_bins"
proof -
  have *: "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using wellformed_bins_elim assms(1) by metis+
  have x: "x \<in> set (items (bs ! k))"
    using assms(2,3) by simp
  have "item_origin x < length bs"
    using x wf_bins_kth_bin *(1,2,4) wf_item_def 
    by (metis One_nat_def add.right_neutral add_Suc_right dual_order.trans le_imp_less_Suc)
  hence "wf_bins cfg inp (bins_upd bs k (Complete_it k x bs red))"
    using *(1,2,4) Suc_eq_plus1 distinct_Complete_it le_imp_less_Suc wf_bins_Complete_it wf_bins_bins_upd x by metis
  thus ?thesis
    by (simp add: *(1-3) wellformed_bins_def)
qed

lemma wellformed_bins_Scan_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = Some a"
  assumes "is_terminal cfg a" "k < length inp"
  shows "(k, cfg, inp, bins_upd bs (k+1) (Scan_it k inp a x pre)) \<in> wellformed_bins"
proof -
  have *: "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using wellformed_bins_elim assms(1) by metis+
  have x: "x \<in> set (items(bs ! k))"
    using assms(2,3) by simp
  have "wf_bins cfg inp (bins_upd bs (k+1) (Scan_it k inp a x pre))"
    using * x assms(1,4,6) distinct_Scan_it wf_bins_Scan_it wf_bins_bins_upd wellformed_bins_elim
    by (metis option.discI)
  thus ?thesis
    by (simp add: *(1-3) wellformed_bins_def)
qed

lemma wellformed_bins_Predict_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = Some a" "\<not> is_terminal cfg a"
  shows "(k, cfg, inp, bins_upd bs k (Predict_it k cfg a)) \<in> wellformed_bins"
proof -
  have *: "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using wellformed_bins_elim assms(1) by metis+
  have x: "x \<in> set (items (bs ! k))"
    using assms(2,3) by simp
  hence "wf_bins cfg inp (bins_upd bs k (Predict_it k cfg a))"
    using * x assms(1,4) distinct_Predict_it wf_bins_Predict_it wf_bins_bins_upd wellformed_bins_elim by metis
  thus ?thesis
    by (simp add: *(1-3) wellformed_bins_def)
qed

fun earley_measure :: "nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins \<Rightarrow> nat \<Rightarrow> nat" where
  "earley_measure (k, cfg, inp, bs) i = card { x | x. wf_item cfg inp x \<and> item_end x = k } - i"

lemma \<pi>_it'_simps[simp]:
  "i \<ge> length (items (bs ! k)) \<Longrightarrow> \<pi>_it' k cfg inp bs i = bs"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = None \<Longrightarrow>
    \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (bins_upd bs k (Complete_it k x bs i)) (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    is_terminal cfg a \<Longrightarrow> k < length inp \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (bins_upd bs (k+1) (Scan_it k inp a x i)) (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    is_terminal cfg a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp bs (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    \<not> is_terminal cfg a \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (bins_upd bs k (Predict_it k cfg a)) (i+1)"
  by (subst \<pi>_it'.simps, simp)+

lemma \<pi>_it'_induct[case_names Base Complete Scan Pass Predict]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes base: "\<And>k cfg inp bs i. i \<ge> length (items (bs ! k)) \<Longrightarrow> P k cfg inp bs i"
  assumes complete: "\<And>k cfg inp bs i x. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = None \<Longrightarrow> P k cfg inp (bins_upd bs k (Complete_it k x bs i)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes scan: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal cfg a \<Longrightarrow> k < length inp \<Longrightarrow> 
            P k cfg inp (bins_upd bs (k+1) (Scan_it k inp a x i)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes pass: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal cfg a \<Longrightarrow> \<not> k < length inp \<Longrightarrow>
            P k cfg inp bs (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes predict: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> \<not> is_terminal cfg a \<Longrightarrow> 
            P k cfg inp (bins_upd bs k (Predict_it k cfg a)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  shows "P k cfg inp bs i"
  using assms(1)
proof (induction n\<equiv>"earley_measure (k, cfg, inp, bs) i" arbitrary: bs i rule: nat_less_induct)
  case 1
  have wf: "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using "1.prems" wellformed_bins_elim by metis+
  hence k: "k < length bs"
    by simp
  have fin: "finite { x | x. wf_item cfg inp x \<and> item_end x = k }"
    using finiteness_UNIV_wf_item by fastforce
  show ?case
  proof cases
    assume "i \<ge> length (items (bs ! k))"
    then show ?thesis
      by (simp add: base)
  next
    assume a1: "\<not> i \<ge> length (items (bs ! k))"
    let ?x = "items (bs ! k) ! i"
    have x: "?x \<in> set (items (bs ! k))"
      using a1 by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "bins_upd bs k (Complete_it k ?x bs i)"
      have "item_origin ?x < length bs"
        using wf(4) k wf_bins_kth_bin wf_item_def x by (metis order_le_less_trans)
      hence wf_bins': "wf_bins cfg inp ?bs'"
        using wf_bins_Complete_it distinct_Complete_it wf(4) wf_bins_bins_upd k x by metis
      hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
        using wf(1,2,3) wellformed_bins_intro by fastforce
      have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
        using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
      have "i < length (items (?bs' ! k))"
        using a1 by (metis dual_order.strict_trans1 items_def leI length_map length_nth_bin_bins_upd)
      also have "... = card (set (items (?bs' ! k)))"
        using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def by (metis k length_bins_upd)
      also have "... \<le> card {x |x. wf_item cfg inp x \<and> item_end x = k}"
        using card_mono fin sub by blast
      finally have "card {x |x. wf_item cfg inp x \<and> item_end x = k} > i"
        by blast
      hence "earley_measure (k, cfg, inp, ?bs') (Suc i) < earley_measure (k, cfg, inp, bs) i"
        by simp
      thus ?thesis
        using 1 a1 a2 complete wf' by simp
    next
      assume a2: "\<not> next_symbol ?x = None"
      then obtain a where a_def: "next_symbol ?x = Some a"
        by blast
      show ?thesis
      proof cases
        assume a3: "is_terminal cfg a"
        show ?thesis
        proof cases
          assume a4: "k < length inp"
          let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a ?x i)"
          have wf_bins': "wf_bins cfg inp ?bs'"
            using wf_bins_Scan_it distinct_Scan_it wf(1,4) wf_bins_bins_upd a2 a4 k x by metis
          hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
            using wf(1,2,3) wellformed_bins_intro by fastforce
          have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
            using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
          have "i < length (items (?bs' ! k))"
            using a1 by (metis dual_order.strict_trans1 items_def leI length_map length_nth_bin_bins_upd)
          also have "... = card (set (items (?bs' ! k)))"
            using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
            by (metis Suc_eq_plus1 le_imp_less_Suc length_bins_upd)
          also have "... \<le> card {x |x. wf_item cfg inp x \<and> item_end x = k}"
            using card_mono fin sub by blast
          finally have "card {x |x. wf_item cfg inp x \<and> item_end x = k} > i"
            by blast
          hence "earley_measure (k, cfg, inp, ?bs') (Suc i) < earley_measure (k, cfg, inp, bs) i"
            by simp
          thus ?thesis
            using 1 a1 a_def a3 a4 scan wf' by simp
        next
          assume a4: "\<not> k < length inp"
          have sub: "set (items (bs ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
            using wf(1,2,4) unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
          have "i < length (items (bs ! k))"
            using a1 by simp
          also have "... = card (set (items (bs ! k)))"
            using wf(1,2,4) distinct_card wf_bins_def wf_bin_def by (metis Suc_eq_plus1 le_imp_less_Suc)
          also have "... \<le> card {x |x. wf_item cfg inp x \<and> item_end x = k}"
            using card_mono fin sub by blast
          finally have "card {x |x. wf_item cfg inp x \<and> item_end x = k} > i"
            by blast
          hence "earley_measure (k, cfg, inp, bs) (Suc i) < earley_measure (k, cfg, inp, bs) i"
            by simp
          thus ?thesis
            using 1 a1 a3 a4 a_def pass by simp
        qed
      next
        assume a3: "\<not> is_terminal cfg a"
        let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
        have wf_bins': "wf_bins cfg inp ?bs'"
          using wf_bins_Predict_it distinct_Predict_it wf(1,3,4) wf_bins_bins_upd k x by metis
        hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
          using wf(1,2,3) wellformed_bins_intro by fastforce
        have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
          using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
        have "i < length (items (?bs' ! k))"
          using a1 by (metis dual_order.strict_trans1 items_def leI length_map length_nth_bin_bins_upd)
        also have "... = card (set (items (?bs' ! k)))"
          using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
          by (metis Suc_eq_plus1 le_imp_less_Suc length_bins_upd)
        also have "... \<le> card {x |x. wf_item cfg inp x \<and> item_end x = k}"
          using card_mono fin sub by blast
        finally have "card {x |x. wf_item cfg inp x \<and> item_end x = k} > i"
          by blast
        hence "earley_measure (k, cfg, inp, ?bs') (Suc i) < earley_measure (k, cfg, inp, bs) i"
          by simp
        thus ?thesis
          using 1 a1 a_def a3 a_def predict wf' by simp
      qed
    qed
  qed
qed

lemma wellformed_bins_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "(k, cfg, inp, \<pi>_it' k cfg inp bs i) \<in> wellformed_bins"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems wellformed_bins_Complete_it by blast
  thus ?case
    using Complete.IH Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems wellformed_bins_Scan_it by metis
  thus ?case
    using Scan.IH Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems wellformed_bins_Predict_it by metis
  thus ?case
    using Predict.IH Predict.hyps by simp
qed simp_all

lemma wellformed_bins_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "(k, cfg, inp, \<pi>_it k cfg inp bs) \<in> wellformed_bins"
  using assms by (simp add: \<pi>_it_def wellformed_bins_\<pi>_it')

lemma length_bins_\<pi>_it'[simp]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (\<pi>_it' k cfg inp bs i) = length bs"
  by (metis assms wellformed_bins_\<pi>_it' wellformed_bins_elim)

lemma length_bins_\<pi>_it[simp]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (\<pi>_it k cfg inp bs) = length bs"
  using assms unfolding \<pi>_it_def by simp

lemma length_nth_bin_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (items (\<pi>_it' k cfg inp bs i ! l)) \<ge> length (items (bs ! l))"
  using length_nth_bin_bins_upd order_trans
  by (induction i rule: \<pi>_it'_induct[OF assms]) (auto simp: items_def, blast+)

lemma wf_bins_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "wf_bins cfg inp (\<pi>_it' k cfg inp bs i)"
  using assms wellformed_bins_\<pi>_it' wellformed_bins_elim by blast

lemma wf_bins_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "wf_bins cfg inp (\<pi>_it k cfg inp bs)"
  using assms \<pi>_it_def wf_bins_\<pi>_it' by metis

lemma kth_\<pi>_it'_bins:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  assumes "j < length (items (bs ! l))"
  shows "items (\<pi>_it' k cfg inp bs i ! l) ! j = items (bs ! l) ! j"
  using assms(2)
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "items (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Complete.IH Complete.prems length_nth_bin_bins_upd items_def order.strict_trans2 by (metis length_map)
  also have "... = items (bs ! l) ! j"
    using Complete.prems items_nth_idem_bins_upd nth_idem_bins_upd length_map items_def by metis
  finally show ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "items (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Scan.IH Scan.prems length_nth_bin_bins_upd order.strict_trans2 items_def by (metis length_map)
  also have "... = items (bs ! l) ! j"
    using Scan.prems items_nth_idem_bins_upd nth_idem_bins_upd length_map items_def by metis
  finally show ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "items (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Predict.IH Predict.prems length_nth_bin_bins_upd order.strict_trans2 items_def by (metis length_map)
  also have "... = items (bs ! l) ! j"
    using Predict.prems items_nth_idem_bins_upd nth_idem_bins_upd length_map items_def by metis
  finally show ?case
    using Predict.hyps by simp
qed simp_all

lemma nth_bin_sub_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "set (items (bs ! l)) \<subseteq> set (items (\<pi>_it' k cfg inp bs i ! l))"
proof standard
  fix x
  assume "x \<in> set (items (bs ! l))"
  then obtain j where *: "j < length (items (bs ! l))" "items (bs ! l) ! j = x"
    using in_set_conv_nth by metis
  have "x = items (\<pi>_it' k cfg inp bs i ! l) ! j"
    using kth_\<pi>_it'_bins assms * by metis
  moreover have "j < length (items (\<pi>_it' k cfg inp bs i ! l))"
    using assms *(1) length_nth_bin_\<pi>_it' less_le_trans by blast
  ultimately show "x \<in> set (items (\<pi>_it' k cfg inp bs i ! l))"
    by simp
qed

lemma nth_\<pi>_it'_eq:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "l < k \<Longrightarrow> \<pi>_it' k cfg inp bs i ! l = bs ! l"
  by (induction i rule: \<pi>_it'_induct[OF assms]) (auto simp: bins_upd_def)

lemma set_items_\<pi>_it'_eq:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "l < k \<Longrightarrow> set (items (\<pi>_it' k cfg inp bs i ! l)) = set (items (bs ! l))"
  by (simp add: assms nth_\<pi>_it'_eq)

lemma bins_upto_k0_\<pi>_it'_eq:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "bins_items_upto (\<pi>_it k cfg inp bs) k 0 = bins_items_upto bs k 0"
  unfolding bins_items_upto_def bin_items_upto_def \<pi>_it_def using set_items_\<pi>_it'_eq assms nth_\<pi>_it'_eq by fastforce

lemma wellformed_bins_Init_it:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, Init_it cfg inp) \<in> wellformed_bins"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg)"
  let ?b0 = "map (\<lambda>r. (Entry (init_item r 0) Null)) ?rs"
  let ?bs = "replicate (length inp + 1) ([])"
  have "distinct (items ?b0)"
    using assms unfolding wf_bin_def wf_item_def wf_cfg_def distinct_rules_def items_def
    by (auto simp: init_item_def distinct_map inj_on_def)
  moreover have "\<forall>x \<in> set (items ?b0). wf_item cfg inp x \<and> item_end x = 0"
    using assms unfolding wf_bin_def wf_item_def by (auto simp: init_item_def items_def)
  moreover have "wf_bins cfg inp ?bs"
    unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def using less_Suc_eq_0_disj by force
  ultimately show ?thesis
    using assms length_replicate wellformed_bins_intro
    unfolding wf_bin_def Init_it_def wf_bin_def wf_bin_items_def wf_bins_def
    by (metis (no_types, lifting) length_list_update nth_list_update_eq nth_list_update_neq)
qed

lemma length_bins_Init_it[simp]:
  "length (Init_it cfg inp) = length inp + 1"
  by (simp add: Init_it_def)

lemma wf_bins_Init_it:
  assumes "wf_cfg cfg"
  shows "wf_bins cfg inp (Init_it cfg inp)"
  using assms wellformed_bins_Init_it wellformed_bins_elim by blast

lemma wellformed_bins_\<I>_it[simp]:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
  using assms
proof (induction k)
  case 0
  have "(k, cfg, inp, Init_it cfg inp) \<in> wellformed_bins"
    using assms wellformed_bins_Init_it by blast
  thus ?case
    by (simp add: assms(2) wellformed_bins_Init_it wellformed_bins_\<pi>_it)
next
  case (Suc k)
  have "(Suc k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
    using Suc.IH Suc.prems(1) Suc_leD assms(2) wellformed_bins_elim wellformed_bins_intro by metis
  thus ?case
    by (simp add: wellformed_bins_\<pi>_it)
qed

lemma length_\<I>_it[simp]:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "length (\<I>_it k cfg inp) = length (Init_it cfg inp)"
  using assms wellformed_bins_\<I>_it wellformed_bins_elim by fastforce

lemma wf_bins_\<I>_it[simp]:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "wf_bins cfg inp (\<I>_it k cfg inp)"
  using assms wellformed_bins_\<I>_it wellformed_bins_elim by fastforce

lemma wellformed_bins_\<II>_it:
  "k \<le> length inp \<Longrightarrow> wf_cfg cfg \<Longrightarrow> (k, cfg, inp, \<II>_it cfg inp) \<in> wellformed_bins"
  by (simp add: \<II>_it_def wellformed_bins_intro)

lemma wf_bins_\<II>_it:
  "wf_cfg cfg \<Longrightarrow> wf_bins cfg inp (\<II>_it cfg inp)"
  by (simp add: \<II>_it_def)


subsection \<open>List to set\<close>

lemma Init_it_eq_Init:
  "bins_items (Init_it cfg inp) = Init cfg"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg)"
  let ?b0 = "map (\<lambda>r. (Entry (init_item r 0) Null)) ?rs"
  let ?bs = "replicate (length inp + 1) ([])"
  have "bins_items (?bs[0 := ?b0]) = set (items ?b0)"
  proof -
    have "bins_items (?bs[0 := ?b0]) = \<Union> {set (items ((?bs[0 := ?b0]) ! k)) |k. k < length (?bs[0 := ?b0])}"
      unfolding bins_items_def by blast
    also have "... = set (items ((?bs[0 := ?b0]) ! 0)) \<union> \<Union> {set (items ((?bs[0 := ?b0]) ! k)) |k. k < length (?bs[0 := ?b0]) \<and> k \<noteq> 0}"
      by fastforce
    also have "... = set (items (?b0))"
      by (auto simp: items_def)
    finally show ?thesis .
  qed
  also have "... = Init cfg"
    by (auto simp: Init_def items_def rule_head_def)
  finally show ?thesis
    by (auto simp: Init_it_def)
qed

lemma Scan_it_sub_Scan:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs" "k < length inp"
  assumes "next_symbol x = Some a"
  shows "set (items (Scan_it k inp a x pre)) \<subseteq> Scan k inp I"
proof standard
  fix y
  assume *: "y \<in> set (items (Scan_it k inp a x pre))"
  have "x \<in> bin I k"
    using kth_bin_sub_bins assms(1-4) items_def wf_bin_def wf_bins_def wf_bin_items_def bin_def by fastforce
  {
    assume #: "k < length inp" "inp!k = a"
    hence "y = inc_item x (k+1)"
      using * unfolding Scan_it_def by (simp add: items_def)
    hence "y \<in> Scan k inp I"
      using \<open>x \<in> bin I k\<close> # assms(6) unfolding Scan_def by blast
  }
  thus "y \<in> Scan k inp I"
    using * assms(5) unfolding Scan_it_def by (auto simp: items_def)
qed

lemma Predict_it_sub_Predict:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol x = Some X"
  shows "set (items (Predict_it k cfg X)) \<subseteq> Predict k cfg I"
proof standard
  fix y
  assume *: "y \<in> set (items (Predict_it k cfg X))"
  have "x \<in> bin I k"
    using kth_bin_sub_bins assms(1-4) items_def wf_bin_def wf_bins_def bin_def wf_bin_items_def by fast
  let ?rs = "filter (\<lambda>r. rule_head r = X) (\<RR> cfg)"
  let ?xs = "map (\<lambda>r. init_item r k) ?rs"
  have "y \<in> set ?xs"
    using * unfolding Predict_it_def items_def by simp
  then obtain r where "y = init_item r k" "rule_head r = X" "r \<in> set (\<RR> cfg)" "next_symbol x = Some (rule_head r)"
    using assms(5) by auto
  thus "y \<in> Predict k cfg I"
    unfolding Predict_def using \<open>x \<in> bin I k\<close> by blast
qed

lemma Complete_it_sub_Complete:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "y \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol y = None"
  shows "set (items (Complete_it k y bs red)) \<subseteq> Complete k I"
  thm Complete_it_def
proof standard
  fix x
  assume *: "x \<in> set (items (Complete_it k y bs red))"
  have "y \<in> bin I k"
    using kth_bin_sub_bins assms items_def wf_bin_def wf_bins_def bin_def wf_bin_items_def by fast
  let ?orig = "bs ! item_origin y"
  let ?xs = "filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"
  let ?xs' = "map (\<lambda>(x, pre). (Entry (inc_item x k) (PreRed (item_origin y, pre, red) []))) ?xs"
  have 0: "item_origin y < length bs"
    using wf_bins_def wf_bin_def wf_item_def wf_bin_items_def assms(1,3,4)
    by (metis Orderings.preorder_class.dual_order.strict_trans1 leD not_le_imp_less)
  {
    fix z
    assume *: "z \<in> set (map fst ?xs)"
    have "next_symbol z = Some (item_rule_head y)"
      using * by (simp add: filter_with_index_cong_filter)
    moreover have "z \<in> bin I (item_origin y)"
      using 0 * assms(1,2) bin_def kth_bin_sub_bins wf_bins_kth_bin filter_with_index_cong_filter
      by (metis (mono_tags, lifting) filter_is_subset in_mono mem_Collect_eq)
    ultimately have "next_symbol z = Some (item_rule_head y)" "z \<in> bin I (item_origin y)"
      by simp_all
  }
  hence 1: "\<forall>z \<in> set (map fst ?xs). next_symbol z = Some (item_rule_head y) \<and> z \<in> bin I (item_origin y)"
    by blast
  obtain z where z: "x = inc_item z k" "z \<in> set (map fst ?xs)"
    using * unfolding Complete_it_def by (auto simp: rev_image_eqI items_def)
  moreover have "next_symbol z = Some (item_rule_head y)" "z \<in> bin I (item_origin y)"
    using 1 z by blast+
  ultimately show "x \<in> Complete k I"
    using \<open>y \<in> bin I k\<close> assms(5) unfolding Complete_def next_symbol_def by (auto split: if_splits)
qed

lemma \<pi>_it'_sub_\<pi>:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "bins_items bs \<subseteq> I"
  shows "bins_items (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp I"
  using assms
proof (induction i arbitrary: I rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Base k cfg inp bs i)
  thus ?case
    using \<pi>_mono by fastforce
next
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by force
  hence "bins_items ?bs' \<subseteq> I \<union> Complete k I"
    using Complete_it_sub_Complete Complete.hyps(3) Complete.prems(1,2) bins_bins_upd wellformed_bins_elim by blast
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  ultimately have "bins_items (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp (I \<union> Complete k I)"
    using Complete.IH Complete.hyps by simp
  thus ?case
    using Complete_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by force
  hence "bins_items ?bs' \<subseteq> I \<union> Scan k inp I"
    using Scan_it_sub_Scan Scan.hyps(3,5) Scan.prems bins_bins_upd wellformed_bins_elim
    by (metis add_mono1 sup_mono)
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  ultimately have "bins_items (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp (I \<union> Scan k inp I)"
    using Scan.IH Scan.hyps by simp
  thus ?case
    using Scan_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
next
  case (Pass k cfg inp bs i x a)
  thus ?case
    by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by force
  hence "bins_items ?bs' \<subseteq> I \<union> Predict k cfg I"
    using Predict_it_sub_Predict Predict.hyps(3) Predict.prems bins_bins_upd wellformed_bins_elim
    by (metis sup_mono)
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  ultimately have "bins_items (\<pi>_it' k cfg inp bs i)  \<subseteq> \<pi> k cfg inp (I \<union> Predict k cfg I)"
    using Predict.IH Predict.hyps by simp
  thus ?case
    using Predict_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
qed

lemma \<pi>_it_sub_\<pi>:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "bins_items bs \<subseteq> I"
  shows "bins_items (\<pi>_it k cfg inp bs) \<subseteq> \<pi> k cfg inp I"
  using assms \<pi>_it'_sub_\<pi> \<pi>_it_def by metis

lemma \<I>_it_sub_\<I>:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "bins_items (\<I>_it k cfg inp) \<subseteq> \<I> k cfg inp"
  using assms
proof (induction k)
  case 0
  have "(k, cfg, inp, Init_it cfg inp) \<in> wellformed_bins"
    using assms(1) assms(2) wellformed_bins_Init_it by blast
  thus ?case
    by (simp add: Init_it_eq_Init \<pi>_it_sub_\<pi> assms(2) wellformed_bins_Init_it)
next
  case (Suc k)
  have "(Suc k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
    by (simp add: Suc.prems(1) Suc_leD assms(2) wellformed_bins_intro)
  thus ?case
    by (simp add: Suc.IH Suc.prems(1) Suc_leD \<pi>_it_sub_\<pi> assms(2))
qed

lemma \<II>_it_sub_\<II>:
  "wf_cfg cfg \<Longrightarrow> bins_items (\<II>_it cfg inp) \<subseteq> \<II> cfg inp"
  using \<I>_it_sub_\<I> \<II>_def \<II>_it_def by (metis dual_order.refl)


subsection \<open>Soundness\<close>

lemma sound_Scan_it:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs" "k < length inp"
  assumes "next_symbol x = Some a" "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (items (Scan_it k inp a x i)))"
  using sound_Scan Scan_it_sub_Scan assms by (smt (verit, best) sound_items_def subsetD)

lemma sound_Predict_it:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol x = Some X" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (items (Predict_it k cfg X)))"
  using sound_Predict Predict_it_sub_Predict sound_items_def assms by (smt (verit, ccfv_SIG) in_mono)

lemma sound_Complete_it:
  assumes "wf_bins cfg inp bs" "bins_items bs \<subseteq> I" "y \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol y = None" "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (items (Complete_it k y bs i)))"
  using sound_Complete Complete_it_sub_Complete sound_items_def assms by (metis (no_types, lifting) subsetD)

lemma sound_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins_items bs)"
  shows "sound_items cfg inp (bins_items (\<pi>_it' k cfg inp bs i))"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by force
  hence "sound_items cfg inp (set (items (Complete_it k x bs i)))"
    using sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  ultimately have "sound_items cfg inp (bins_items (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Complete.IH Complete.prems(2) length_bins_upd bins_bins_upd sound_items_def wellformed_bins_elim
    Suc_eq_plus1 Un_iff le_imp_less_Suc by metis
  thus ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by force
  hence "sound_items cfg inp (set (items (Scan_it k inp a x i)))"
    using sound_Scan_it \<pi>_mono Scan.hyps(3,5) Scan.prems(1,2) bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  ultimately have "sound_items cfg inp (bins_items (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Scan.IH sound_items_def Scan.hyps(5) Scan.prems(2) length_bins_upd bins_bins_upd wellformed_bins_elim
    by (metis UnE add_less_cancel_right )
  thus ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by force
  hence "sound_items cfg inp (set (items(Predict_it k cfg a)))"
    using sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems bins_bin_exists wellformed_bins_elim
          sound_\<pi> wf_bins_kth_bin wf_items_def by metis
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  ultimately have "sound_items cfg inp (bins_items (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Predict.IH sound_items_def Predict.prems(2) length_bins_upd bins_bins_upd wellformed_bins_elim
    by (metis Suc_eq_plus1 UnE le_imp_less_Suc)
  thus ?case
    using Predict.hyps by simp
qed simp_all

lemma sound_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins_items bs)"
  shows "sound_items cfg inp (bins_items (\<pi>_it k cfg inp bs))"
  using sound_\<pi>_it' assms \<pi>_it_def by metis


subsection \<open>Set to list\<close>

lemma bin_bins_upto_bins_eq:
  assumes "wf_bins cfg inp bs" "k < length bs" "i \<ge> length (items (bs ! k))" "l \<le> k"
  shows "bin (bins_items_upto bs k i) l = bin (bins_items bs) l"
  unfolding bins_items_upto_def bins_items_def bin_def using assms nat_less_le
  apply (auto simp: nth_list_update bin_items_upto_eq_set_items wf_bins_kth_bin items_def)
  apply (metis imageI nle_le order_trans, fast)
  done

lemma impossible_complete_item:
  assumes "wf_cfg cfg" "wf_item cfg inp x" "sound_item cfg inp x"
  assumes "is_complete x"  "item_origin x = k" "item_end x = k" "nonempty_derives cfg"
  shows False
proof -
  have "derives cfg [item_rule_head x] []"
    using assms(3-6) by (simp add: slice_empty is_complete_def sound_item_def item_\<beta>_def )
  moreover have "is_nonterminal cfg (item_rule_head x)"
    using assms(1,2) unfolding wf_item_def item_rule_head_def rule_head_def 
    by (metis prod.collapse rule_nonterminal_type)
  ultimately show ?thesis
    using assms(7) nonempty_derives_def is_nonterminal_def by metis
qed

lemma Complete_Un_eq_terminal:
  assumes "next_symbol z = Some a" "is_terminal cfg a" "wf_items cfg inp I" "wf_item cfg inp z" "wf_cfg cfg"
  shows "Complete k (I \<union> {z}) = Complete k I"
proof (rule ccontr)
  assume "Complete k (I \<union> {z}) \<noteq> Complete k I"
  hence "Complete k I \<subset> Complete k (I \<union> {z})"
    using Complete_sub_mono by blast
  then obtain w x y  where *:
    "w \<in> Complete k (I \<union> {z})" "w \<notin> Complete k I" "w = inc_item x k"
    "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by fast
  show False
  proof (cases "x = z")
    case True
    have "is_nonterminal cfg (item_rule_head y)"
      using *(5,6) assms(1,3-5)
      apply (auto simp: wf_defs bin_def item_rule_head_def rule_head_def next_symbol_def)
      by (metis prod.exhaust_sel rule_nonterminal_type)
    thus ?thesis
      using True *(7) assms(1,2,5) is_terminal_nonterminal by fastforce
  next
    case False
    thus ?thesis
      using * assms(1) by (auto simp: next_symbol_def Complete_def bin_def)
  qed
qed

lemma Complete_Un_eq_nonterminal:
  assumes "next_symbol z = Some a" "is_nonterminal cfg a" "sound_items cfg inp I" "item_end z = k"
  assumes "wf_items cfg inp I" "wf_item cfg inp z" "wf_cfg cfg" "nonempty_derives cfg"
  shows "Complete k (I \<union> {z}) = Complete k I"
proof (rule ccontr)
  assume "Complete k (I \<union> {z}) \<noteq> Complete k I"
  hence "Complete k I \<subset> Complete k (I \<union> {z})"
    using Complete_sub_mono by blast
  then obtain w x y where *:
    "w \<in> Complete k (I \<union> {z})" "w \<notin> Complete k I" "w = inc_item x k"
    "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by fast
  consider (A) "x = z" | (B) "y = z" | "\<not> (x = z \<or> y = z)"
    by blast
  thus False
  proof cases
    case A
    have "item_origin y = k"
      using *(4) A assms(4) by (auto simp: bin_def)
    moreover have "item_end y = k"
      using *(5) bin_def by blast
    moreover have "sound_item cfg inp y"
      using *(5,6) assms(1,3) by (auto simp: bin_def next_symbol_def sound_items_def)
    moreover have "wf_item cfg inp y"
      using *(5) assms(5,6) wf_items_def by (auto simp: bin_def)
    ultimately show ?thesis
      using impossible_complete_item *(6) assms(7,8) by blast
  next
    case B
    thus ?thesis
      using *(6) assms(1) by (auto simp: next_symbol_def)
  next
    case 3
    thus ?thesis
      using *(2-7) Complete_def by (auto simp: bin_def; blast)
  qed
qed

lemma wf_item_in_kth_bin:
  "wf_bins cfg inp bs \<Longrightarrow> x \<in> bins_items bs \<Longrightarrow> item_end x = k \<Longrightarrow> x \<in> set (items (bs ! k))"
  using bins_bin_exists wf_bins_kth_bin wf_bins_def by blast

lemma Complete_bins_upto_eq_bins:
  assumes "wf_bins cfg inp bs" "k < length bs" "i \<ge> length (items (bs ! k))"
  shows "Complete k (bins_items_upto bs k i) = Complete k (bins_items bs)"
proof -
  have "\<And>l. l \<le> k \<Longrightarrow> bin (bins_items_upto bs k i) l = bin (bins_items bs) l"
    using bin_bins_upto_bins_eq[OF assms] by blast
  moreover have "wf_items cfg inp (bins_items bs)"
    using assms(1) wf_bins_impl_wf_items by metis
  ultimately show ?thesis
    unfolding Complete_def bin_def wf_items_def wf_item_def by auto
qed

lemma Complete_sub_bins_Un_Complete_it:
  assumes "Complete k I \<subseteq> bins_items bs" "I \<subseteq> bins_items bs" "is_complete z" "wf_bins cfg inp bs" "wf_item cfg inp z"
  shows "Complete k (I \<union> {z}) \<subseteq> bins_items bs \<union> set (items (Complete_it k z bs red))"
proof standard
  fix w
  assume "w \<in> Complete k (I \<union> {z})"
  then obtain x y where *:
    "w = inc_item x k" "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by blast
  consider (A) "x = z" | (B) "y = z" | "\<not> (x = z \<or> y = z)"
    by blast
  thus "w \<in> bins_items bs \<union> set (items (Complete_it k z bs red))"
  proof cases
    case A
    thus ?thesis
      using *(5) assms(3) by (auto simp: next_symbol_def)
  next
    case B
    let ?orig = "bs ! item_origin z"
    let ?is = "filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head z)) (items ?orig)"
    have "x \<in> bin I (item_origin y)"
      using B *(2) *(5) assms(3) by (auto simp: next_symbol_def bin_def)
    moreover have "bin I (item_origin z) \<subseteq> set (items (bs ! item_origin z))"
      using wf_item_in_kth_bin assms(2,4) bin_def by blast
    ultimately have "x \<in> set (map fst ?is)"
      using *(5) B by (simp add: filter_with_index_cong_filter in_mono)
    thus ?thesis
      unfolding Complete_it_def *(1) by (auto simp: rev_image_eqI items_def)
  next
    case 3
    thus ?thesis
      using * assms(1) Complete_def by (auto simp: bin_def; blast)
  qed
qed

lemma Complete_it_eq_item_origin:
  "bs ! item_origin y = bs' ! item_origin y \<Longrightarrow> Complete_it k y bs red = Complete_it k y bs' red"
  by (auto simp: Complete_it_def)

lemma kth_bin_bins_upto_empty:
  assumes "wf_bins cfg inp bs" "k < length bs"
  shows "bin (bins_items_upto bs k 0) k = {}"
proof -
  {
    fix x
    assume "x \<in> bins_items_upto bs k 0"
    then obtain l where "x \<in> set (items (bs ! l))" "l < k"
      unfolding bins_items_upto_def bin_items_upto_def by blast
    hence "item_end x = l"
      using wf_bins_kth_bin assms by fastforce
    hence "item_end x < k"
      using \<open>l < k\<close> by blast
  }
  thus ?thesis
    by (auto simp: bin_def)
qed

lemma \<pi>_it'_mono:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "bins_items bs \<subseteq> bins_items (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  hence "bins_items bs \<subseteq> bins_items ?bs'"
    using length_bins_upd bins_bins_upd wellformed_bins_elim by (metis Un_upper1)
  also have "... \<subseteq> bins_items (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using wf Complete.IH by blast
  finally show ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  hence "bins_items bs \<subseteq> bins_items ?bs'"
    using Scan.hyps(5) length_bins_upd bins_bins_upd wellformed_bins_elim
    by (metis add_mono1 sup_ge1)
  also have "... \<subseteq> bins_items (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using wf Scan.IH by blast
  finally show ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  hence "bins_items bs \<subseteq> bins_items ?bs'"
    using length_bins_upd bins_bins_upd wellformed_bins_elim by (metis sup_ge1)
  also have "... \<subseteq> bins_items (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using wf Predict.IH by blast
  finally show ?case
    using Predict.hyps by simp
qed simp_all

lemma \<pi>_step_sub_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_items_upto bs k i) \<subseteq> bins_items bs"
  assumes "sound_items cfg inp (bins_items bs)" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi>_step k cfg inp (bins_items bs) \<subseteq> bins_items (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Base k cfg inp bs i)
  have "bin (bins_items bs) k = bin (bins_items_upto bs k i) k"
    using Base.hyps Base.prems(1) bin_bins_upto_bins_eq wellformed_bins_elim by blast
  thus ?case
    using Scan_bin_absorb Predict_bin_absorb Complete_bins_upto_eq_bins wellformed_bins_elim
      Base.hyps Base.prems(1,2,3,5) \<pi>_step_def Complete_\<pi>_step_mono Predict_\<pi>_step_mono Scan_\<pi>_step_mono \<pi>_it'_mono
    by (metis (no_types, lifting) Un_assoc sup.orderE)
next
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by auto
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  have sound: "sound_items cfg inp (set (items (Complete_it k x bs i)))"
    using x sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  have "Scan k inp (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Scan k inp (bins_items_upto ?bs' k (i + 1)) = Scan k inp (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Complete.hyps(1) bins_items_upto_Suc_Un length_nth_bin_bins_upd items_def
      by (metis length_map linorder_not_less sup.boundedE sup.order_iff)
    also have "... = Scan k inp (bins_items_upto bs k i \<union> {x})"
      using Complete.hyps(1,2) Complete.prems(1) items_nth_idem_bins_upd bins_items_upto_kth_nth_idem wellformed_bins_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins_items bs \<union> Scan k inp {x}"
      using Complete.prems(2,3) Scan_Un Scan_\<pi>_step_mono by fastforce
    also have "... = bins_items bs"
      using Complete.hyps(3) by (auto simp: Scan_def bin_def)
    finally show ?thesis
      using Complete.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  moreover have "Predict k cfg (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Predict k cfg (bins_items_upto ?bs' k (i + 1)) = Predict k cfg (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Complete.hyps(1) bins_items_upto_Suc_Un length_nth_bin_bins_upd
      by (metis dual_order.strict_trans1 items_def length_map not_le_imp_less)
    also have "... = Predict k cfg (bins_items_upto bs k i \<union> {x})"
      using Complete.hyps(1,2) Complete.prems(1) items_nth_idem_bins_upd bins_items_upto_kth_nth_idem wellformed_bins_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins_items bs \<union> Predict k cfg {x}"
      using Complete.prems(2,3) Predict_Un Predict_\<pi>_step_mono by blast
    also have "... = bins_items bs"
      using Complete.hyps(3) by (auto simp: Predict_def bin_def)
    finally show ?thesis
      using Complete.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  moreover have "Complete k (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Complete k (bins_items_upto ?bs' k (i + 1)) = Complete k (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_items_upto_Suc_Un length_nth_bin_bins_upd Complete.hyps(1)
      by (metis (no_types, opaque_lifting) dual_order.trans items_def length_map not_le_imp_less)
    also have "... = Complete k (bins_items_upto bs k i \<union> {x})"
      using items_nth_idem_bins_upd Complete.hyps(1,2) bins_items_upto_kth_nth_idem Complete.prems(1) wellformed_bins_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins_items bs \<union> set (items (Complete_it k x bs i))"
      using Complete_sub_bins_Un_Complete_it Complete.hyps(3) Complete.prems(1,2,3) next_symbol_def
        bins_items_upto_sub_bins_items wf_bins_kth_bin x Complete_\<pi>_step_mono wellformed_bins_elim
      by (smt (verit, best) option.distinct(1) subset_trans)
    finally show ?thesis
      using Complete.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  ultimately have "\<pi>_step k cfg inp (bins_items ?bs') \<subseteq> bins_items (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Complete.IH Complete.prems sound wf \<pi>_step_def bins_items_upto_sub_bins_items
          wellformed_bins_elim bins_bins_upd sound_items_def
    by (metis UnE sup.boundedI)
  thus ?case
    using Complete.hyps Complete.prems(1) \<pi>_it'_simps(2) \<pi>_step_sub_mono bins_bins_upd wellformed_bins_elim
    by (smt (verit, best) sup.coboundedI2 sup.orderE sup_ge1)
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have x: "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by auto
  hence sound: "sound_items cfg inp (set (items (Scan_it k inp a x i)))"
    using sound_Scan_it \<pi>_mono Scan.hyps(3,5) Scan.prems(1,2,3) bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  have "Scan k inp (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Scan k inp (bins_items_upto ?bs' k (i + 1)) = Scan k inp (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_items_upto_Suc_Un Scan.hyps(1) nth_idem_bins_upd
      by (metis Suc_eq_plus1 items_def length_map lessI less_not_refl not_le_imp_less)
    also have "... = Scan k inp (bins_items_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(1,2) nth_idem_bins_upd bins_items_upto_kth_nth_idem wellformed_bins_elim
      by (metis add_mono_thms_linordered_field(1) items_def length_map less_add_one linorder_le_less_linear not_add_less1)
    also have "... \<subseteq> bins_items bs \<union> Scan k inp {x}"
      using Scan.prems(2,3) Scan_Un Scan_\<pi>_step_mono by fastforce
    finally have *: "Scan k inp (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items bs \<union> Scan k inp {x}" .
    show ?thesis
    proof cases
      assume a1: "inp!k = a"
      hence "Scan k inp {x} = {inc_item x (k+1)}"
        using Scan.hyps(1-3,5) Scan.prems(1,2) wellformed_bins_elim apply (auto simp: Scan_def bin_def)
        using wf_bins_kth_bin x by blast
      hence "Scan k inp (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items bs \<union> {inc_item x (k+1)}"
        using * by blast
      also have "... = bins_items bs \<union> set (items (Scan_it k inp a x i))"
        using a1 Scan.hyps(5) by (auto simp: Scan_it_def items_def)
      also have "... = bins_items ?bs'"
        using Scan.hyps(5) Scan.prems(1) wellformed_bins_elim bins_bins_upd by (metis add_mono1)
      finally show ?thesis .
    next
      assume a1: "\<not> inp!k = a"
      hence "Scan k inp {x} = {}"
        using Scan.hyps(3) by (auto simp: Scan_def bin_def)
      hence "Scan k inp (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items bs"
        using * by blast
      also have "... \<subseteq> bins_items ?bs'"
        using Scan.hyps(5) Scan.prems(1) wellformed_bins_elim bins_bins_upd
        by (metis Un_left_absorb add_strict_right_mono subset_Un_eq)
      finally show ?thesis .
    qed
  qed
  moreover have "Predict k cfg (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Predict k cfg (bins_items_upto ?bs' k (i + 1)) = Predict k cfg (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_items_upto_Suc_Un Scan.hyps(1) nth_idem_bins_upd
      by (metis Suc_eq_plus1 dual_order.refl items_def length_map lessI linorder_not_less)
    also have "... = Predict k cfg (bins_items_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(1,2) nth_idem_bins_upd bins_items_upto_kth_nth_idem wellformed_bins_elim
      by (metis add_strict_right_mono items_def le_add1 length_map less_add_one linorder_not_le)
    also have "... \<subseteq> bins_items bs \<union> Predict k cfg {x}"
      using Scan.prems(2,3) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = bins_items bs"
      using Scan.hyps(3,4) Scan.prems(1) is_terminal_nonterminal wellformed_bins_elim
      by (auto simp: Predict_def bin_def rule_head_def, fastforce) 
    finally show ?thesis
      using Scan.hyps(5) Scan.prems(1) by (simp add: bins_bins_upd sup.coboundedI1 wellformed_bins_elim)
  qed
  moreover have "Complete k (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Complete k (bins_items_upto ?bs' k (i + 1)) = Complete k (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_items_upto_Suc_Un Scan.hyps(1) nth_idem_bins_upd
      by (metis Suc_eq_plus1 items_def length_map lessI less_not_refl not_le_imp_less)
    also have "... = Complete k (bins_items_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(1,2) nth_idem_bins_upd bins_items_upto_kth_nth_idem wellformed_bins_elim
      by (metis add_mono1 items_def length_map less_add_one linorder_not_le not_add_less1)
    also have "... = Complete k (bins_items_upto bs k i)"
      using Complete_Un_eq_terminal Scan.hyps(3,4) Scan.prems bins_items_upto_sub_bins_items subset_iff
            wf_bins_impl_wf_items wf_bins_kth_bin wf_items_def x wellformed_bins_elim
      by (smt (verit, ccfv_threshold))
    finally show ?thesis
      using Scan.hyps(5) Scan.prems(1,2,3) Complete_\<pi>_step_mono by (auto simp: bins_bins_upd wellformed_bins_elim, blast)
  qed
  ultimately have "\<pi>_step k cfg inp (bins_items ?bs') \<subseteq> bins_items (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Scan.IH Scan.prems Scan.hyps(5) sound wf \<pi>_step_def bins_items_upto_sub_bins_items wellformed_bins_elim
          bins_bins_upd sound_items_def by (metis UnE add_mono1 le_supI)
  thus ?case
    using \<pi>_step_sub_mono \<pi>_it'_simps(3) Scan.hyps Scan.prems(1) wellformed_bins_elim bins_bins_upd
    by (smt (verit, ccfv_SIG) add_mono1 sup.cobounded1 sup.coboundedI2 sup.orderE)
next
  case (Pass k cfg inp bs i x a)
  have x: "x \<in> set (items (bs ! k))"
    using Pass.hyps(1,2) by auto
  have "Scan k inp (bins_items_upto bs k (i + 1)) \<subseteq> bins_items bs"
    using Scan_def Pass.hyps(5) by auto
  moreover have "Predict k cfg (bins_items_upto bs k (i + 1)) \<subseteq> bins_items bs"
  proof -
    have "Predict k cfg (bins_items_upto bs k (i + 1)) = Predict k cfg (bins_items_upto bs k i \<union> {items (bs ! k) ! i})"
      using bins_items_upto_Suc_Un Pass.hyps(1) by (metis items_def length_map not_le_imp_less)
    also have "... = Predict k cfg (bins_items_upto bs k i \<union> {x})"
      using Pass.hyps(1,2,5) nth_idem_bins_upd bins_items_upto_kth_nth_idem by simp
    also have "... \<subseteq> bins_items bs \<union> Predict k cfg {x}"
      using Pass.prems(2) Predict_Un Predict_\<pi>_step_mono by blast
    also have "... = bins_items bs"
      using Pass.hyps(3,4) Pass.prems(1) is_terminal_nonterminal wellformed_bins_elim 
      by (auto simp: Predict_def bin_def rule_head_def, fastforce)
    finally show ?thesis
      using bins_bins_upd Pass.hyps(5) Pass.prems(3) by auto
  qed
  moreover have "Complete k (bins_items_upto bs k (i + 1)) \<subseteq> bins_items bs"
  proof -
    have "Complete k (bins_items_upto bs k (i + 1)) = Complete k (bins_items_upto bs k i \<union> {x})"
      using bins_items_upto_Suc_Un Pass.hyps(1,2)
      by (metis items_def length_map not_le_imp_less)
    also have "... = Complete k (bins_items_upto bs k i)"
      using Complete_Un_eq_terminal Pass.hyps Pass.prems bins_items_upto_sub_bins_items subset_iff 
            wf_bins_impl_wf_items wf_items_def wf_bins_kth_bin x wellformed_bins_elim by (smt (verit, best))
    finally show ?thesis
      using Pass.prems(1,2) Complete_\<pi>_step_mono wellformed_bins_elim by blast
  qed
  ultimately have "\<pi>_step k cfg inp (bins_items bs) \<subseteq> bins_items (\<pi>_it' k cfg inp bs (i+1))"
    using Pass.IH Pass.prems \<pi>_step_def bins_items_upto_sub_bins_items wellformed_bins_elim
    by (metis le_sup_iff)
  thus ?case
    using bins_bins_upd Pass.hyps Pass.prems by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "k \<ge> length inp \<or> \<not> inp!k = a"
    using Predict.hyps(4) Predict.prems(4) is_word_is_terminal leI by blast
  have x: "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by auto
  hence sound: "sound_items cfg inp (set (items (Predict_it k cfg a)))"
    using sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems bins_bin_exists wellformed_bins_elim
          sound_\<pi> wf_bins_kth_bin wf_items_def by metis
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  have len: "i < length (items (?bs' ! k))"
    using length_nth_bin_bins_upd Predict.hyps(1)
    by (metis dual_order.strict_trans1 items_def length_map linorder_not_less)
  have "item_rule x \<in> set (\<RR> cfg)"
    using Predict.prems(1) wf_bins_kth_bin x wf_item_def wellformed_bins_elim by blast
  hence "\<forall>s \<in> set (item_rule_body x). s \<in> set (\<NN> cfg) \<union> set (\<TT> cfg)"
    using Predict.prems(1) wellformed_bins_elim by (auto simp: wf_cfg_defs item_rule_body_def rule_body_def; fastforce)
  hence "is_terminal cfg a \<or> is_nonterminal cfg a"
    using Predict.hyps(3) by (auto simp: next_symbol_def is_complete_def is_nonterminal_def is_terminal_def split: if_splits)
  hence nonterm: "is_nonterminal cfg a"
    using Predict.hyps(4) by blast
  have "Scan k inp (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Scan k inp (bins_items_upto ?bs' k (i + 1)) = Scan k inp (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Predict.hyps(1) bins_items_upto_Suc_Un by (metis items_def len length_map)
    also have "... = Scan k inp (bins_items_upto bs k i \<union> {x})"
      using Predict.hyps(1,2) Predict.prems(1) items_nth_idem_bins_upd bins_items_upto_kth_nth_idem wellformed_bins_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins_items bs \<union> Scan k inp {x}"
      using Predict.prems(2,3) Scan_Un Scan_\<pi>_step_mono by fastforce
    also have "... = bins_items bs"
      using Predict.hyps(3) \<open>length inp \<le> k \<or> inp ! k \<noteq> a\<close> by (auto simp: Scan_def bin_def)
    finally show ?thesis
      using Predict.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  moreover have "Predict k cfg (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Predict k cfg (bins_items_upto ?bs' k (i + 1)) = Predict k cfg (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Predict.hyps(1) bins_items_upto_Suc_Un by (metis items_def len length_map)
    also have "... = Predict k cfg (bins_items_upto bs k i \<union> {x})"
      using Predict.hyps(1,2) Predict.prems(1) items_nth_idem_bins_upd bins_items_upto_kth_nth_idem wellformed_bins_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins_items bs \<union> Predict k cfg {x}"
      using Predict.prems(2,3) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = bins_items bs \<union> set (items (Predict_it k cfg a))"
      using Predict.hyps Predict.prems(1-3) wellformed_bins_elim 
      apply (auto simp: Predict_def Predict_it_def bin_def items_def)
      using wf_bins_kth_bin x by blast
    finally show ?thesis
      using Predict.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  moreover have "Complete k (bins_items_upto ?bs' k (i + 1)) \<subseteq> bins_items ?bs'"
  proof -
    have "Complete k (bins_items_upto ?bs' k (i + 1)) = Complete k (bins_items_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_items_upto_Suc_Un len by (metis items_def length_map)
    also have "... = Complete k (bins_items_upto bs k i \<union> {x})"
      using items_nth_idem_bins_upd Predict.hyps(1,2) Predict.prems(1) bins_items_upto_kth_nth_idem wellformed_bins_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... = Complete k (bins_items_upto bs k i)"
      using Complete_Un_eq_nonterminal[OF Predict.hyps(3) nonterm] Predict.prems bins_items_upto_sub_bins_items
            sound_items_def subset_eq wf_bins_kth_bin x wf_bins_impl_wf_items wf_items_def wellformed_bins_elim
      by metis
    finally show ?thesis
      using bins_bins_upd Predict.prems(1,2,3) Complete_\<pi>_step_mono wellformed_bins_elim
      by (metis Un_upper1 dual_order.trans)
  qed
  ultimately have "\<pi>_step k cfg inp (bins_items ?bs') \<subseteq> bins_items (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Predict.IH Predict.prems sound wf \<pi>_step_def bins_items_upto_sub_bins_items 
          bins_bins_upd sound_items_def wellformed_bins_elim by (metis UnE le_supI)
  thus ?case
    using \<pi>_step_sub_mono \<pi>_it'_simps(5) Predict.hyps Predict.prems(1) wellformed_bins_elim
    by (smt (verit, ccfv_SIG) bins_bins_upd sup.coboundedI2 sup.orderE sup_ge1)
qed

lemma \<pi>_step_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs"
  assumes "sound_items cfg inp (bins_items bs)" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi>_step k cfg inp (bins_items bs) \<subseteq> bins_items (\<pi>_it k cfg inp bs)"
  using assms \<pi>_step_sub_\<pi>_it' \<pi>_it_def by metis

lemma bins_eq_items_Complete_it:
  assumes "bins_eq_items as bs" "item_origin x < length as"
  shows "items (Complete_it k x as i) = items (Complete_it k x bs i)"
proof -
  let ?orig_a = "as ! item_origin x"
  let ?orig_b = "bs ! item_origin x"
  have "items ?orig_a = items ?orig_b"
    using assms by (metis (no_types, opaque_lifting) bins_eq_items_def length_map nth_map)
  thus ?thesis
    unfolding Complete_it_def by simp
qed

lemma \<pi>_it'_bins_items_eq:
  assumes "(k, cfg, inp, as) \<in> wellformed_bins"
  assumes "bins_eq_items as bs" "wf_bins cfg inp as"
  shows "bins_eq_items (\<pi>_it' k cfg inp as i) (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction i arbitrary: bs rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Base k cfg inp as i)
  have "\<pi>_it' k cfg inp as i = as"
    by (simp add: Base.hyps)
  moreover have "\<pi>_it' k cfg inp bs i = bs"
    using Base.hyps Base.prems(1,2) unfolding bins_eq_items_def
    by (metis \<pi>_it'_simps(1) length_map nth_map wellformed_bins_elim)
  ultimately show ?case
    using Base.prems(2) by presburger
next
  case (Complete k cfg inp as i x)
  let ?as' = "bins_upd as k (Complete_it k x as i)"
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have k: "k < length as"
    using Complete.prems(1) wellformed_bins_elim by blast
  hence wf_x: "wf_item cfg inp x"
    using Complete.hyps(1,2) Complete.prems(3) wf_bins_kth_bin by fastforce
  have "(k, cfg, inp, ?as') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  moreover have "bins_eq_items ?as' ?bs'"
    using Complete.hyps(1,2) Complete.prems(2,3) bins_eq_items_dist_bins_upd bins_eq_items_Complete_it 
      k wf_x wf_bins_kth_bin wf_item_def by (metis dual_order.strict_trans2 leI nth_mem)
  ultimately have "bins_eq_items (\<pi>_it' k cfg inp ?as' (i + 1)) (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using Complete.IH wellformed_bins_elim by blast
  moreover have "\<pi>_it' k cfg inp as i = \<pi>_it' k cfg inp ?as' (i+1)"
    using Complete.hyps by simp
  moreover have "\<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp ?bs' (i+1)"
    using Complete.hyps Complete.prems unfolding bins_eq_items_def
    by (metis \<pi>_it'_simps(2) map_eq_imp_length_eq nth_map wellformed_bins_elim)
  ultimately show ?case
    by argo
next
  case (Scan k cfg inp as i x a)
  let ?as' = "bins_upd as (k+1) (Scan_it k inp a x i)"
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "(k, cfg, inp, ?as') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by fast
  moreover have "bins_eq_items ?as' ?bs'"
    using Scan.hyps(5) Scan.prems(1,2) bins_eq_items_dist_bins_upd add_mono1 wellformed_bins_elim by metis
  ultimately have "bins_eq_items (\<pi>_it' k cfg inp ?as' (i + 1)) (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using Scan.IH wellformed_bins_elim by blast
  moreover have "\<pi>_it' k cfg inp as i = \<pi>_it' k cfg inp ?as' (i+1)"
    using Scan.hyps by simp
  moreover have "\<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp ?bs' (i+1)"
    using Scan.hyps Scan.prems unfolding bins_eq_items_def
    by (smt (verit, ccfv_threshold) \<pi>_it'_simps(3) length_map nth_map wellformed_bins_elim)
  ultimately show ?case
    by argo
next
  case (Pass k cfg inp as i x a)
  have "bins_eq_items (\<pi>_it' k cfg inp as (i + 1)) (\<pi>_it' k cfg inp bs (i + 1))"
    using Pass.prems Pass.IH by blast
  moreover have "\<pi>_it' k cfg inp as i = \<pi>_it' k cfg inp as (i+1)"
    using Pass.hyps by simp
  moreover have "\<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp bs (i+1)"
    using Pass.hyps Pass.prems unfolding bins_eq_items_def
    by (metis \<pi>_it'_simps(4) map_eq_imp_length_eq nth_map wellformed_bins_elim)
  ultimately show ?case
    by argo
next
  case (Predict k cfg inp as i x a)
  let ?as' = "bins_upd as k (Predict_it k cfg a)"
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "(k, cfg, inp, ?as') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by fast
  moreover have "bins_eq_items ?as' ?bs'"
    using Predict.prems(1,2) bins_eq_items_dist_bins_upd wellformed_bins_elim by blast
  ultimately have "bins_eq_items (\<pi>_it' k cfg inp ?as' (i + 1)) (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using Predict.IH wellformed_bins_elim by blast
  moreover have "\<pi>_it' k cfg inp as i = \<pi>_it' k cfg inp ?as' (i+1)"
    using Predict.hyps by simp
  moreover have "\<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp ?bs' (i+1)"
    using Predict.hyps Predict.prems unfolding bins_eq_items_def
    by (metis \<pi>_it'_simps(5) length_map nth_map wellformed_bins_elim)
  ultimately show ?case
    by argo
qed

lemma \<pi>_it'_idem:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "i \<le> j" "sound_items cfg inp (bins_items bs)" "nonempty_derives cfg"
  shows "bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j) = bins_items (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction i arbitrary: j rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by auto
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  have "sound_items cfg inp (set (items (Complete_it k x bs i)))"
    using x sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  hence sound: "sound_items cfg inp (bins_items ?bs')"
    by (metis Complete.prems(1) Complete.prems(3) UnE bins_bins_upd sound_items_def wellformed_bins_elim)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using wf sound Complete \<pi>_it'_simps(2) by metis
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Complete.prems(2) by simp
    have "bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j) = bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j)"
      using \<pi>_it'_simps(2) Complete.hyps(1-3) by simp
    also have "... = bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1))"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_bins_upd order_trans wf Complete.hyps Complete.prems(1)
        by (smt (verit, ccfv_threshold) \<pi>_it'_simps(2))
      hence 0: "\<not> length (items (?bs'' ! k)) \<le> j"
        using \<open>i = j\<close> Complete.hyps(1) by linarith
      have "x = items (?bs' ! k) ! j"
        using \<open>i = j\<close> items_nth_idem_bins_upd Complete.hyps(1,2)
        by (metis items_def length_map not_le_imp_less)
      hence 1: "x = items (?bs'' ! k) ! j"
        using \<open>i = j\<close> kth_\<pi>_it'_bins Complete.hyps Complete.prems(1) \<pi>_it'_simps(2) leI by metis
      have "bins_items (\<pi>_it' k cfg inp ?bs'' j) = bins_items (\<pi>_it' k cfg inp (bins_upd ?bs'' k (Complete_it k x ?bs'' i)) (j+1))"
        using \<pi>_it'_simps(2) 0 1 Complete.hyps(1,3) Complete.prems(2) \<open>i = j\<close> by auto
      moreover have "bins_eq_items (bins_upd ?bs'' k (Complete_it k x ?bs'' i)) ?bs''"
      proof -
        have "k < length bs"
          using Complete.prems(1) wellformed_bins_elim by blast
        have 0: "set (Complete_it k x bs i) = set (Complete_it k x ?bs'' i)"
        proof (cases "item_origin x = k")
          case True
          thus ?thesis
            using impossible_complete_item kth_bin_sub_bins Complete.hyps(3) Complete.prems wellformed_bins_elim
              wf_bins_kth_bin x sound_items_def next_symbol_def by (metis option.distinct(1) subsetD)
        next
          case False
          hence "item_origin x < k"
            using x Complete.prems(1) wf_bins_kth_bin wf_item_def nat_less_le by (metis wellformed_bins_elim)
          hence "bs ! item_origin x = ?bs'' ! item_origin x"
            using False nth_idem_bins_upd nth_\<pi>_it'_eq wf by metis
          thus ?thesis
            using Complete_it_eq_item_origin by metis
        qed
        have "set (items (Complete_it k x bs i)) \<subseteq> set (items (?bs' ! k))"
          by (simp add: \<open>k < length bs\<close> bins_upd_def set_items_bin_upds)
        hence "set (items (Complete_it k x ?bs'' i)) \<subseteq> set (items (?bs' ! k))"
          using 0 by (simp add: items_def)
        also have "... \<subseteq> set (items (?bs'' ! k))"
          by (simp add: wf nth_bin_sub_\<pi>_it')
        finally show ?thesis
          using bins_eq_items_bins_upd by blast
      qed
      moreover have "(k, cfg, inp, bins_upd ?bs'' k (Complete_it k x ?bs'' i)) \<in> wellformed_bins"
        using wellformed_bins_\<pi>_it' wellformed_bins_Complete_it Complete.hyps Complete.prems(1)
          \<open>length (items (bs ! k)) \<le> length (items (?bs'' ! k))\<close> kth_\<pi>_it'_bins 0 1 by blast
      ultimately show ?thesis
        using \<pi>_it'_bins_items_eq bins_eq_items_imp_eq_bins_items wellformed_bins_elim by blast
    qed
    also have "... = bins_items (\<pi>_it' k cfg inp ?bs' (i + 1))"
      using Complete.IH[OF wf _ sound Complete.prems(4)] \<open>i = j\<close> by blast
    finally show ?thesis
      using Complete.hyps by simp
  qed
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have x: "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by auto
  hence "sound_items cfg inp (set (items (Scan_it k inp a x i)))"
    using sound_Scan_it \<pi>_mono Scan.hyps(3,5) Scan.prems(1,2,3) bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  hence sound: "sound_items cfg inp (bins_items ?bs')"
    using Scan.hyps(5) Scan.prems(1,3) bins_bins_upd sound_items_def wellformed_bins_elim
    by (metis UnE add_less_cancel_right)
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using sound Scan by (metis \<pi>_it'_simps(3) wellformed_bins_Scan_it)
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Scan.prems(2) by auto
    have "bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j) = bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j)"
      using Scan.hyps by simp
    also have "... = bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1))"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_bins_upd order_trans Scan.hyps Scan.prems(1) \<pi>_it'_simps(3)
        by (smt (verit, ccfv_SIG))
      hence "bins_items (\<pi>_it' k cfg inp ?bs'' j) = bins_items (\<pi>_it' k cfg inp (bins_upd ?bs'' (k+1) (Scan_it k inp a x i)) (j+1))"
        using \<open>i = j\<close> kth_\<pi>_it'_bins nth_idem_bins_upd \<pi>_it'_simps(3) Scan.hyps Scan.prems(1) by (smt (verit, best) leI le_trans)
      moreover have "bins_eq_items (bins_upd ?bs'' (k+1) (Scan_it k inp a x i)) ?bs''"
      proof -
        have "k+1 < length bs"
          using Scan.hyps(5) Scan.prems wellformed_bins_elim by fastforce+
        hence "set (items (Scan_it k inp a x i)) \<subseteq> set (items (?bs' ! (k+1)))"
          by (simp add: bins_upd_def set_items_bin_upds)
        also have "... \<subseteq> set (items (?bs'' ! (k+1)))"
          using wf nth_bin_sub_\<pi>_it' by blast
        finally show ?thesis
          using bins_eq_items_bins_upd by blast
      qed
      moreover have "(k, cfg, inp, bins_upd ?bs'' (k+1) (Scan_it k inp a x i)) \<in> wellformed_bins"
        using wellformed_bins_\<pi>_it' wellformed_bins_Scan_it Scan.hyps Scan.prems(1)
          \<open>length (items (bs ! k)) \<le> length (items (?bs'' ! k))\<close> kth_\<pi>_it'_bins
        by (smt (verit, ccfv_SIG) \<pi>_it'_simps(3) linorder_not_le order.trans)
      ultimately show ?thesis
        using \<pi>_it'_bins_items_eq bins_eq_items_imp_eq_bins_items wellformed_bins_elim by blast
    qed
    also have "... = bins_items (\<pi>_it' k cfg inp ?bs' (i + 1))"
      using \<open>i = j\<close> Scan.IH Scan.prems Scan.hyps sound wellformed_bins_Scan_it by fast
    finally show ?thesis
      using Scan.hyps by simp
  qed
next
  case (Pass k cfg inp bs i x a)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using Pass by (metis \<pi>_it'_simps(4))
  next
    assume "\<not> i+1 \<le> j"
    show ?thesis
      using Pass \<pi>_it'_simps(1,4) kth_\<pi>_it'_bins by (metis Suc_eq_plus1 Suc_leI antisym_conv2 not_le_imp_less)
  qed
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have x: "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by auto
  hence "sound_items cfg inp (set (items (Predict_it k cfg a)))"
    using sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems bins_bin_exists wellformed_bins_elim
          sound_\<pi> wf_bins_kth_bin wf_items_def by metis
  hence sound: "sound_items cfg inp (bins_items ?bs')"
    using Predict.prems(1,3) UnE bins_bins_upd sound_items_def wellformed_bins_elim by metis
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  have len: "i < length (items (?bs' ! k))"
    using length_nth_bin_bins_upd Predict.hyps(1) Orderings.preorder_class.dual_order.strict_trans1 linorder_not_less
    by (metis items_def length_map)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using sound wf Predict by (metis \<pi>_it'_simps(5))
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Predict.prems(2) by auto
    have "bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j) = bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j)"
      using Predict.hyps by simp
    also have "... = bins_items (\<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1))"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_bins_upd order_trans wf
        by (metis (no_types, lifting) items_def length_map)
      hence "bins_items (\<pi>_it' k cfg inp ?bs'' j) = bins_items (\<pi>_it' k cfg inp (bins_upd ?bs'' k (Predict_it k cfg a)) (j+1))"
        using \<open>i = j\<close> kth_\<pi>_it'_bins nth_idem_bins_upd \<pi>_it'_simps(5) Predict.hyps Predict.prems(1) length_bins_\<pi>_it'
          wf_bins_\<pi>_it' wf_bins_kth_bin wf_item_def x by (smt (verit, ccfv_SIG) linorder_not_le order.trans)
      moreover have "bins_eq_items (bins_upd ?bs'' k (Predict_it k cfg a)) ?bs''"
      proof -
        have "k < length bs"
          using wellformed_bins_elim[OF Predict.prems(1)] by blast
        hence "set (items (Predict_it k cfg a)) \<subseteq> set (items (?bs' ! k))"
          by (simp add: bins_upd_def set_items_bin_upds)
        also have "... \<subseteq> set (items (?bs'' ! k))"
          using wf nth_bin_sub_\<pi>_it' by blast
        finally show ?thesis
          using bins_eq_items_bins_upd by blast
      qed
      moreover have "(k, cfg, inp, bins_upd ?bs'' k (Predict_it k cfg a)) \<in> wellformed_bins"
        using wellformed_bins_\<pi>_it' wellformed_bins_Predict_it Predict.hyps Predict.prems(1)
          \<open>length (items (bs ! k)) \<le> length (items (?bs'' ! k))\<close> kth_\<pi>_it'_bins
        by (smt (verit, best) \<pi>_it'_simps(5) dual_order.trans not_le_imp_less)
      ultimately show ?thesis
        using \<pi>_it'_bins_items_eq bins_eq_items_imp_eq_bins_items wellformed_bins_elim by blast
    qed
    also have "... = bins_items (\<pi>_it' k cfg inp ?bs' (i + 1))"
      using \<open>i = j\<close> Predict.IH Predict.prems sound wf by (metis order_refl)
    finally show ?thesis
      using Predict.hyps by simp
  qed
qed simp

lemma \<pi>_it_idem:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins_items bs)" "nonempty_derives cfg"
  shows "bins_items (\<pi>_it k cfg inp (\<pi>_it k cfg inp bs)) = bins_items (\<pi>_it k cfg inp bs)"
  using assms \<pi>_it'_idem \<pi>_it_def le0 by metis

lemma funpower_\<pi>_step_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs" "sound_items cfg inp (bins_items bs)"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "funpower (\<pi>_step k cfg inp) n (bins_items bs) \<subseteq> bins_items (\<pi>_it k cfg inp bs)"
  using assms
proof (induction n)
  case 0
  thus ?case
    by (simp add: \<pi>_it'_mono \<pi>_it_def)
next
  case (Suc n)
  have 0: "\<pi>_step k cfg inp (bins_items_upto (\<pi>_it k cfg inp bs) k 0) \<subseteq> bins_items (\<pi>_it k cfg inp bs)"
    using \<pi>_it'_mono bins_upto_k0_\<pi>_it'_eq \<pi>_it_def order_trans by (metis (no_types, lifting) assms(1,2))
  have "funpower (\<pi>_step k cfg inp) (Suc n) (bins_items bs) \<subseteq> \<pi>_step k cfg inp (bins_items (\<pi>_it k cfg inp bs))"
    using \<pi>_step_sub_mono Suc by (metis funpower.simps(2))
  also have "... \<subseteq> bins_items (\<pi>_it k cfg inp (\<pi>_it k cfg inp bs))"
    using \<pi>_step_sub_\<pi>_it Suc.prems wf_bins_\<pi>_it sound_\<pi>_it 0 wellformed_bins_\<pi>_it by blast
  also have "... \<subseteq> bins_items (\<pi>_it k cfg inp bs)"
    using \<pi>_it_idem Suc.prems by blast
  finally show ?case .
qed

lemma \<pi>_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_items_upto bs k 0) \<subseteq> bins_items bs" "sound_items cfg inp (bins_items bs)"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi> k cfg inp (bins_items bs) \<subseteq> bins_items (\<pi>_it k cfg inp bs)"
  using assms funpower_\<pi>_step_sub_\<pi>_it \<pi>_def elem_limit_simp by fastforce

lemma \<I>_sub_\<I>_it:
  assumes "k \<le> length inp" "wf_cfg cfg"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "\<I> k cfg inp \<subseteq> bins_items (\<I>_it k cfg inp)"
  using assms
proof (induction k)
  case 0
  hence "\<pi> 0 cfg inp (Init cfg) \<subseteq> bins_items (\<pi>_it 0 cfg inp (Init_it cfg inp))"
    using \<pi>_sub_\<pi>_it Init_it_eq_Init length_bins_Init_it Init_it_eq_Init sound_Init bins_items_upto_empty
          \<pi>_step_empty bins_items_upto_sub_bins_items wellformed_bins_Init_it wellformed_bins_elim by metis
  thus ?case
    by simp
next
  case (Suc k)
  have wf: "(Suc k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
    by (simp add: Suc.prems(1) Suc_leD assms(2) wellformed_bins_intro)
  have sub: "\<pi>_step (Suc k) cfg inp (bins_items_upto (\<I>_it k cfg inp) (Suc k) 0) \<subseteq> bins_items (\<I>_it k cfg inp)"
  proof -
    have "bin (bins_items_upto (\<I>_it k cfg inp) (Suc k) 0) (Suc k) = {}"
      using kth_bin_bins_upto_empty wf Suc.prems wellformed_bins_elim by blast
    hence "\<pi>_step (Suc k) cfg inp (bins_items_upto (\<I>_it k cfg inp) (Suc k) 0) = bins_items_upto (\<I>_it k cfg inp) (Suc k) 0"
      unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast
    also have "... \<subseteq> bins_items (\<I>_it k cfg inp)"
      using wf Suc.prems bins_items_upto_sub_bins_items wellformed_bins_elim by blast
    finally show ?thesis .
  qed
  have sound: "sound_items cfg inp (bins_items (\<I>_it k cfg inp))"
    using Suc sound_\<I> \<I>_it_sub_\<I> by (metis Suc_leD subset_antisym)
  have "\<I> (Suc k) cfg inp \<subseteq> \<pi> (Suc k) cfg inp (bins_items (\<I>_it k cfg inp))"
    using Suc \<pi>_sub_mono by simp
  also have "... \<subseteq> bins_items (\<pi>_it (Suc k) cfg inp (\<I>_it k cfg inp))"
    using \<pi>_sub_\<pi>_it wf sub sound Suc.prems by fastforce
  finally show ?case
    by simp
qed

lemma \<II>_sub_\<II>_it:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<II> cfg inp \<subseteq> bins_items (\<II>_it cfg inp)"
  using assms \<I>_sub_\<I>_it \<II>_def \<II>_it_def by (metis le_refl)


subsection \<open>Correctness\<close>

definition earley_recognized_it :: "'a bins \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "earley_recognized_it I cfg inp = (\<exists>x \<in> set (items (I ! length inp)). is_finished cfg inp x)"

theorem earley_recognized_it_iff_earley_recognized:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "earley_recognized_it (\<II>_it cfg inp) cfg inp \<longleftrightarrow> earley_recognized (\<II> cfg inp) cfg inp"
proof -
  have "earley_recognized_it (\<II>_it cfg inp) cfg inp = (\<exists>x \<in> set (items ((\<II>_it cfg inp) ! length inp)). is_finished cfg inp x)"
    unfolding earley_recognized_it_def by blast
  also have "... = (\<exists>x \<in> bins_items (\<II>_it cfg inp). is_finished cfg inp x)"
    using is_finished_def kth_bin_sub_bins \<II>_it_def length_bins_Init_it wf_bins_\<II>_it
      wf_item_in_kth_bin length_\<I>_it assms(1)
    by (smt (verit) le_eq_less_or_eq subset_code(1) wellformed_bins_\<I>_it wellformed_bins_elim)
  also have "... = (\<exists>x \<in> \<II> cfg inp. is_finished cfg inp x)"
    using assms \<II>_it_sub_\<II> \<II>_sub_\<II>_it by blast
  also have "... = earley_recognized (\<II> cfg inp) cfg inp"
    unfolding earley_recognized_def by blast
  finally show ?thesis .
qed

corollary correctness_list:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "earley_recognized_it (\<II>_it cfg inp) cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
  using assms correctness_set earley_recognized_it_iff_earley_recognized by blast


section \<open>Earley parse trees\<close>

subsection \<open>Main definitions\<close>

datatype 'a dtree =
  Leaf 'a
  | Node 'a "'a dtree list"

fun yield_dtree :: "'a dtree \<Rightarrow> 'a sentence" where
  "yield_dtree (Leaf a) = [a]"
| "yield_dtree (Node _ ts) = concat (map yield_dtree ts)"

fun root_dtree :: "'a dtree \<Rightarrow> 'a" where
  "root_dtree (Leaf a) = a"
| "root_dtree (Node N _) = N"

fun wf_rule_dtree :: "'a cfg \<Rightarrow> 'a dtree \<Rightarrow> bool" where
  "wf_rule_dtree _ (Leaf a) \<longleftrightarrow> True"
| "wf_rule_dtree cfg (Node N ts) \<longleftrightarrow> (
    (\<exists>r \<in> set (\<RR> cfg). N = rule_head r \<and> map root_dtree ts = rule_body r) \<and>
    (\<forall>t \<in> set ts. wf_rule_dtree cfg t))"

fun wf_item_dtree :: "'a cfg \<Rightarrow> 'a item \<Rightarrow> 'a dtree \<Rightarrow> bool" where
  "wf_item_dtree cfg _ (Leaf a) \<longleftrightarrow> True"
| "wf_item_dtree cfg x (Node N ts) \<longleftrightarrow> (
    N = item_rule_head x \<and> map root_dtree ts = take (item_dot x) (item_rule_body x) \<and>
    (\<forall>t \<in> set ts. wf_rule_dtree cfg t))"

definition wf_yield_dtree :: "'a sentence \<Rightarrow> 'a item \<Rightarrow> 'a dtree \<Rightarrow> bool" where
  "wf_yield_dtree inp x t \<longleftrightarrow> yield_dtree t = slice (item_origin x) (item_end x) inp"

function build_dtree' :: "'a bins \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a dtree" where
  "build_dtree' bs inp k i = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Node (item_rule_head (item e)) [] \<comment>\<open>start building sub-tree\<close>
    | Pre pre \<Rightarrow> ( \<comment>\<open>add sub-tree starting from terminal\<close>
      case build_dtree' bs inp (k-1) pre of
        Node N ts \<Rightarrow> Node N (ts @ [Leaf (inp!(k-1))])
      | _ \<Rightarrow> undefined) \<comment>\<open>impossible case\<close>
    | PreRed (k', pre, red) _ \<Rightarrow> ( \<comment>\<open>add sub-tree starting from non-terminal\<close>
      case build_dtree' bs inp k' pre of
        Node N ts \<Rightarrow> Node N (ts @ [build_dtree' bs inp k red])
      | _ \<Rightarrow> undefined) \<comment>\<open>impossible case\<close>
    ))"
  by pat_completeness auto
termination sorry

declare build_dtree'.simps [simp del]

definition build_dtree :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a dtree option" where
  "build_dtree cfg inp bs = (
    let k = length bs - 1 in
    case filter_with_index (\<lambda>x. is_finished cfg inp x) (items (bs!k)) of
      [] \<Rightarrow> None
    | (_,i)#_ \<Rightarrow> Some (build_dtree' bs inp k i)
  )"

definition valid_ptrs :: "'a bins \<Rightarrow> bool" where
  "valid_ptrs bs = (\<forall>k < length bs. \<forall>i < length (bs!k).
    (\<forall>pre. Pre pre = pointer (bs!k!i) \<longrightarrow> pre < length (bs!(k-1))) \<and>
    (\<forall>p ps k' pre red. PreRed p ps = pointer (bs!k!i) \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow>
      k' < k \<and> pre < length (bs!k') \<and> red < i))"

definition predicts :: "'a item \<Rightarrow> bool" where
  "predicts x \<longleftrightarrow> item_origin x = item_end x \<and> item_dot x = 0"

definition scans :: "'a sentence \<Rightarrow> nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "scans inp k x y \<longleftrightarrow> 0 < k \<and> y = inc_item x k \<and> 
    (\<exists>a. next_symbol x = Some a \<and> inp!(k-1) = a)"

definition completes :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "completes k x y z \<longleftrightarrow> y = inc_item x k \<and> is_complete z \<and> item_origin z = item_end x \<and>
    (\<exists>N. next_symbol x = Some N \<and> N = item_rule_head z)"

definition wf_ptrs :: "'a sentence \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "wf_ptrs inp bs \<longleftrightarrow> (\<forall>k < length bs. \<forall>i < length (bs!k). (
    (pointer (bs!k!i) = Null \<longleftrightarrow> predicts (item (bs!k!i))) \<and>
    (\<forall>pre. pointer (bs!k!i) = Pre pre \<longleftrightarrow> scans inp k (item (bs!(k-1)!pre)) (item (bs!k!i))) \<and>
    (\<forall>p ps k' pre red. (pointer (bs!k!i) = PreRed p ps \<and> (k', pre, red) \<in> set (p#ps)) \<longleftrightarrow> 
      completes k (item (bs!k'!pre)) (item (bs!k!i)) (item (bs!k!red)))))"


subsection \<open>Lemmas\<close>

lemma build_tree'_simps[simp]:
  "e = bs!k!i \<Longrightarrow> pointer e = Null \<Longrightarrow> build_dtree' bs inp k i = Node (item_rule_head (item e)) []"
  "e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> build_dtree' bs inp (k-1) pre = Node N ts \<Longrightarrow> 
    build_dtree' bs inp k i = Node N (ts @ [Leaf (inp!(k-1))])"
  "e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) ps \<Longrightarrow> build_dtree' bs inp k' pre = Node N ts \<Longrightarrow>
    build_dtree' bs inp k i = Node N (ts @ [build_dtree' bs inp k red])"
  by (auto simp: build_dtree'.simps Let_def)

lemma ex_Node_build_tree':
  "\<exists>N ts. build_dtree' bs inp k i = Node N ts"
  apply (induction bs inp k i rule: build_dtree'.induct)
  apply (subst build_dtree'.simps)
  apply (auto simp: Let_def split: list.splits dtree.splits pointer.splits)
  by (metis dtree.distinct(1))+

lemma nex_Leaf_build_tree':
  "\<nexists>a. build_dtree' bs inp k i = Leaf a"
  using ex_Node_build_tree' by (metis dtree.distinct(1))

definition valid_pre_ptr :: "'a entry \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_pre_ptr e n c = (\<forall>pre. Pre pre = pointer e \<longrightarrow> pre < n + c)"

definition valid_pre_ptrs :: "'a bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_pre_ptrs bs c K = (
    \<forall>k < length bs. \<forall>i < length (bs!k). 
      (k-1 = K-1 \<longrightarrow> valid_pre_ptr (bs!k!i) (length (bs!(k-1))) c) \<and>
      (k-1 \<noteq> K-1 \<longrightarrow> valid_pre_ptr (bs!k!i) (length (bs!(k-1))) 0))"

lemma valid_pre_ptrs_bin_upd:
  assumes "valid_pre_ptrs bs c k" "k < length bs" "es = bs!k"
  assumes "valid_pre_ptr e (length (bs!(k-1))) c"
  shows "valid_pre_ptrs (bs[k := bin_upd e es]) c k"
  using assms
proof (induction es arbitrary: e bs c)
  case Nil
  let ?bs = "bs[k := [e]]"
  {
    fix l i pre
    assume a0: "l < length ?bs"
    assume a1: "i < length (?bs!l)"
    assume a2: "Pre pre = pointer (?bs!l!i)"
    have "pre < length (?bs!(l-1)) + c"
    proof cases
      assume "l = k"
      hence "valid_pre_ptr (?bs!l!i) (length (bs!(k-1))) c"
        using Nil.prems(2,4) a1 by auto
      moreover have "length (bs!(k-1)) \<le> length (?bs!(k-1))"
        using Nil.prems(3) by (cases k) auto
      ultimately have "valid_pre_ptr (?bs!l!i) (length (?bs!(k-1))) c"
        unfolding valid_pre_ptr_def by auto
      thus ?thesis
        using \<open>l = k\<close> a2 valid_pre_ptr_def by blast
    next
      assume "\<not> l = k"
      hence "l < length bs" "i < length (bs!l)" "Pre pre = pointer (bs!l!i)"
        using a0 a1 a2 \<open>l \<noteq> k\<close> by auto
      hence "pre < length (bs!(l-1)) + c"
        using Nil.prems(1) unfolding valid_pre_ptrs_def valid_pre_ptr_def by blast
      moreover have "l-1 \<noteq> k \<Longrightarrow> bs[k := [e]]!(l-1) = bs!(l-1)"
        by simp
      moreover have "l-1 = k \<Longrightarrow> pre < c"
        using \<open>pre < length (bs!(l-1)) + c\<close> Nil.prems(3) by simp
      ultimately show ?thesis
        by force
    qed
  }
  hence "valid_pre_ptrs (?bs[k := bin_upd e []]) c"
    unfolding valid_pre_ptrs_def valid_pre_ptr_def by simp
  thus ?case
    by simp
next
  case (Cons e' es')
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> e' = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where ee': "e = Entry x (PreRed xp xs)" "e' = Entry y (PreRed yp ys)"
      by blast
    thus ?thesis
    proof cases
      assume *: "x = y"
      let ?bs = "bs[k := Entry x (PreRed xp (yp # xs @ ys)) # es']"
      {
        fix l i pre
        assume a0: "l < length ?bs"
        assume a1: "i < length (?bs!l)"
        assume a2: "Pre pre = pointer (?bs!l!i)"
        have "pre < length (?bs!(l-1)) + c"
        proof cases
          assume "l = k"
          have "i \<noteq> 0 \<Longrightarrow> Pre pre = pointer (bs!l!i)"
            using Cons.prems(2,3) a2 by (metis nth_Cons' nth_list_update_eq nth_list_update_neq)
          moreover have "l < length bs"
            using Cons.prems(2,3) \<open>l = k\<close> by blast
          moreover have "i < length (bs!l)"
            by (metis Cons.prems(3) \<open>l = k\<close> a1 calculation(2) length_Cons nth_list_update_eq)
          moreover have "length (bs!(l-1)) = length (?bs!(l-1))"
            using Cons.prems(2,3) \<open>l = k\<close> by (metis length_Cons nth_list_update_eq nth_list_update_neq)
          ultimately have "i \<noteq> 0 \<Longrightarrow> pre < length (?bs!(l-1)) + c"
            using Cons.prems(1) unfolding valid_pre_ptrs_def valid_pre_ptr_def by auto
          thus ?thesis
            using Cons.prems(2) \<open>l = k\<close> a2 by force
        next
          assume "\<not> l = k"
          have "length (?bs!(l-1)) \<ge> length (bs!(l-1))"
            using Cons.prems(2,3) by (metis dual_order.refl length_Cons nth_list_update_eq nth_list_update_neq)
          moreover have "pre < length (bs!(l-1)) + c"
            using Cons.prems(1) \<open>l \<noteq> k\<close> a0 a1 a2 unfolding valid_pre_ptr_def valid_pre_ptrs_def by simp
          ultimately show ?thesis
            by simp
        qed
      }
      hence "valid_pre_ptrs ?bs c"
        unfolding valid_pre_ptrs_def valid_pre_ptr_def by blast
      moreover have "bin_upd e (e' # es') = Entry x (PreRed xp (yp # xs @ ys)) # es'"
        using ee' * by simp
      ultimately show ?thesis
        by simp
    next
      assume *: "\<not> x = y"
      let ?bs = "bs[k := es']"
      {
        fix l i pre
        assume a0: "l < length ?bs"
        assume a1: "i < length (?bs!l)"
        assume a2: "Pre pre = pointer (?bs!l!i)"
        have "l < length bs"
          using a0 by auto
        have "l \<noteq> k \<Longrightarrow> bs!l!i = ?bs!l!i"
          by simp
        moreover have "l \<noteq> k \<Longrightarrow> i < length (bs!l)"
          using a1 by force
        ultimately have 0: "l \<noteq> k \<Longrightarrow> pre < length (bs!(l-1)) + c"
          using Cons.prems(1) \<open>l < length bs\<close> a2 unfolding valid_pre_ptrs_def valid_pre_ptr_def by simp
        have "l = k \<Longrightarrow> bs!l!(i+1) = ?bs!l!i"
          using Cons.prems(2,3) by (auto, metis nth_Cons_Suc)
        moreover have "l = k \<Longrightarrow> i+1 < length (bs!l)"
          using Cons.prems(3) \<open>l < length bs\<close> a1 by (auto, metis Suc_less_eq length_Cons)
        ultimately have 1: "l = k \<Longrightarrow> pre < length (bs!(l-1)) + c"
          using Cons.prems(1) \<open>l < length bs\<close> a2 unfolding valid_pre_ptrs_def valid_pre_ptr_def by simp
        have "l-1 = k \<Longrightarrow> length (bs!(l-1)) = length (?bs!(l-1)) + 1"
          using Cons.prems(2,3) by (auto, metis length_Cons)
        hence "pre < length (?bs!(l-1)) + (c+1)"
          using 0 1 by fastforce
      }
      hence "valid_pre_ptrs ?bs (c+1)"
        unfolding valid_pre_ptrs_def valid_pre_ptr_def by blast
      moreover have "valid_pre_ptr e (length (?bs!(k-1))) (c+1)"
        using True valid_pre_ptr_def by force
      ultimately have "valid_pre_ptrs (?bs[k := bin_upd e es']) (c+1)"
        using Cons.IH Cons.prems(2) by (metis length_list_update nth_list_update_eq)
      hence "valid_pre_ptrs (bs[k := bin_upd e es']) (c+1)"
        by simp
      let ?bs' = "bs[k := e' # bin_upd e es']"
      {
        fix l i pre
        assume a0: "l < length ?bs'"
        assume a1: "i < length (?bs'!l)"
        assume a2: "Pre pre = pointer (?bs'!l!i)"
        have "l < length bs"
          using a0 by fastforce
        have "k \<noteq> l \<Longrightarrow> i < length (bs!l)"
          using a1 by simp
        moreover have "k \<noteq> l \<Longrightarrow> Pre pre = pointer (bs!l!i)"
          by (simp add: a2)
        ultimately have "k \<noteq> l \<Longrightarrow> pre < length (bs!(l-1)) + c"
          using Cons.prems(1) \<open>l < length bs\<close> unfolding valid_pre_ptrs_def valid_pre_ptr_def by blast
        moreover have "length (bs!(l-1)) \<le> length (?bs'!(l-1))"
          using Cons.prems(2,3) length_bin_upd
          by (cases "l-1 = k") (auto, smt (verit, del_insts) Suc_le_mono length_Cons length_bin_upd)
        ultimately have 0: "k \<noteq> l \<Longrightarrow> pre < length (?bs'!(l-1)) + c"
          by simp

        let ?bs'' = "bs[k := bin_upd e es']"
        have "l < length ?bs''"
          using a0 by force
        moreover have "i > 0 \<Longrightarrow> i-1 < length (?bs''!l)"
          using Cons.prems(2) a1 by (metis One_nat_def Suc_leI less_diff_conv2 less_imp_diff_less list.size(4) nth_list_update_eq nth_list_update_neq)
        moreover have "k = l \<Longrightarrow> i > 0 \<Longrightarrow> Pre pre = pointer (?bs''!l!(i-1))"
          using Cons.prems(2) a2 by simp
        ultimately have "k = l \<Longrightarrow> i > 0 \<Longrightarrow> pre < length (?bs''!(l-1)) + (c+1)"
          using \<open>valid_pre_ptrs (bs[k := bin_upd e es']) (c+1)\<close> unfolding valid_pre_ptrs_def valid_pre_ptr_def by blast

        have "k = l-1 \<Longrightarrow> length (?bs''!(l-1)) + 1 = length (?bs'!(l-1))"
          using Cons.prems(2) by (metis One_nat_def list.size(4) nth_list_update_eq)

        have "pre < (length (?bs'!(l-1))) + c"
          using 0 sorry
      }
      hence "valid_pre_ptrs (bs[k := e' # bin_upd e es']) c"
        unfolding valid_pre_ptrs_def valid_pre_ptr_def by blast
      thus ?thesis
        using ee' * by simp
    qed
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item e'"
      hence "bin_upd e (e' # es') = e' # es'"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using Cons.prems(1,2,3) by auto
    next
      assume *: "\<not> item e = item e'"
      hence "bin_upd e (e' # es') = e' # bin_upd e es'"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        sorry
    qed
  qed
qed

lemma valid_ptrs_bin_upd: \<comment>\<open>TODO\<close>
  assumes "valid_ptrs bs" "es = bs!k" "k < length bs"
  assumes "(\<forall>pre. Pre pre = pointer e \<longrightarrow> pre < length (bs!(k-1)))"
  assumes "(\<forall>p ps k' pre red. PreRed p ps = pointer e \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow> k' < k \<and> pre < length (bs!k') \<and> red < length (bs!k))"
  shows "valid_ptrs (bs[k := bin_upd e es])"
  using assms
proof (induction es arbitrary: e bs)
  case Nil
  let ?bs = "bs[k := [e]]"
  have 1: "\<And>l. l \<noteq> k \<Longrightarrow> l < length ?bs \<Longrightarrow> 
    \<forall>i<length (?bs ! l).
       (\<forall>pre. Pre pre = pointer (?bs ! l ! i) \<longrightarrow> pre < length (?bs ! (l - 1))) \<and>
       (\<forall>p ps k' pre red. PreRed p ps = pointer (?bs ! l ! i) \<and> (k', pre, red) \<in> set (p # ps) \<longrightarrow> k' < l \<and> pre < length (?bs ! k') \<and> red < i)"
    using Nil.prems(1,2) unfolding valid_ptrs_def by (smt (z3) gr_implies_not0 length_list_update list.size(3) nth_list_update_neq)
  have "?bs!k!0 = e"
    by (simp add: Nil.prems(3))
  show ?case
  proof (cases k)
    case 0
    have "length (?bs!(k-1)) = length (bs!(k-1)) + 1"
      using 0 Nil.prems(2,3) by auto
    have "k < length ?bs \<Longrightarrow>
    \<forall>i<length (?bs ! k).
       (\<forall>pre. Pre pre = pointer (?bs ! k ! i) \<longrightarrow> pre < length (?bs ! (k - 1))) \<and>
       (\<forall>p ps k' pre red. PreRed p ps = pointer (?bs ! k ! i) \<and> (k', pre, red) \<in> set (p # ps) \<longrightarrow> k' < k \<and> pre < length (?bs ! k') \<and> red < i)"
      using Nil.prems by (simp add: 0)
    thus ?thesis
      using 1 by (smt (verit, ccfv_threshold) bin_upd.simps(1) valid_ptrs_def)
  next
    case (Suc n)
    have "?bs ! Suc n ! 0 = e"
      using Suc \<open>bs[k := [e]] ! k ! 0 = e\<close> by blast
    have "(\<forall>pre. Pre pre = pointer (?bs ! Suc n ! 0) \<longrightarrow> pre < length (?bs ! (Suc n - 1)))"
      using Nil.prems(4) Suc \<open>bs[k := [e]] ! k ! 0 = e\<close> by auto
    have "(\<forall>p ps k' pre red. PreRed p ps = pointer (?bs ! Suc n ! 0) \<and> (k', pre, red) \<in> set (p # ps) \<longrightarrow> k' < Suc n \<and> pre < length (?bs ! k') \<and> red < 0)"
      using Nil.prems(5) Suc \<open>bs[k := [e]] ! k ! 0 = e\<close> Nil.prems(2) by force
    have "Suc n < length ?bs \<Longrightarrow>
    \<forall>i<length (?bs ! Suc n).
       (\<forall>pre. Pre pre = pointer (?bs ! Suc n ! i) \<longrightarrow> pre < length (?bs ! (Suc n - 1))) \<and>
       (\<forall>p ps k' pre red. PreRed p ps = pointer (?bs ! Suc n ! i) \<and> (k', pre, red) \<in> set (p # ps) \<longrightarrow> k' < Suc n \<and> pre < length (?bs ! k') \<and> red < i)"
      using Nil.prems using Suc by simp
    then show ?thesis
      using 1 by (smt (verit, ccfv_threshold) Suc bin_upd.simps(1) valid_ptrs_def)
  qed
next
  case (Cons e' es)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> e' = Entry y (PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where ee': "e = Entry x (PreRed xp xs)" "e' = Entry y (PreRed yp ys)"
      by blast
    thus ?thesis
    proof cases
      assume *: "x = y"
      let ?bs = "bs[k := Entry x (PreRed xp (yp # xs @ ys)) # es]"
      {
        fix l
        assume a0: "l < length ?bs"
        fix i
        assume a1: "i < length (?bs ! l)"
        fix pre
        assume a2: "Pre pre = pointer (?bs!l!i)"
        have "pre < length (?bs!(l-1))"
        proof cases
          assume "k \<noteq> l"
          have "length (?bs!(l-1)) \<ge> length (bs!(l-1))"
            using Cons.prems(2,3) by (metis dual_order.refl length_Cons nth_list_update_eq nth_list_update_neq)
          moreover have "pre < length (bs!(l-1))"
            using Cons.prems(1) valid_ptrs_def \<open>k \<noteq> l\<close> a0 a1 a2 by auto
          ultimately show ?thesis
            by simp
        next
          assume "\<not> k \<noteq> l"
          hence "k = l"
            by simp
          have "i \<noteq> 0 \<Longrightarrow> ?bs!l!i = bs!l!i"
            using Cons.prems(2,3) by (metis nth_Cons' nth_list_update_eq nth_list_update_neq)
          hence "i \<noteq> 0 \<Longrightarrow> Pre pre = pointer (bs!l!i)"
            using a2 by presburger
          moreover have "l < length bs"
            using Cons.prems(3) \<open>k = l\<close> by blast
          moreover have "i < length (bs!l)"
            by (metis Cons.prems(2) \<open>k = l\<close> a1 calculation(2) length_Cons nth_list_update_eq)
          ultimately have "i \<noteq> 0 \<Longrightarrow> pre < length (bs!(l-1))"
            using Cons.prems(1) valid_ptrs_def by blast
          moreover have "i = 0 \<Longrightarrow> ?bs!l!i = Entry x (PreRed xp (yp # xs @ ys))"
            using Cons.prems(3) \<open>k = l\<close> by auto
          ultimately show ?thesis
            using Cons.prems(2,3) a2 by (metis entry.sel(2) length_Cons nth_list_update_eq nth_list_update_neq pointer.distinct(5))
        qed
      }
      moreover
      {
        fix l
        assume a0: "l < length ?bs"
        fix i
        assume a1: "i < length (?bs ! l)"
        fix p ps k' pre red
        assume a2: "PreRed p ps = pointer (?bs ! l ! i)" "(k', pre, red) \<in> set (p # ps)"
        have "k' < l \<and> pre < length (?bs ! k') \<and> red < i"
        proof cases
          assume "k \<noteq> l"
          have "?bs!l!i = bs!l!i"
            by (simp add: \<open>k \<noteq> l\<close>)
          moreover have "l < length bs"
            using a0 by fastforce
          moreover have "i < length (bs!l)"
            using \<open>k \<noteq> l\<close> a1 by fastforce
          ultimately have "k' < l" "red < i" "pre < length (bs!k')"
            using a2 Cons.prems(1) unfolding valid_ptrs_def by metis+
          moreover have "length (?bs!k') = length (bs!k')"
            using Cons.prems(2,3) by (metis length_Cons nth_list_update_eq nth_list_update_neq)
          ultimately show ?thesis
            by simp
        next
          assume "\<not> k \<noteq> l"
          hence "k = l"
            by simp
          have "i \<noteq> 0 \<Longrightarrow> ?bs!l!i = bs!l!i"
            using Cons.prems(2,3) by (metis nth_Cons' nth_list_update_eq nth_list_update_neq)
          moreover have "l < length bs"
            using Cons.prems(3) \<open>k = l\<close> by auto
          moreover have "i < length (bs!l)"
            using Cons.prems(2,3) a1 by (metis list.size(4) nth_list_update)
          ultimately have "i \<noteq> 0 \<Longrightarrow> k' < l \<and> red < i \<and> pre < length (bs!k')"
            using a2 Cons.prems(1) unfolding valid_ptrs_def by metis
          have "i = 0 \<Longrightarrow> ?bs!l!i = Entry x (PreRed xp (yp # xs @ ys))"
            using Cons.prems(3) \<open>k = l\<close> by auto
          {
            assume "i = 0"
            have "bs!k!i = e'"
              by (metis Cons.prems(2) \<open>i = 0\<close> nth_Cons_0)
            moreover have "k < length bs"
              by (simp add: Cons.prems(3))
            moreover have "i < length (bs!k)"
              using \<open>k = l\<close> \<open>i < length (bs ! l)\<close> by auto
            ultimately have False
              using Cons.prems(1) \<open>i = 0\<close> ee'(2) unfolding valid_ptrs_def
              by (metis entry.sel(2) less_nat_zero_code list.set_intros(1) surj_pair)
            hence "k' < l \<and> red < i \<and> pre < length (?bs!k')"
              by blast
          }
          hence "i = 0 \<Longrightarrow> k' < l \<and> red < i \<and> pre < length (?bs!k')"
            by blast
          thus ?thesis
            using \<open>\<not> k \<noteq> l\<close> \<open>i \<noteq> 0 \<Longrightarrow> k' < l \<and> red < i \<and> pre < length (bs ! k')\<close> by fastforce
        qed
      }
      ultimately have "valid_ptrs ?bs"
        unfolding valid_ptrs_def by blast
      moreover have "bin_upd e (e' # es) = Entry x (PreRed xp (yp # xs @ ys)) # es"
        using ee' * by simp
      ultimately show ?thesis
        by simp
    next
      assume *: "\<not> x = y"
      let ?bs = "bs[k := es]"
      have "valid_ptrs ?bs"
        sorry

      thm Cons.IH

      thm bin_upd.simps

      show ?thesis
        sorry
    qed
  next
    case False
    then show ?thesis
    proof cases
      assume *: "item e = item e'"
      hence "bin_upd e (e' # es) = e' # es"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using Cons.prems(1,2) by auto
    next
      assume *: "\<not> item e = item e'"
      hence "bin_upd e (e' # es) = e' # bin_upd e es"
        using False by (auto split: pointer.splits entry.splits)
      thus ?thesis
        sorry
    qed
  qed
qed

lemma valid_ptrs_bin_upds: \<comment>\<open>TODO\<close>
  assumes "valid_ptrs bs" "b = bs!k" "k < length bs"
  assumes "(\<forall>e \<in> set es. \<forall>pre. Pre pre = pointer e \<longrightarrow> pre < length (bs!(k-1)))"
  assumes "(\<forall>e \<in> set es. \<forall>p ps k' pre red. PreRed p ps = pointer e \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow> k' < k \<and> pre < length (bs!k') \<and> red < length (bs!k))"
  shows "valid_ptrs (bs[k := bin_upds es b])"
  using assms
proof (induction es arbitrary: b bs)
  case (Cons e es)
  have 0: "valid_ptrs (bs[k := bin_upd e b])"
    using valid_ptrs_bin_upd[OF Cons.prems(1,2,3)] Cons.prems(4,5) by auto
  have 1: "bin_upd e b = (bs[k := bin_upd e b]) ! k"
    using Cons.prems(3) by simp
  have 2: "k < length (bs[k := bin_upd e b])"
    using Cons.prems(3) by simp
  have "valid_ptrs ((bs[k := bin_upd e b])[k := bin_upds es (bin_upd e b)])"
    using Cons.IH[OF 0 1 2] Cons.prems(4,5)
    by (smt (verit) "1" Cons.prems(2) dual_order.strict_trans1 insert_iff length_bin_upd list.set(2) nth_list_update_neq)
  thus ?case
    by simp
qed simp

lemma valid_ptrs_bins_upd: \<comment>\<open>TODO\<close>
  assumes "valid_ptrs bs" "k < length bs"
  assumes "(\<forall>e \<in> set xs. \<forall>pre. Pre pre = pointer e \<longrightarrow> pre < length (bs!(k-1)))"
  assumes "(\<forall>e \<in> set xs. \<forall>p ps k' pre red. PreRed p ps = pointer e \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow> k' < k \<and> pre < length (bs!k') \<and> red < length (bs!k))"
  shows "valid_ptrs (bins_upd bs k xs)"
  unfolding bins_upd_def using valid_ptrs_bin_upds[OF assms(1) _ assms(2,3,4)] by blast

lemma valid_ptrs_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "valid_ptrs bs" "sound_items cfg inp (bins_items bs)" "nonempty_derives cfg"
  shows "valid_ptrs (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by force
  hence "sound_items cfg inp (set (items (Complete_it k x bs i)))"
    using sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  hence sound: "sound_items cfg inp (bins_items ?bs')"
    using Complete.prems(1,3) bins_bins_upd sound_items_def wellformed_bins_elim UnE by metis
  {
    fix e
    assume a0: "e \<in> set (Complete_it k x bs i)"
    fix p ps k' pre red
    assume a1: "PreRed p ps = pointer e" "(k', pre, red) \<in> set (p#ps)"
    have "k' = item_origin x"
      using a0 a1 unfolding Complete_it_def by auto
    moreover have "wf_item cfg inp x" "item_end x = k"
      using Complete.prems(1) x wellformed_bins_elim wf_bins_kth_bin by blast+
    ultimately have 0: "k' \<le> k"
      using wf_defs(1) by blast
    have 1: "k' \<noteq> k"
    proof (rule ccontr)
      assume "\<not> k' \<noteq> k"
      have "sound_item cfg inp x"
        using Complete.prems(1,3) x sound_items_def kth_bin_sub_bins wellformed_bins_elim by (metis subset_eq)
      moreover have "is_complete x"
        using Complete.hyps(3) by (auto simp: next_symbol_def split: if_splits)
      moreover have "item_origin x = k"
        using \<open>\<not> k' \<noteq> k\<close> \<open>k' = item_origin x\<close> by auto
      ultimately show False
        using impossible_complete_item Complete.prems(1,4) wellformed_bins_elim \<open>item_end x = k\<close> \<open>wf_item cfg inp x\<close> by blast
    qed
    have 2: "pre < length (bs!k')"
      using a0 a1 index_filter_with_index_lt_length unfolding Complete_it_def by (auto simp: items_def; fastforce)
    have 3: "red < i+1"
      using a0 a1 unfolding Complete_it_def by auto
    have "k' < k" "pre < length (bs!k')" "red < i+1"
      using 0 1 2 3 by simp_all
  }
  hence "(\<forall>e \<in> set (Complete_it k x bs i). \<forall>p ps k' pre red. PreRed p ps = pointer e \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow> k' < k \<and> pre < length (bs!k') \<and> red < i+1)"
    by blast
  moreover have "k < length bs"
    using Complete.prems(1) wellformed_bins_elim by auto
  moreover have "(\<forall>e \<in> set (Complete_it k x bs i). \<forall>pre. Pre pre = pointer e \<longrightarrow> pre < length (bs!(k-1)))"
    unfolding Complete_it_def by auto
  ultimately have "valid_ptrs ?bs'"
    using valid_ptrs_bins_upd Complete.hyps(1) Complete.prems(2) by (auto simp: items_def; fastforce) 
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  ultimately have "valid_ptrs (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using Complete.IH Complete.prems(4) sound by blast
  thus ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by force
  hence "sound_items cfg inp (set (items (Scan_it k inp a x i)))"
    using sound_Scan_it \<pi>_mono Scan.hyps(3,5) Scan.prems(1,2,3) bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  hence sound: "sound_items cfg inp (bins_items ?bs')"
    using Scan.hyps(5) Scan.prems(1,3) bins_bins_upd sound_items_def wellformed_bins_elim UnE by (metis add_less_cancel_right)
  have "(\<forall>e \<in> set (Scan_it k inp a x i). \<forall>p ps k' pre red. PreRed p ps = pointer e \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow> k' < k+1 \<and> pre < length (bs!k') \<and> red < i+1)"
    unfolding Scan_it_def by simp
  moreover have "k+1 < length bs"
    using Scan.hyps(5) Scan.prems(1) wellformed_bins_elim by force
  moreover have "(\<forall>e \<in> set (Scan_it k inp a x i). \<forall>pre. Pre pre = pointer e \<longrightarrow> pre < length (bs!((k+1)-1)))"
    unfolding Scan_it_def using Scan.hyps(1) by (auto simp: items_def)
  ultimately have "valid_ptrs ?bs'"
    using valid_ptrs_bins_upd Scan.hyps(1) Scan.prems(2) by (auto simp: items_def Scan_it_def valid_ptrs_bins_upd)
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  ultimately have "valid_ptrs (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using Scan.IH Scan.prems(4) sound by blast
  thus ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by force
  hence "sound_items cfg inp (set (items(Predict_it k cfg a)))"
    using sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems bins_bin_exists wellformed_bins_elim
          sound_\<pi> wf_bins_kth_bin wf_items_def by metis
  hence sound: "sound_items cfg inp (bins_items ?bs')"
    using Predict.prems(1,3) bins_bins_upd sound_items_def wellformed_bins_elim by (metis UnE)
  have "(\<forall>e \<in> set (Predict_it k cfg a). \<forall>p ps k' pre red. PreRed p ps = pointer e \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow> k' < k \<and> pre < length (bs!k') \<and> red < i+1)"
    unfolding Predict_it_def by simp
  moreover have "k < length bs"
    using Predict.prems(1) wellformed_bins_elim by force
  moreover have "(\<forall>e \<in> set (Predict_it k cfg a). \<forall>pre. Pre pre = pointer e \<longrightarrow> pre < length (bs!(k-1)))"
    unfolding Predict_it_def by simp
  ultimately have "valid_ptrs ?bs'"
    using valid_ptrs_bins_upd Predict.hyps(1) Predict.prems(2) by (auto simp: items_def; fastforce)
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  ultimately have "valid_ptrs (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using Predict.IH Predict.prems(4) sound by blast
  thus ?case
    using Predict.hyps by simp
qed simp_all

lemma valid_ptrs_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "valid_ptrs bs" "sound_items cfg inp (bins_items bs)" "nonempty_derives cfg"
  shows "valid_ptrs (\<pi>_it k cfg inp bs)"
  using assms valid_ptrs_\<pi>_it' \<pi>_it_def by metis

lemma valid_ptrs_Init_it:
  "valid_ptrs (Init_it cfg inp)"
  unfolding valid_ptrs_def Init_it_def by (auto simp: less_Suc_eq_0_disj)

lemma valid_ptrs_\<I>_it:
  assumes "k \<le> length inp" "wf_cfg cfg" "nonempty_derives cfg"
  shows "valid_ptrs (\<I>_it k cfg inp)"
  using assms
proof (induction k)
  case 0
  have "(0, cfg, inp, (Init_it cfg inp)) \<in> wellformed_bins"
    using assms(2) wellformed_bins_Init_it by blast
  moreover have "sound_items cfg inp (bins_items (Init_it cfg inp))"
    by (simp add: Init_it_eq_Init sound_Init)
  ultimately show ?case
    using valid_ptrs_\<pi>_it valid_ptrs_Init_it "0.prems"(2,3) by fastforce
next
  case (Suc k)
  have "(Suc k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
    by (simp add: Suc.prems(1) Suc_leD assms(2) wellformed_bins_intro)
  moreover have "valid_ptrs (\<I>_it k cfg inp)"
    using Suc by simp
  moreover have "sound_items cfg inp (bins_items (\<I>_it k cfg inp))"
    using sound_\<I> \<I>_it_sub_\<I> Suc.prems(1,2) sound_items_def by (metis Suc_leD subsetD)
  ultimately show ?case
    using Suc.prems(3) valid_ptrs_\<pi>_it by auto
qed

lemma valid_ptrs_\<II>_it:
  assumes "wf_cfg cfg" "nonempty_derives cfg"
  shows "valid_ptrs (\<II>_it cfg inp)"
  using assms valid_ptrs_\<I>_it \<II>_it_def by (metis dual_order.refl)

lemma wf_ptrs_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "wf_bins cfg inp bs"
  shows "wf_ptrs inp (\<pi>_it' k cfg inp bs i)"
  sorry

lemma wf_ptrs_\<II>_it:
  "wf_ptrs inp (\<II>_it cfg inp)"
  sorry

lemma wf_item_dtree_build_dtree':
  assumes "wf_bins cfg inp bs"
  assumes "wf_ptrs inp bs"
  assumes "valid_ptrs bs" "k < length bs" "i < length (bs!k)"
  shows "wf_item_dtree cfg (item (bs!k!i)) (build_dtree' bs inp k i)"
  using assms
proof (induction bs inp k i rule: build_dtree'.induct)
  case (1 bs inp k i)
  let ?e = "bs!k!i"
  consider (Null) "pointer ?e = Null" | (Pre) "\<exists>pre. pointer ?e = Pre pre" | (PreRed) "\<exists>p ps. pointer ?e = PreRed p ps"
    by (meson PreRed pointer.exhaust)
  thus ?case
  proof cases
    case Null
    hence 0: "build_dtree' bs inp k i = Node (item_rule_head (item ?e)) []"
      by simp
    have "predicts (item ?e)"
      using Null "1.prems"(2,4,5) unfolding wf_ptrs_def by blast
    hence "item_dot (item ?e) = 0"
      unfolding predicts_def by blast
    thus ?thesis
      using 0 by simp
  next
    case Pre
    then obtain pre where pre: "pointer ?e = Pre pre"
      by blast
    obtain N ts where node: "build_dtree' bs inp (k-1) pre = Node N ts"
      by (meson ex_Node_build_tree')
    hence simp: "build_dtree' bs inp k i = Node N (ts @ [Leaf (inp!(k-1))])"
      using pre by simp
    have bounds: "pre < length (bs!(k-1))"
      using "1.prems"(3,4,5) pre unfolding valid_ptrs_def by metis
    have scans: "scans inp k (item (bs!(k-1)!pre)) (item (bs!k!i))"
      using "1.prems"(2,4,5) pre unfolding wf_ptrs_def by simp
    have IH: "wf_item_dtree cfg (item (bs!(k-1)!pre)) (build_dtree' bs inp (k-1) pre)"
      using "1.IH"(1) pre "1.prems"(1,2,3,4) bounds by simp
    have *: 
      "item_rule_head (item (bs!(k-1)!pre)) = item_rule_head (item (bs!k!i))"
      "item_rule_body (item (bs!(k-1)!pre)) = item_rule_body (item (bs!k!i))"
      "item_dot (item (bs!(k-1)!pre)) + 1 = item_dot (item (bs!k!i))"
      "next_symbol (item (bs!(k-1)!pre)) = Some (inp!(k-1))"
      using scans unfolding scans_def inc_item_def by (simp_all add: item_rule_head_def item_rule_body_def)
    have "map root_dtree (ts @ [Leaf (inp!(k-1))]) = map root_dtree ts @ [inp!(k-1)]"
      by simp
    also have "... = take (item_dot (item (bs!(k-1)!pre))) (item_rule_body (item (bs!(k-1)!pre))) @ [inp!(k-1)]"
      using IH node by simp
    also have "... = take (item_dot (item (bs!(k-1)!pre))) (item_rule_body (item (bs!k!i))) @ [inp!(k-1)]"
      using *(2) by simp
    also have "... = take (item_dot (item (bs!k!i))) (item_rule_body (item (bs!k!i)))"
      using *(2-4) by (auto simp: next_symbol_def is_complete_def split: if_splits; metis leI take_Suc_conv_app_nth)
    finally show ?thesis
      using *(1) IH node simp by simp
  next
    case PreRed
    then obtain k' pre red ps where prered: "pointer ?e = PreRed (k', pre, red) ps"
      by auto
    obtain N ts where node: "build_dtree' bs inp k' pre = Node N ts"
      by (meson ex_Node_build_tree')
    hence simp: "build_dtree' bs inp k i = Node N (ts @ [build_dtree' bs inp k red])"
      using prered by simp
    have bounds: "k' < k" "pre < length (bs ! k')" "red < i"
      using "1.prems"(3,4,5) prered unfolding valid_ptrs_def by (metis list.set_intros(1))+
    have completes: "completes k (item (bs!k'!pre)) (item (bs!k!i)) (item (bs!k!red))"
      using "1.prems"(2,4,5) prered unfolding wf_ptrs_def by (meson list.set_intros(1))
    have IH_pre: "wf_item_dtree cfg (item (bs!k'!pre)) (build_dtree' bs inp k' pre)"
      using "1.IH"(2) "1.prems"(1-4) bounds prered by simp
    have IH_red: "wf_item_dtree cfg (item (bs!k!red)) (build_dtree' bs inp k red)"
      using "1.IH"(3) "1.prems"(1-5) bounds prered node by simp
    have *: 
      "item_rule_head (item (bs!k'!pre)) = item_rule_head (item (bs!k!i))"
      "item_rule_body (item (bs!k'!pre)) = item_rule_body (item (bs!k!i))"
      "item_dot (item (bs!k'!pre)) + 1 = item_dot (item (bs!k!i))"
      "next_symbol (item (bs!k'!pre)) = Some (item_rule_head (item (bs!k!red)))"
      "is_complete (item (bs!k!red))"
      using completes unfolding completes_def inc_item_def
      by (auto simp: item_rule_head_def item_rule_body_def is_complete_def)
    have "map root_dtree (ts @ [build_dtree' bs inp k red]) = map root_dtree ts @ [root_dtree (build_dtree' bs inp k red)]"
      by simp
    also have "... = take (item_dot (item (bs!k'!pre))) (item_rule_body (item (bs!k'!pre))) @ [root_dtree (build_dtree' bs inp k red)]"
      using IH_pre node by force
    also have "... = take (item_dot (item (bs!k'!pre))) (item_rule_body (item (bs!k'!pre))) @ [item_rule_head (item (bs!k!red))]"
      using IH_red ex_Node_build_tree' by (metis root_dtree.simps(2) wf_item_dtree.simps(2))
    also have "... = take (item_dot (item (bs!k!i))) (item_rule_body (item (bs!k!i)))"
      using * by (auto simp: next_symbol_def is_complete_def split: if_splits; metis leI take_Suc_conv_app_nth)
    finally have 0: "map root_dtree (ts @ [build_dtree' bs inp k red]) = take (item_dot (item (bs!k!i))) (item_rule_body (item (bs!k!i)))" .
    have wf: "wf_item cfg inp (item (bs!k!red))"
      using "1.prems"(1,4,5) bounds(3) unfolding wf_bins_def wf_bin_def wf_bin_items_def by (simp add: items_def)
    obtain N' ts' where node': "build_dtree' bs inp k red = Node N' ts'"
      by (meson ex_Node_build_tree')
    hence "N' = item_rule_head (item (bs!k!red))"
          "map root_dtree ts' = item_rule_body (item (bs!k!red))"
      using IH_red *(5) by (auto simp: is_complete_def)
    hence "\<exists>r \<in> set (\<RR> cfg). N' = rule_head r \<and> map root_dtree ts' = rule_body r"
      using wf unfolding wf_item_def item_rule_body_def item_rule_head_def by auto
    hence 1: "wf_rule_dtree cfg (build_dtree' bs inp k red)"
      using IH_red node' by simp
    show ?thesis
      using *(1) 0 1 IH_pre node simp by simp
  qed
qed

lemma wf_yield_dtree_build_dtree':
  assumes "wf_bins cfg inp bs"
  assumes "wf_ptrs inp bs"
  assumes "valid_ptrs bs" "k < length bs" "i < length (bs!k)" "k \<le> length inp"
  shows "wf_yield_dtree inp (item (bs!k!i)) (build_dtree' bs inp k i)"
  using assms
proof (induction bs inp k i rule: build_dtree'.induct)
  case (1 bs inp k i)
  let ?e = "bs!k!i"
  consider (Null) "pointer ?e = Null" | (Pre) "\<exists>pre. pointer ?e = Pre pre" | (PreRed) "\<exists>p ps. pointer ?e = PreRed p ps"
    by (meson PreRed pointer.exhaust)
  thus ?case
  proof cases
    case Null
    hence simp: "build_dtree' bs inp k i = Node (item_rule_head (item ?e)) []"
      by simp
    have "predicts (item ?e)"
      using Null "1.prems"(2,4,5) unfolding wf_ptrs_def by blast
    hence "item_origin (item ?e) = item_end (item ?e)"
      unfolding predicts_def by blast
    thus ?thesis
      unfolding wf_yield_dtree_def using simp by (simp add: slice_empty)
  next
    case Pre
    then obtain pre where pre: "pointer ?e = Pre pre"
      by blast
    obtain N ts where node: "build_dtree' bs inp (k-1) pre = Node N ts"
      by (meson ex_Node_build_tree')
    hence simp: "build_dtree' bs inp k i = Node N (ts @ [Leaf (inp!(k-1))])"
      using pre by simp
    have bounds: "pre < length (bs!(k-1))"
      using "1.prems"(3,4,5) pre unfolding valid_ptrs_def by metis
    have scans: "scans inp k (item (bs!(k-1)!pre)) (item (bs!k!i))"
      using "1.prems"(2,4,5) pre unfolding wf_ptrs_def by simp
    have IH: "wf_yield_dtree inp (item (bs!(k-1)!pre)) (build_dtree' bs inp (k-1) pre)"
      using "1.IH"(1) pre "1.prems"(1,2,3,4,6) bounds by simp
    have wf: 
      "item_origin (item (bs!(k-1)!pre)) \<le> item_end (item (bs!(k-1)!pre))"
      "item_end (item (bs!(k-1)!pre)) = k-1"
      "item_end (item (bs!k!i)) = k"
      using "1.prems"(1,4,5) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def wf_item_def
      by (auto, meson less_imp_diff_less nth_mem)
    have "yield_dtree (build_dtree' bs inp k i) = concat (map yield_dtree (ts @ [Leaf (inp!(k-1))]))"
      using simp by simp
    also have "... = concat (map yield_dtree ts) @ [inp!(k-1)]"
      by simp
    also have "... = slice (item_origin (item (bs!(k-1)!pre))) (item_end (item (bs!(k-1)!pre))) inp @ [inp!(k-1)]"
      using node IH by (simp add: wf_yield_dtree_def)
    also have "... = slice (item_origin (item (bs!(k-1)!pre))) (item_end (item (bs!(k-1)!pre)) + 1) inp"
      using slice_append_nth wf "1.prems"(6) by (metis One_nat_def Suc_pred leD not_less_eq scans scans_def)
    also have "... = slice (item_origin (item ?e)) (item_end (item (bs!(k-1)!pre)) + 1) inp"
      using scans unfolding scans_def inc_item_def by simp
    also have "... = slice (item_origin (item ?e)) k inp"
      using scans wf unfolding scans_def by simp
    also have "... = slice (item_origin (item ?e)) (item_end (item ?e)) inp"
      using wf by auto
    finally show ?thesis
      using wf_yield_dtree_def by blast
  next
    case PreRed
    then obtain k' pre red ps where prered: "pointer ?e = PreRed (k', pre, red) ps"
      by auto
    obtain N ts where node: "build_dtree' bs inp k' pre = Node N ts"
      by (meson ex_Node_build_tree')
    hence simp: "build_dtree' bs inp k i = Node N (ts @ [build_dtree' bs inp k red])"
      using prered by simp
    have bounds: "k' < k" "pre < length (bs ! k')" "red < i"
      using "1.prems"(3,4,5) prered unfolding valid_ptrs_def by (metis list.set_intros(1))+
    have completes: "completes k (item (bs!k'!pre)) (item (bs!k!i)) (item (bs!k!red))"
      using "1.prems"(2,4,5) prered unfolding wf_ptrs_def by (meson list.set_intros(1))
    have IH_pre: "wf_yield_dtree inp (item (bs!k'!pre)) (build_dtree' bs inp k' pre)"
      using "1.IH"(2) "1.prems"(1-4,6) bounds prered by simp
    have IH_red: "wf_yield_dtree inp (item (bs!k!red)) (build_dtree' bs inp k red)"
      using "1.IH"(3) "1.prems"(1-6) bounds prered node by simp
    have wf1: 
      "item_origin (item (bs!k'!pre)) \<le> item_end (item (bs!k'!pre))"
      "item_origin (item (bs!k!red)) \<le> item_end (item (bs!k!red))"
      using "1.prems"(1,4,5) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def wf_item_def
      by (metis length_map nth_map nth_mem order_less_trans)+
    have wf2:
      "item_end (item (bs!k!red)) = k"
      "item_end (item (bs!k!i)) = k"
      using "1.prems"(1,4,5) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def by simp_all
    have "yield_dtree (build_dtree' bs inp k i) = concat (map yield_dtree (ts @ [build_dtree' bs inp k red]))"
      using simp by simp
    also have "... = concat (map yield_dtree ts) @ yield_dtree (build_dtree' bs inp k red)"
      by simp
    also have "... = slice (item_origin (item (bs!k'!pre))) (item_end (item (bs!k'!pre))) inp @ 
      slice (item_origin (item (bs!k!red))) (item_end (item (bs!k!red))) inp"
      using IH_pre IH_red by (simp add: node wf_yield_dtree_def)
    also have "... = slice (item_origin (item (bs!k'!pre))) (item_end (item (bs!k!red))) inp"
      using slice_concat wf1 completes_def completes by (metis (no_types, lifting))
    also have "... = slice (item_origin (item ?e)) (item_end (item (bs!k!red))) inp"
      using completes unfolding completes_def inc_item_def by simp
    also have "... = slice (item_origin (item ?e)) (item_end (item ?e)) inp"
      using wf2 by simp
    finally show ?thesis
      using wf_yield_dtree_def by blast
  qed
qed

theorem build_dtree_Some_wf_rule_dtree:
  assumes "wf_bins cfg inp bs" "wf_ptrs inp bs" "valid_ptrs bs" "length bs = length inp + 1"
  assumes "Some t = build_dtree cfg inp bs"
  shows "wf_rule_dtree cfg t \<and> root_dtree t = \<SS> cfg \<and> yield_dtree t = inp"
proof -
  let ?k = "length bs - 1"
  obtain x i xs where *: "filter_with_index (is_finished cfg inp) (items (bs!?k)) = (x,i)#xs"
    using assms(5) unfolding build_dtree_def by (auto simp: Let_def split: list.splits)
  have k: "?k < length bs" "?k \<le> length inp"
    using assms(4) by simp_all
  have i: "i < length (bs ! ?k)"
    using index_filter_with_index_lt_length * items_def by (metis length_map list.set_intros(1))
  have x: "x = item (bs!?k!i)"
    using * i filter_with_index_nth items_def nth_map by (metis list.set_intros(1))
  have finished: "is_finished cfg inp x"
    using * filter_with_index_P by (metis list.set_intros(1))
  hence wf_item_rule: "wf_item_dtree cfg x (build_dtree' bs inp ?k i)"
    using wf_item_dtree_build_dtree'[OF assms(1-3) k(1) i] x by blast
  have wf_item: "wf_item cfg inp (item (bs!?k!i))"
    using k(1) i assms(1) unfolding wf_bins_def wf_bin_def wf_bin_items_def by (simp add: items_def)
  obtain N ts where node: "build_dtree' bs inp ?k i = Node N ts"
    by (meson ex_Node_build_tree')
  hence "N = item_rule_head x"
    "map root_dtree ts = item_rule_body x"
    using finished wf_item_rule by (auto simp: is_finished_def is_complete_def)
  hence "\<exists>r \<in> set (\<RR> cfg). N = rule_head r \<and> map root_dtree ts = rule_body r"
    using wf_item x unfolding wf_item_def item_rule_body_def item_rule_head_def by blast
  hence wf_rule: "wf_rule_dtree cfg (build_dtree' bs inp ?k i)"
    using wf_item_rule node by simp
  have root: "root_dtree (build_dtree' bs inp ?k i) = \<SS> cfg"
    using finished node \<open>N = item_rule_head x\<close> by (auto simp: is_finished_def)
  have "yield_dtree (build_dtree' bs inp ?k i) = slice (item_origin (item (bs!?k!i))) (item_end (item (bs!?k!i))) inp"
    using k i assms(1,2,3) wf_yield_dtree_build_dtree' wf_yield_dtree_def by blast
  hence yield: "yield_dtree (build_dtree' bs inp ?k i) = inp"
    using finished x unfolding is_finished_def by simp
  show ?thesis
    using * wf_rule root yield assms(5) unfolding build_dtree_def by simp
qed

corollary build_dtree_Some_wf_rule_dtree_\<II>_it:
  assumes "wf_cfg cfg" "nonempty_derives cfg" "Some t = build_dtree cfg inp (\<II>_it cfg inp)"
  shows "wf_rule_dtree cfg t \<and> root_dtree t = \<SS> cfg \<and> yield_dtree t = inp"
  using assms build_dtree_Some_wf_rule_dtree wf_bins_\<II>_it valid_ptrs_\<II>_it wf_ptrs_\<II>_it \<II>_it_def
    length_\<I>_it length_bins_Init_it by (metis nle_le)

theorem build_dtree_Some_\<II>_it:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "(\<exists>t. Some t = build_dtree cfg inp (\<II>_it cfg inp)) \<longleftrightarrow> derives cfg [\<SS> cfg] inp" (is "?L \<longleftrightarrow> ?R")
proof standard
  assume *: ?L
  let ?k = "length (\<II>_it cfg inp) - 1"
  obtain t where "Some t = build_dtree cfg inp (\<II>_it cfg inp)"
    using * by blast
  then obtain x i xs where *: "filter_with_index (is_finished cfg inp) (items ((\<II>_it cfg inp)!?k)) = (x,i)#xs"
    unfolding build_dtree_def by (auto simp: Let_def split: list.splits)
  have k: "?k < length (\<II>_it cfg inp)" "?k \<le> length inp"
    by (simp_all add: \<II>_it_def assms(1))
  have i: "i < length ((\<II>_it cfg inp) ! ?k)"
    using index_filter_with_index_lt_length * items_def by (metis length_map list.set_intros(1))
  have x: "x = item ((\<II>_it cfg inp)!?k!i)"
    using * i filter_with_index_nth items_def nth_map by (metis list.set_intros(1))
  have finished: "is_finished cfg inp x"
    using * filter_with_index_P by (metis list.set_intros(1))
  moreover have "x \<in> set (items ((\<II>_it cfg inp) ! ?k))"
    using x by (auto simp: items_def; metis One_nat_def i imageI nth_mem)
  ultimately have "(\<exists>x \<in> set (items ((\<II>_it cfg inp) ! length inp)). is_finished cfg inp x)"
    by (metis assms(1) is_finished_def k(1) wf_bins_\<II>_it wf_bins_kth_bin)    
  hence "earley_recognized_it (\<II>_it cfg inp) cfg inp"
    using earley_recognized_it_def by blast
  thus ?R
    using correctness_list assms by blast
next
  assume ?R
  hence "earley_recognized_it (\<II>_it cfg inp) cfg inp"
    using assms(1) assms(2) assms(3) correctness_list by blast
  hence "(\<exists>x\<in>set (items ((\<II>_it cfg inp) ! length inp)). is_finished cfg inp x)"
    using earley_recognized_it_def by blast
  hence "(\<exists>x\<in>set (items ((\<II>_it cfg inp) ! (length (\<II>_it cfg inp) - 1))). is_finished cfg inp x)"
    by (simp add: \<II>_it_def assms(1))
  hence "\<exists>x i xs. filter_with_index (is_finished cfg inp) (items ((\<II>_it cfg inp)! (length (\<II>_it cfg inp) - 1))) = (x,i)#xs"
    using filter_with_index_cong_filter list.exhaust list.simps(8) prod.collapse by (metis empty_filter_conv)
  thus ?L
    by (auto simp: build_dtree_def)
qed

end

theory Earley_List
  imports 
    Earley_Set
    (* "HOL-Library.While_Combinator" \<comment>\<open>TODO: Use?\<close> *)
begin

subsection \<open>Bins\<close>

datatype bin = Bin (items: "item list")

datatype bins = Bins (bins: "bin list")

definition set_bin_upto :: "bin \<Rightarrow> nat \<Rightarrow> items" where
  "set_bin_upto b i = { items b ! j | j. j < i \<and> j < length (items b) }"

definition set_bin :: "bin \<Rightarrow> items" where
  "set_bin b = set (items b)"

definition set_bins_upto :: "bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> items" where
  "set_bins_upto bs k i = \<Union> { set_bin (bins bs ! l) | l. l < k } \<union> set_bin_upto (bins bs ! k) i"

definition set_bins :: "bins \<Rightarrow> items" where
  "set_bins bs = \<Union> { set_bin (bins bs ! k) | k. k < length (bins bs) }"

definition app_bin :: "bin \<Rightarrow> item list \<Rightarrow> bin" where
  "app_bin b is = Bin (items b @ (filter (\<lambda>i. i \<notin> set (items b)) is))"

definition app_bins :: "bins \<Rightarrow> nat \<Rightarrow> item list \<Rightarrow> bins" where
  "app_bins bs k is = Bins ((bins bs)[k := app_bin ((bins bs)!k) is])"

locale Earley_List = Earley_Set +
  fixes rules :: "rule list"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
  assumes nonempty_deriv: "N \<in> \<NN> \<Longrightarrow> \<not> derives [N] []"
begin

subsection \<open>Earley algorithm\<close>

definition Init_it :: "bins" where
  "Init_it = (
    let rs = filter (\<lambda>r. rule_head r = \<SS>) rules in
    let b0 = map (\<lambda>r. init_item r 0) rs in
    let bs = replicate (length inp + 1) (Bin []) in
    app_bins (Bins bs) 0 b0)"

definition Scan_it :: "nat \<Rightarrow> symbol \<Rightarrow> item \<Rightarrow> item list" where
  "Scan_it k a x = (
    if k < length inp \<and> inp!k = a then
      let x' = inc_item x (k+1) in
      [x']
    else [])"

definition Predict_it :: "nat \<Rightarrow> symbol \<Rightarrow> item list" where
  "Predict_it k X = (
    let rs = filter (\<lambda>r. rule_head r = X) rules in
    map (\<lambda>r. init_item r k) rs)"

definition Complete_it :: "nat \<Rightarrow> item \<Rightarrow> bins \<Rightarrow> item list" where
  "Complete_it k y bs = (
    let orig = (bins bs)!(item_origin y) in
    let is = filter (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items orig) in
    map (\<lambda>x. inc_item x k) is)"

function \<pi>_it' :: "nat \<Rightarrow> bins \<Rightarrow> nat \<Rightarrow> bins" where
  "\<pi>_it' k bs i = (
    if i \<ge> length (items (bins bs ! k)) then bs
    else
      let x = items (bins bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow>
            if is_terminal a then
              if k < length inp then app_bins bs (k+1) (Scan_it k a x)
              else bs
            else app_bins bs k (Predict_it k a)
        | None \<Rightarrow> app_bins bs k (Complete_it k x bs)
      in \<pi>_it' k bs' (i+1))"
  by pat_completeness simp
termination
  sorry
(* while_option :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option"
   while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" *)

definition \<pi>_it :: "nat \<Rightarrow> bins \<Rightarrow> bins" where
  "\<pi>_it k bs = \<pi>_it' k bs 0"

fun \<I>_it :: "nat \<Rightarrow> bins" where
  "\<I>_it 0 = \<pi>_it 0 Init_it"
| "\<I>_it (Suc n) = \<pi>_it (Suc n) (\<I>_it n)"

definition \<II>_it :: "bins" where
  "\<II>_it = \<I>_it (length inp)"

subsubsection \<open>Alternate \<pi>_it' simps and induction rule\<close>

lemma \<pi>_it'_simps[simp]:
  "length (items (bins bs ! k)) \<le> i \<Longrightarrow> \<pi>_it' k bs i = bs"
  "\<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = None \<Longrightarrow> 
    \<pi>_it' k bs i = \<pi>_it' k (app_bins bs k (Complete_it k x bs)) (i+1)"
  "\<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    is_terminal a \<Longrightarrow> k < length inp \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k (app_bins bs (k+1) (Scan_it k a x)) (i+1)"
  "\<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    is_terminal a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
  "\<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    \<not> is_terminal a \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k (app_bins bs k (Predict_it k a)) (i+1)"
  by (simp_all, simp_all add: Let_def)

lemma \<pi>_it'_induct[case_names Base Complete Scan Pass Predict]:
  assumes base: "\<And>k bs i. length (items (bins bs ! k)) \<le> i \<Longrightarrow> P k bs i"
  assumes complete: "\<And>k bs i x. \<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = None \<Longrightarrow> (\<And>xa. xa = app_bins bs k (Complete_it k x bs) \<Longrightarrow> P k xa (i+1)) \<Longrightarrow> P k bs i"
  assumes scan: "\<And>k bs i x a. \<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal a \<Longrightarrow> k < length inp \<Longrightarrow> 
            (\<And>xa. xa = app_bins bs (k+1) (Scan_it k a x) \<Longrightarrow> P k xa (i+1)) \<Longrightarrow> P k bs i"
  assumes pass: "\<And>k bs i x a. \<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> P k bs (i+1) \<Longrightarrow> P k bs i"
  assumes predict: "\<And>k bs i x a. \<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> \<not> is_terminal a \<Longrightarrow> 
            (\<And>xa. xa = app_bins bs k (Predict_it k a) \<Longrightarrow> P k xa (i+1)) \<Longrightarrow> P k bs i"
  shows "P k bs i"
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume "length (items (bins bs ! k)) \<le> i"
    thus ?thesis
      using base by blast
  next
    assume a1: "\<not> length (items (bins bs ! k)) \<le> i"
    let ?x = "items (bins bs ! k) ! i"
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      show ?thesis
        using 1 a1 a2 complete by simp
    next
      assume a2: "\<not> next_symbol ?x = None"
      then obtain a where a_def: "next_symbol ?x = Some a"
        by blast
      show ?thesis
      proof cases
        assume a3: "is_terminal a"
        show ?thesis
        proof cases
          assume a4: "k < length inp"
          show ?thesis
            using 1 a1 a3 a4 a_def scan by simp
        next
          assume a4: "\<not> k < length inp"
          show ?thesis
            using 1 a1 a3 a4 a_def pass by simp
        qed
      next
        assume a3: "\<not> is_terminal a"
        show ?thesis
          using 1 a1 a3 a_def predict by simp
      qed
    qed
  qed
qed

declare \<pi>_it'.simps[simp del]

subsection \<open>Bin lemmas\<close>

lemma length_bins_app_bins[simp]:
  "length (bins (app_bins bs k is)) = length (bins bs)"
  unfolding app_bins_def by simp

lemma length_nth_bin_app_bins:
  "length (items (bins (app_bins bs k is) ! l)) \<ge> length (items (bins bs ! l))"
  by (cases "k < length (bins bs)") (auto simp: nth_list_update app_bins_def app_bin_def)

lemma length_nth_bin_app_bins_eq:
  "k \<noteq> l \<Longrightarrow> length (items (bins (app_bins bs k is) ! l)) = length (items (bins bs ! l))"
  by (cases "k < length (bins bs)") (auto simp: app_bins_def app_bin_def)

lemma length_bins_Init_it[simp]:
  "length (bins Init_it) = length inp + 1"
  unfolding Init_it_def using length_bins_app_bins by force

lemma length_bins_\<pi>_it'[simp]:
  "length (bins (\<pi>_it' k bs i)) = length (bins bs)"
  by (induction k bs i rule: \<pi>_it'_induct) auto

lemma length_bins_\<pi>_it[simp]:
  "length (bins (\<pi>_it k bs)) = length (bins bs)"
  unfolding \<pi>_it_def by simp

lemma length_nth_bin_\<pi>_it':
  "length (items (bins (\<pi>_it' k bs i) ! l)) \<ge> length (items (bins bs ! l))"
  using length_nth_bin_app_bins order_trans
  by (induction k bs i rule: \<pi>_it'_induct) (auto, blast+)

lemma length_bins_\<I>_it[simp]:
  "length (bins (\<I>_it k)) = length (bins Init_it)"
  by (induction k) auto

declare set_bin_def[simp]

lemma app_bins_eq:
  "set is \<subseteq> set_bin (bins bs ! k) \<Longrightarrow> app_bins bs k is = bs"
  using filter_False unfolding app_bins_def app_bin_def by (auto simp: in_mono)

lemma nth_app_bin:
  "i < length (items b) \<Longrightarrow> items (app_bin b is) ! i = items b ! i"
  unfolding app_bin_def by (simp add: nth_append)

lemma nth_app_bins:
  "k \<noteq> l \<Longrightarrow> bins (app_bins bs k is) ! l = bins bs ! l"
  unfolding app_bins_def nth_app_bin by simp

lemma kth_app_bins:
  assumes "i < length (items (bins bs ! k))"
  shows "items (bins (app_bins bs k is) ! k) ! i = items (bins bs ! k) ! i"
  by (cases "k < length (bins bs)") (auto simp: app_bins_def nth_app_bin assms)

lemma kth_\<pi>_it'_bins:
  assumes "j < length (items (bins bs ! l))"
  shows "items (bins (\<pi>_it' k bs i) ! l) ! j = items (bins bs ! l) ! j"
  using assms length_nth_bin_app_bins nth_app_bins kth_app_bins length_bins_app_bins
  by (induction k bs i rule: \<pi>_it'_induct) (auto simp: less_le_trans, metis+)

lemma nth_bin_sub_\<pi>_it':
  assumes "k < length (bins bs)" "l < length (bins bs)"
  shows "set_bin (bins bs ! l) \<subseteq> set_bin (bins (\<pi>_it' k bs i) ! l)"
proof standard
  fix x
  assume "x \<in> set_bin (bins bs ! l)"
  then obtain j where *: "j < length (items (bins bs ! l))" "items (bins bs ! l) ! j = x"
    using set_bin_def in_set_conv_nth by metis
  have "x = items (bins (\<pi>_it' k bs i) ! l) ! j"
    using kth_\<pi>_it'_bins assms * by simp
  moreover have "j < length (items (bins (\<pi>_it' k bs i) ! l))"
    using assms *(1) length_nth_bin_\<pi>_it' less_le_trans by blast
  ultimately show "x \<in> set_bin (bins (\<pi>_it' k bs i) ! l)"
    by simp
qed

lemma set_bin_\<pi>_it'_eq:
  "l < k \<Longrightarrow> set_bin (bins (\<pi>_it' k bs i) ! l) = set_bin (bins bs ! l)"
  by (induction k bs i rule: \<pi>_it'_induct) (auto simp: app_bins_def nth_app_bins)

lemma set_bin_upto_eq_set_bin:
  "i \<ge> length (items b) \<Longrightarrow> set_bin_upto b i = set_bin b"
  unfolding set_bin_upto_def set_bin_def by (auto, metis in_set_conv_nth less_le_trans)

lemma set_bins_upto_k0_\<pi>_it'_eq:
  "k < length (bins bs) \<Longrightarrow> set_bins_upto (\<pi>_it k bs) k 0 = set_bins_upto bs k 0"
  unfolding set_bins_upto_def set_bin_upto_def \<pi>_it_def using set_bin_\<pi>_it'_eq by auto

lemma set_bins_upto_empty:
  "set_bins_upto bs 0 0 = {}"
  unfolding set_bins_upto_def set_bin_upto_def by simp

lemma set_bin_app_bin[simp]:
  "set_bin (app_bin b is) = set_bin b \<union> set is"
  unfolding app_bin_def by auto

lemma set_bins_app_bins:
  "k < length (bins bs) \<Longrightarrow> set_bins (app_bins bs k is) = set_bins bs \<union> set is"
  unfolding set_bins_def app_bins_def using set_bin_app_bin
  by (auto, metis bins.sel Un_iff app_bins_def nth_app_bins nth_list_update_eq)+

lemma kth_bin_in_bins:
  "k < length (bins bs) \<Longrightarrow> set_bin (bins bs ! k) \<subseteq> set_bins bs"
  unfolding set_bins_def set_bins_upto_def set_bin_upto_def by blast

lemma set_bins_upto_kth_nth_id:
  assumes "l < length (bins bs)" "k \<le> l" "i < length (items (bins bs ! k))"
  shows "set_bins_upto (app_bins bs l is) k i = set_bins_upto bs k i"
  unfolding set_bins_upto_def set_bin_def set_bin_upto_def app_bins_def app_bin_def
  using assms by (auto simp: nth_append nth_list_update, metis not_less)

lemma set_bins_upto_sub_set_bins:
  "k < length (bins bs) \<Longrightarrow> set_bins_upto bs k i \<subseteq> set_bins bs"
  unfolding set_bins_def set_bins_upto_def set_bin_upto_def using less_trans by (auto, blast)

lemma set_bins_upto_Suc_Un:
  "i < length (items (bins bs ! k)) \<Longrightarrow> set_bins_upto bs k (i+1) = set_bins_upto bs k i \<union> { items (bins bs ! k) ! i }"
  unfolding set_bins_upto_def set_bin_upto_def using less_Suc_eq by auto

lemma set_bins_upto_Suc_eq:
  "i \<ge> length (items (bins bs ! k)) \<Longrightarrow> set_bins_upto bs k (i+1) = set_bins_upto bs k i"
  unfolding set_bins_upto_def set_bin_upto_def by auto

lemma set_bins_bin_exists:
  "x \<in> set_bins bs \<Longrightarrow> \<exists>k < length (bins bs). x \<in> set_bin (bins bs ! k)"
  unfolding set_bins_def by blast

lemma distinct_app_bin:
  "distinct (items b) \<Longrightarrow> distinct is \<Longrightarrow> distinct (items (app_bin b is))"
  unfolding app_bin_def by auto

subsection \<open>Wellformed Bins\<close>

definition wf_bin :: "nat \<Rightarrow> bin \<Rightarrow> bool" where
  "wf_bin k b \<longleftrightarrow> distinct (items b) \<and> (\<forall>x \<in> set (items b). wf_item x \<and> item_end x = k)"

definition wf_bins :: "bins \<Rightarrow> bool" where
  "wf_bins bs \<longleftrightarrow> (\<forall>k < length (bins bs). wf_bin k (bins bs ! k))"

lemma wf_bins_impl_wf_items:
  "wf_bins bs \<Longrightarrow> wf_items (set_bins bs)"
  unfolding wf_bins_def wf_bin_def wf_items_def set_bins_def by auto

lemma wf_bins_app_bins:
  "wf_bins bs \<Longrightarrow> distinct xs \<Longrightarrow> \<forall>x \<in> set xs. wf_item x \<and> item_end x = k \<Longrightarrow> wf_bins (app_bins bs k xs)"
  unfolding wf_bins_def wf_bin_def app_bins_def using set_bin_app_bin distinct_app_bin
  by (cases "k < length (bins bs)") (auto simp: nth_list_update)

lemma wf_bins_kth_bin:
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> x \<in> set_bin (bins bs ! k) \<Longrightarrow> wf_item x \<and> item_end x = k"
  using set_bin_def wf_bin_def wf_bins_def by blast

lemma wf_bins_Init_it:
  "wf_bins Init_it"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS>) rules"
  let ?b0 = "Bin (map (\<lambda>r. init_item r 0) ?rs)"
  let ?bs = "replicate (length inp + 1) (Bin [])"
  have "wf_bin 0 ?b0"
    unfolding wf_bin_def wf_item_def using valid_rules by (auto simp: init_item_def distinct_map inj_on_def)
  moreover have "wf_bins (Bins ?bs)"
    unfolding wf_bins_def wf_bin_def using less_Suc_eq_0_disj by force
  ultimately show ?thesis
    using wf_bins_app_bins unfolding wf_bin_def by (simp add: Init_it_def)
qed

lemma distinct_Scan_it:
  "distinct (Scan_it k a x)"
  unfolding Scan_it_def by simp

lemma distinct_Predict_it:
  "distinct (Predict_it k X)"
  unfolding Predict_it_def using valid_rules by (auto simp: init_item_def rule_head_def distinct_map inj_on_def)

lemma distinct_Complete_it:
  "wf_bins bs \<Longrightarrow> item_origin y < length (bins bs) \<Longrightarrow> distinct (Complete_it k y bs)"
  unfolding Complete_it_def wf_bins_def wf_bin_def by (auto simp: distinct_map inj_on_def inc_item_def item.expand)

lemma wf_bins_Scan_it':
  assumes "wf_bins bs" "k < length (bins bs)" "x \<in> set_bin (bins bs ! k)"
  assumes "k < length inp" "next_symbol x \<noteq> None" "y = inc_item x (k+1)"
  shows "wf_item y \<and> item_end y = k+1"
  using assms wf_bins_kth_bin[OF assms(1-3)]
  unfolding wf_item_def inc_item_def next_symbol_def is_complete_def item_rule_body_def
  by (auto split: if_splits)

lemma wf_bins_Scan_it:
  assumes "wf_bins bs" "k < length (bins bs)" "x \<in> set_bin (bins bs ! k)"
  assumes "k \<le> length inp" "next_symbol x \<noteq> None"
  shows "\<forall>y \<in> set (Scan_it k a x). wf_item y \<and> item_end y = (k+1)" 
  using wf_bins_Scan_it'[OF assms(1-3) _ assms(5)] 
  by (metis List.list.set(1,2) Scan_it_def empty_iff insert_iff)

lemma wf_bins_Predict_it:
  assumes "wf_bins bs" "k < length (bins bs)" "k \<le> length inp"
  shows "\<forall>y \<in> set (Predict_it k X). wf_item y \<and> item_end y = k"
  using assms by (auto simp: Predict_it_def wf_item_def wf_bins_def wf_bin_def init_item_def valid_rules)

lemma wf_bins_Complete_it:
  assumes "wf_bins bs" "k < length (bins bs)" "y \<in> set_bin (bins bs ! k)"
  shows "\<forall>x \<in> set (Complete_it k y bs). wf_item x \<and> item_end x = k"
  using assms wf_bins_kth_bin[OF assms]
  unfolding Complete_it_def wf_bins_def wf_bin_def wf_item_def inc_item_def next_symbol_def
            is_complete_def item_rule_body_def
  by (auto, metis le_less_trans, metis le_less_trans le_trans)

lemma wf_bins_\<pi>_it':
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> k \<le> length inp \<Longrightarrow> wf_bins (\<pi>_it' k bs i)"
  sorry
(*
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof (cases "\<not> length (items (bins bs ! k)) \<le> i")
    case True
    let ?x = "items (bins bs ! k) ! i"
    have "?x \<in> set_bin (bins bs ! k)"
      using True by simp
    thus ?thesis
      using True 1 wf_bins_Scan_it wf_bins_Predict_it wf_bins_Complete_it
            wf_bins_app_bins
      apply (auto simp: \<pi>_it'.simps Let_def simp del: set_bin_def split: option.split)
      sledgehammer
  qed (auto simp: "1.prems"(1))
qed
*)

lemma wf_bins_\<pi>_it:
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> k \<le> length inp \<Longrightarrow> wf_bins (\<pi>_it k bs)"
  using \<pi>_it_def wf_bins_\<pi>_it' by presburger

lemma wf_bins_\<I>_it:
  "k \<le> length inp \<Longrightarrow> wf_bins (\<I>_it k)"
  by (induction k) (auto simp: wf_bins_Init_it wf_bins_\<pi>_it)

lemma wf_bins_\<II>_it:
  "wf_bins \<II>_it"
  unfolding \<II>_it_def using wf_bins_\<I>_it length_bins_Init_it by auto

subsection \<open>List to Set\<close>

lemma Init_it_eq_Init:
  "set_bins Init_it = Init"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS>) rules"
  let ?b0 = "map (\<lambda>r. init_item r 0) ?rs"
  let ?bs = "Bins (replicate (length inp + 1) (Bin []))"
  have "set_bins ?bs = {}"
    unfolding set_bins_def set_bins_upto_def set_bin_def set_bin_upto_def
    by (auto simp del: replicate_Suc)
  hence "set_bins Init_it = set ?b0"
    using Init_it_def set_bins_app_bins by simp
  thus ?thesis
    unfolding Init_def rule_head_def using valid_rules by auto
qed

lemma Scan_it_sub_Scan:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some a"
  shows "set (Scan_it k a x) \<subseteq> Scan k I"
proof standard
  fix y
  assume *: "y \<in> set (Scan_it k a x)"
  have "x \<in> bin I k"
    using kth_bin_in_bins assms(1-4) set_bin_def wf_bin_def wf_bins_def bin_def by blast
  {
    assume #: "k < length inp" "inp!k = a"
    hence "y = inc_item x (k+1)"
      using * unfolding Scan_it_def by simp
    hence "y \<in> Scan k I"
      using \<open>x \<in> bin I k\<close> # assms(5) unfolding Scan_def by blast
  }
  thus "y \<in> Scan k I"
    using * unfolding Scan_it_def by fastforce
qed

lemma Predict_it_sub_Predict:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some X"
  shows "set (Predict_it k X) \<subseteq> Predict k I"
proof standard
  fix y
  assume *: "y \<in> set (Predict_it k X)"
  have "x \<in> bin I k"
    using kth_bin_in_bins assms(1-4) set_bin_def wf_bin_def wf_bins_def bin_def by blast
  let ?rs = "filter (\<lambda>r. rule_head r = X) rules"
  let ?xs = "map (\<lambda>r. init_item r k) ?rs"
  have "y \<in> set ?xs"
    using * unfolding Predict_it_def by simp
  then obtain r where "y = init_item r k" "rule_head r = X" "r \<in> \<RR>" "next_symbol x = Some (rule_head r)"
    using valid_rules assms(5) by auto
  thus "y \<in> Predict k I"
    unfolding Predict_def using \<open>x \<in> bin I k\<close> by blast
qed

lemma Complete_it_sub_Complete:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "y \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol y = None"
  shows "set (Complete_it k y bs) \<subseteq> Complete k I"
proof standard
  fix x
  assume *: "x \<in> set (Complete_it k y bs)"
  have "y \<in> bin I k"
    using kth_bin_in_bins assms set_bin_def wf_bin_def wf_bins_def bin_def by blast
  let ?orig = "bins bs ! item_origin y"
  let ?xs = "filter (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"
  have "item_origin y < length (bins bs)"
    using set_bin_def wf_bins_def wf_bin_def wf_item_def assms(1,3,4) by force
  hence "\<forall>z \<in> set ?xs. z \<in> bin I (item_origin y)"
     using wf_bin_def wf_bins_def bin_def assms kth_bin_in_bins set_bin_def by fastforce
  then obtain z where "x = inc_item z k" "next_symbol z = Some (item_rule_head y)" "z \<in> bin I (item_origin y)"
    using * Complete_it_def by auto
  thus "x \<in> Complete k I"
    using \<open>y \<in> bin I k\<close> assms(5) unfolding Complete_def next_symbol_def by (auto split: if_splits)
qed

lemma \<pi>_it'_sub_\<pi>:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "length (bins bs) = length inp + 1" "k < length (bins bs)"
  shows "set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k I"
  using assms
proof (induction k bs i arbitrary: I rule: \<pi>_it'_induct)
  case (Base k bs i)
  thus ?case
    using \<pi>_mono by auto
next
  case (Complete k bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by force
  have "set_bins ?bs' \<subseteq> I \<union> Complete k I"
    using 0 Complete_it_sub_Complete Complete.hyps(3) Complete.prems(1,2,4) set_bins_app_bins Un_mono by metis
  moreover have "wf_bins ?bs'"
    using 0 wf_bins_app_bins Complete.hyps(2) Complete.prems(1,4) wf_bins_Complete_it 
      distinct_Complete_it wf_bins_kth_bin wf_item_def by (metis Orderings.order_class.dual_order.strict_trans2)
  ultimately have "set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k (I \<union> Complete k I)"
    using Complete.IH Complete.hyps Complete.prems(3,4) by simp
  thus ?case
    using Complete_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
next
  case (Scan k bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k a x)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by force
  have "set_bins ?bs' \<subseteq> I \<union> Scan k I"
    using 0 Scan_it_sub_Scan[OF Scan.prems(1,2) 0 Scan.prems(4) Scan.hyps(3)]
          Scan.hyps(5) Scan.prems(2,3) set_bins_app_bins by auto
  moreover have "wf_bins ?bs'"
    using 0 wf_bins_Scan_it wf_bins_app_bins Scan.hyps(3,5) Scan.prems(1,4) distinct_Scan_it by force
  ultimately have "set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k (I \<union> Scan k I)"
    using Scan.IH Scan.hyps Scan.prems(3,4) by simp
  thus ?case
    using Scan_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
next
  case (Pass k bs i x a)
  thus ?case
    using \<pi>_it'_simps(4) by presburger
next
  case (Predict k bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k a)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by force
  have "set_bins ?bs' \<subseteq> I \<union> Predict k I"
    using 0 Predict_it_sub_Predict Predict.hyps(3) Predict.prems(1,2,4) set_bins_app_bins Un_mono by metis
  moreover have "wf_bins ?bs'"
    using Suc_eq_plus1 Suc_le_eq Suc_le_mono Predict.prems(1,3,4) wf_bins_Predict_it
      wf_bins_app_bins distinct_Predict_it by presburger
  ultimately have "set_bins (\<pi>_it' k bs i)  \<subseteq> \<pi> k (I \<union> Predict k I)"
    using Predict.IH Predict.hyps Predict.prems(3,4) by simp
  thus ?case
    using Predict_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
qed

lemma \<pi>_it_sub_\<pi>:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "length (bins bs) = length inp + 1" "k < length (bins bs)"
  shows "set_bins (\<pi>_it k bs) \<subseteq> \<pi> k I"
  using assms \<pi>_it'_sub_\<pi> \<pi>_it_def by metis

lemma \<I>_it_sub_\<I>:
  "k < length (bins Init_it) \<Longrightarrow> set_bins (\<I>_it k) \<subseteq> \<I> k"
  by (induction k) (auto simp: Init_it_eq_Init \<pi>_it_sub_\<pi> wf_bins_Init_it wf_bins_\<I>_it)

lemma \<II>_it_sub_\<II>:
  "set_bins \<II>_it \<subseteq> \<II>"
  using \<I>_it_sub_\<I> \<II>_def \<II>_it_def by auto

subsection \<open>Soundness\<close>

lemma sound_Scan_it:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some a" "wf_items I" "sound_items I"
  shows "sound_items (set (Scan_it k a x))"
  using sound_Scan Scan_it_sub_Scan assms by (meson sound_items_def subsetD)

lemma sound_Predict_it:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some X" "sound_items I"
  shows "sound_items (set (Predict_it k X))"
  using sound_Predict Predict_it_sub_Predict sound_items_def assms by (meson subsetD)

lemma sound_Complete_it:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "y \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol y = None" "wf_items I" "sound_items I"
  shows "sound_items (set (Complete_it k y bs))"
  using sound_Complete Complete_it_sub_Complete sound_items_def assms by (meson subsetD)

lemma sound_\<pi>_it':
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "sound_items (set_bins bs)"
  shows "sound_items (set_bins (\<pi>_it' k bs i))"
  using assms
proof (induction k bs i rule: \<pi>_it'_induct)
  case (Complete k bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by force
  have "wf_bins ?bs'"
    using 0 Complete.prems(1,2) wf_bins_Complete_it wf_bins_app_bins distinct_Complete_it
      wf_bins_kth_bin wf_item_def by (metis Orderings.order_class.order.strict_trans1)
  moreover have "sound_items (set (Complete_it k x bs))"
    using 0 sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems(1,2,4) set_bins_bin_exists 
            sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def by metis
  ultimately have "sound_items (set_bins (\<pi>_it' k ?bs' (i + 1)))"
    using Complete.IH Complete.prems(2-4) set_bins_app_bins sound_items_def by auto
  thus ?case
    using Complete.hyps by simp
next
  case (Scan k bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k a x)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by force
  have "wf_bins ?bs'"
    using 0 Scan.prems(1,2) wf_bins_Scan_it wf_bins_app_bins Scan.hyps(3,5) distinct_Scan_it by simp
  moreover have "sound_items (set (Scan_it k a x))"
    using 0 sound_Scan_it \<pi>_mono Scan.hyps(3) Scan.prems(1,2,4) set_bins_bin_exists 
            sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def by metis
  ultimately have "sound_items (set_bins (\<pi>_it' k ?bs' (i + 1)))"
    using Scan.IH Scan.prems(2-4) set_bins_app_bins sound_items_def Scan.hyps(5) by auto
  thus ?case
    using Scan.hyps by simp
next
  case (Predict k bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k a)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by force
  have "wf_bins ?bs'"
    using 0 Predict.prems(1-3) wf_bins_Predict_it wf_bins_app_bins distinct_Predict_it by simp
  moreover have "sound_items (set (Predict_it k a))"
    using 0 sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems(1,2,4) set_bins_bin_exists 
            sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def by metis
  ultimately have "sound_items (set_bins (\<pi>_it' k ?bs' (i + 1)))"
    using Predict.IH Predict.prems(2-4) set_bins_app_bins sound_items_def by auto
  thus ?case
    using Predict.hyps by simp
qed simp_all

lemma sound_\<pi>_it:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "sound_items (set_bins bs)"
  shows "sound_items (set_bins (\<pi>_it k bs))"
  using sound_\<pi>_it' assms \<pi>_it_def by simp

subsection \<open>Set to List\<close>

lemma bin_set_bins_upto_set_bins_eq:
  assumes "wf_bins bs" "k < length (bins bs)" "i \<ge> length (items (bins bs ! k))" "l \<le> k"
  shows "bin (set_bins_upto bs k i) l = bin (set_bins bs) l"
  unfolding set_bins_upto_def set_bins_def bin_def using assms nat_less_le
  by (auto simp: nth_list_update set_bin_upto_eq_set_bin wf_bins_kth_bin, metis less_trans, blast)

lemma impossible_complete_item:
  assumes "wf_item x" "sound_item x" "is_complete x"  "item_origin x = k" "item_end x = k"
  shows False
proof -
  have "derives [item_rule_head x] []"
    using assms(2-5) sound_item_def item_\<beta>_def is_complete_def by (simp add: slice_empty)
  moreover have "is_nonterminal (item_rule_head x)"
    using assms(1) unfolding wf_item_def item_rule_head_def rule_head_def
    by (metis prod.collapse rule_nonterminal_type)
  ultimately show ?thesis
    using nonempty_deriv is_nonterminal_def by blast
qed

lemma Complete_Un_eq_terminal:
  assumes "next_symbol z = Some a" "is_terminal a" "wf_items I" "wf_item z"
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
    have "is_nonterminal (item_rule_head y)"
      using wf_item_def wf_items_def bin_def item_rule_head_def rule_head_def validRules *(5) assms(3,4) by force
    thus ?thesis
      using True *(7) assms(1,2) is_terminal_nonterminal by auto
  next
    case False
    thus ?thesis
      using * assms(1) next_symbol_def Complete_def bin_def by auto
  qed
qed

lemma Complete_Un_eq_nonterminal:
  assumes "next_symbol z = Some a" "is_nonterminal a" "sound_items I" "item_end z = k" "wf_items I" "wf_item z"
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
      using *(4) A assms(4) bin_def by auto
    moreover have "item_end y = k"
      using *(5) bin_def by blast
    moreover have "sound_item y"
      using *(5,6) assms(1) next_symbol_def assms(3) bin_def sound_items_def by auto
    moreover have "wf_item y"
      using *(5) assms(5,6) bin_def wf_items_def by fastforce
    ultimately show ?thesis
      using impossible_complete_item *(6) by blast
  next
    case B
    thus ?thesis
      using *(6) assms(1) next_symbol_def by force
  next
    case 3
    thus ?thesis
      using *(2-7) Complete_def bin_def by simp
  qed
qed

lemma wf_item_in_kth_bin:
  "wf_bins bs \<Longrightarrow> x \<in> set_bins bs \<Longrightarrow> item_end x = k \<Longrightarrow> x \<in> set_bin (bins bs ! k)"
  using set_bins_bin_exists wf_bins_kth_bin wf_bins_def by blast

lemma Complete_set_bins_upto_eq_set_bins:
  assumes "wf_bins bs" "k < length (bins bs)" "i \<ge> length (items (bins bs ! k))"
  shows "Complete k (set_bins_upto bs k i) = Complete k (set_bins bs)"
proof -
  have "\<And>l. l \<le> k \<Longrightarrow> bin (set_bins_upto bs k i) l = bin (set_bins bs) l"
    using bin_set_bins_upto_set_bins_eq[OF assms] by blast
  moreover have "wf_items (set_bins bs)"
    using assms(1) wf_items_def wf_bins_def wf_bin_def by (auto, metis set_bins_bin_exists wf_bins_kth_bin)
  ultimately show ?thesis
    unfolding Complete_def bin_def wf_items_def wf_item_def by auto
qed

lemma Complete_sub_set_bins_Un_Complete_it:
  assumes "Complete k I \<subseteq> set_bins bs" "I \<subseteq> set_bins bs" "is_complete z" "wf_bins bs" "wf_item z"
  shows "Complete k (I \<union> {z}) \<subseteq> set_bins bs \<union> set (Complete_it k z bs)"
proof standard
  fix w
  assume "w \<in> Complete k (I \<union> {z})"
  then obtain x y where *:
    "w = inc_item x k" "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by blast
  consider (A) "x = z" | (B) "y = z" | "\<not> (x = z \<or> y = z)"
    by blast
  thus "w \<in> set_bins bs \<union> set (Complete_it k z bs)"
  proof cases
    case A
    thus ?thesis
      using *(5) assms(3) next_symbol_def by auto
  next
    case B
    let ?orig = "bins bs ! item_origin z"
    let ?is = "filter (\<lambda>x. next_symbol x = Some (item_rule_head z)) (items ?orig)"
    have "x \<in> bin I (item_origin y)"
      using B *(2) *(5) assms(3) next_symbol_def bin_def by auto
    moreover have "bin I (item_origin z) \<subseteq> set_bin (bins bs ! item_origin z)"
      using wf_item_in_kth_bin assms(2,4) bin_def by blast
    ultimately have "x \<in> set ?is"
      using *(5) B set_bin_def by (simp add: in_mono)
    thus ?thesis
      unfolding Complete_it_def *(1) by simp
  next
    case 3
    thus ?thesis
      using * assms(1) Complete_def bin_def by auto
  qed
qed

lemma Complete_it_eq_item_origin:
  assumes "set_bin (bins bs ! item_origin x) = set_bin (bins bs' ! item_origin x)"
  shows "set (Complete_it k x bs) = set (Complete_it k x bs')"
  using assms unfolding Complete_it_def by simp

lemma kth_bin_set_bins_upto_empty:
  assumes "wf_bins bs" "k < length (bins bs)"
  shows "bin (set_bins_upto bs k 0) k = {}"
proof -
  {
    fix x
    assume "x \<in> set_bins_upto bs k 0"
    then obtain l where "x \<in> set_bin (bins bs ! l)" "l < k"
      unfolding set_bins_upto_def set_bin_upto_def by blast
    hence "item_end x = l"
      using wf_bins_kth_bin assms by simp
    hence "item_end x < k"
      using \<open>l < k\<close> by blast
  }
  thus ?thesis
    using bin_def by auto
qed

lemma \<pi>_it'_mono:
  assumes "k < length (bins bs)" "length (bins bs) = length inp + 1"
  shows "set_bins bs \<subseteq> set_bins (\<pi>_it' k bs i)"
  using assms set_bins_app_bins
  by (induction k bs i rule: \<pi>_it'_induct) auto

lemma \<pi>_step_sub_\<pi>_it':
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k i) \<subseteq> set_bins bs"
  assumes "sound_items (set_bins bs)"
  shows "\<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  using assms
proof (induction k bs i rule: \<pi>_it'_induct)
  case (Base k bs i)
  have "bin (set_bins bs) k = bin (set_bins_upto bs k i) k"
    using Base.hyps Base.prems(1,2) bin_set_bins_upto_set_bins_eq by simp
  thus ?case
    using Scan_bin_absorb Predict_bin_absorb Complete_set_bins_upto_eq_set_bins 
      Base.hyps Base.prems(1,2,4) \<pi>_step_def by (auto; metis in_mono)
next
  case (Complete k bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by auto
  have wf: "wf_bins ?bs'"
    using Complete.hyps Complete.prems(1,2) wf_bins_Complete_it wf_bins_app_bins set_bin_def
      distinct_Complete_it wf_bins_kth_bin wf_item_def x by (metis Orderings.order_class.order.strict_trans1)
  have sound: "sound_items (set_bins ?bs')"
    using sound_Complete_it[OF _ _ _ Complete.prems(2) Complete.hyps(3)] wf_bins_impl_wf_items 
          Complete.hyps(1,2) set_bins_app_bins sound_items_def Complete.prems(1,2,5) by auto
  have "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Scan k (set_bins_upto ?bs' k (i + 1)) = Scan k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using Complete.hyps(1) set_bins_upto_Suc_Un length_nth_bin_app_bins by (metis less_le_trans not_le_imp_less)
    also have "... = Scan k (set_bins_upto bs k i \<union> {x})"
      using Complete.hyps(1,2) Complete.prems(2) kth_app_bins set_bins_upto_kth_nth_id by simp
    also have "... \<subseteq> set_bins bs \<union> Scan k {x}"
      using Complete.prems(3,4) Scan_Un Scan_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Complete.hyps(3) Complete.prems(1,2) bin_def kth_bin_in_bins wf_bins_kth_bin Scan_def by auto
    finally show ?thesis
      using Complete.prems(2) set_bins_app_bins by auto
  qed
  moreover have "Predict k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Predict k (set_bins_upto ?bs' k (i + 1)) = Predict k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using Complete.hyps(1) set_bins_upto_Suc_Un length_nth_bin_app_bins by (metis less_le_trans not_le_imp_less)
    also have "... = Predict k (set_bins_upto bs k i \<union> {x})"
      using Complete.hyps(1,2) Complete.prems(2) kth_app_bins set_bins_upto_kth_nth_id by simp
    also have "... \<subseteq> set_bins bs \<union> Predict k {x}"
      using Complete.prems(3,4) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Complete.hyps(3) Complete.prems(1,2) bin_def kth_bin_in_bins wf_bins_kth_bin Predict_def by auto
    finally show ?thesis
      using Complete.prems(2) set_bins_app_bins by auto
  qed
  moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un length_nth_bin_app_bins Complete.hyps(1) by (metis less_le_trans not_le_imp_less)
    also have "... = Complete k (set_bins_upto bs k i \<union> {x})"
      using kth_app_bins Complete.hyps(1,2) set_bins_upto_kth_nth_id Complete.prems(2) by simp
    also have "... \<subseteq> set_bins bs \<union> set (Complete_it k x bs)"
      using Complete_sub_set_bins_Un_Complete_it Complete.hyps(3) Complete.prems(1,2,4) next_symbol_def
        set_bins_upto_sub_set_bins wf_bins_kth_bin x by (metis Complete_\<pi>_step_mono Option.option.simps(3) subset_trans)
    finally show ?thesis
      using Complete.prems(2) set_bins_app_bins by blast
  qed
  ultimately have "\<pi>_step k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i+1))"
    using Complete.IH Complete.prems(2,3) sound wf \<pi>_step_def set_bins_upto_sub_set_bins by simp
  thus ?case
    using \<pi>_it'_simps(2) \<pi>_step_sub_mono Complete.hyps local.Complete.prems(2) set_bins_app_bins
    by (metis inf_sup_ord(3) subset_trans)
next
  case (Scan k bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k a x)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by auto
  have wf: "wf_bins ?bs'"
    using Scan.prems(1,2) Scan.hyps wf_bins_app_bins wf_bins_Scan_it x distinct_Scan_it by (metis Option.option.discI nat_less_le)
  have sound: "sound_items (set_bins ?bs')"
    using sound_Scan_it[OF Scan.prems(1) _ x Scan.prems(2)] Scan.hyps(3,5) Scan.prems(1,3,5) 
          set_bins_app_bins sound_items_def wf_bins_impl_wf_items by fastforce
  have "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Scan k (set_bins_upto ?bs' k (i + 1)) = Scan k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un Scan.hyps(1) nth_app_bins by auto
    also have "... = Scan k (set_bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(3) nth_app_bins set_bins_upto_kth_nth_id by simp
    also have "... \<subseteq> set_bins bs \<union> Scan k {x}"
      using Scan.prems(3,4) Scan_Un Scan_\<pi>_step_mono by fastforce
    finally have *: "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs \<union> Scan k {x}" .
    show ?thesis
    proof cases
      assume a1: "inp!k = a"
      hence "Scan k {x} = {inc_item x (k+1)}"
        using Scan_def bin_def Scan.hyps(1-3,5) wf_bins_kth_bin bin_def Scan.prems(1,2) by simp
      hence "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs \<union> {inc_item x (k+1)}"
        using * by blast
      also have "... = set_bins bs \<union> set (Scan_it k a x)"
        using Scan_it_def a1 Scan.hyps(5) by force
      also have "... = set_bins ?bs'"
        using set_bins_app_bins Scan.hyps(5) Scan.prems(3) by auto
      finally show ?thesis .
    next
      assume a1: "\<not> inp!k = a"
      hence "Scan k {x} = {}"
        using Scan_def bin_def Scan.hyps(3) by simp
      hence "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs"
        using * by blast
      also have "... \<subseteq> set_bins ?bs'"
        using Scan.hyps(5) Scan.prems(3) set_bins_app_bins by force
      finally show ?thesis .
    qed
  qed
  moreover have "Predict k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Predict k (set_bins_upto ?bs' k (i + 1)) = Predict k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un Scan.hyps(1) nth_app_bins by auto
    also have "... = Predict k (set_bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(3) nth_app_bins set_bins_upto_kth_nth_id by simp
    also have "... \<subseteq> set_bins bs \<union> Predict k {x}"
      using Scan.prems(3,4) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Scan.hyps(3,4) Predict_def bin_def rule_head_def validRules valid_rules is_terminal_nonterminal by fastforce
    finally show ?thesis
      using set_bins_app_bins Scan.hyps(5) Scan.prems(3) by auto
  qed
  moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un Scan.hyps(1) nth_app_bins by force
    also have "... = Complete k (set_bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(3) nth_app_bins set_bins_upto_kth_nth_id by auto
    also have "... = Complete k (set_bins_upto bs k i)"
      using Complete_Un_eq_terminal Scan.hyps(3,4) Scan.prems(1,2) set_bins_upto_sub_set_bins subset_iff
            wf_bins_impl_wf_items wf_bins_kth_bin wf_items_def x by metis
    finally show ?thesis
      using Scan.hyps(5) Scan.prems(3,4) set_bins_app_bins Complete_\<pi>_step_mono by fastforce
  qed
  ultimately have "\<pi>_step k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i+1))"
    using Scan.IH Scan.prems(2,3) sound wf \<pi>_step_def set_bins_upto_sub_set_bins by simp
  thus ?case
    using set_bins_app_bins \<pi>_step_sub_mono \<pi>_it'_simps(3) Scan.hyps Scan.prems(2,3)
    by (auto, meson Un_upper1 in_mono)
next
  case (Pass k bs i x a)
  have x: "x \<in> set_bin (bins bs ! k)"
    using Pass.hyps(1,2) by auto
  have "Scan k (set_bins_upto bs k (i + 1)) \<subseteq> set_bins bs"
    using Scan_def Pass.hyps(5) by blast
  moreover have "Predict k (set_bins_upto bs k (i + 1)) \<subseteq> set_bins bs"
  proof -
    have "Predict k (set_bins_upto bs k (i + 1)) = Predict k (set_bins_upto bs k i \<union> {items (bins bs ! k) ! i})"
      using set_bins_upto_Suc_Un Pass.hyps(1) nth_app_bins by auto
    also have "... = Predict k (set_bins_upto bs k i \<union> {x})"
      using Pass.hyps(1,2,5) Pass.prems(3) nth_app_bins set_bins_upto_kth_nth_id by simp
    also have "... \<subseteq> set_bins bs \<union> Predict k {x}"
      using Pass.prems(3,4) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Pass.hyps(3,4) Predict_def bin_def rule_head_def validRules valid_rules is_terminal_nonterminal by fastforce
    finally show ?thesis
      using set_bins_app_bins Pass.hyps(5) Pass.prems(3) by auto
  qed
  moreover have "Complete k (set_bins_upto bs k (i + 1)) \<subseteq> set_bins bs"
  proof -
    have "Complete k (set_bins_upto bs k (i + 1)) = Complete k (set_bins_upto bs k i \<union> {x})"
      using set_bins_upto_Suc_Un Pass.hyps(1,2) by simp
    also have "... = Complete k (set_bins_upto bs k i)"
      using Complete_Un_eq_terminal Pass.hyps Pass.prems(1,2) set_bins_upto_Suc_Un set_bins_upto_sub_set_bins subset_iff 
            wf_bins_impl_wf_items wf_items_def wf_bins_kth_bin x by metis
    finally show ?thesis
      using Pass.prems(4) Complete_\<pi>_step_mono by blast
  qed
  ultimately have "\<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs (i+1))"
    using Pass.IH Pass.prems(1-3,5) \<pi>_step_def set_bins_upto_sub_set_bins by simp
  thus ?case
    using set_bins_app_bins Pass.hyps Pass.prems by simp
next
  case (Predict k bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k a)"
  have "k \<ge> length inp \<or> \<not> inp!k = a"
    using Predict.hyps(4) valid_inp is_terminal_def by force
  have x: "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by auto
  have len: "i < length (items (bins ?bs' ! k))"
    using length_nth_bin_app_bins Predict.hyps(1) by (meson leI le_trans)
  have wf: "wf_bins ?bs'"
    using Predict.prems(1-3) wf_bins_Predict_it wf_bins_app_bins distinct_Predict_it by force
  have sound: "sound_items (set_bins ?bs')" 
    using sound_Predict_it[OF _ _ x] Predict.hyps(3) Predict.prems(1,2,5) set_bins_app_bins sound_items_def by auto
  have nonterm: "is_nonterminal a"
    using is_complete_def is_sentence_cons is_sentence_item_\<beta> is_symbol_distinct item_\<beta>_def
          Predict.hyps(3,4) Predict.prems(1,2) next_symbol_def wf_bins_kth_bin x
    by (metis Cons_nth_drop_Suc Option.option.inject Option.option.simps(3) not_le_imp_less)
  have "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Scan k (set_bins_upto ?bs' k (i + 1)) = Scan k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using Predict.hyps(1) set_bins_upto_Suc_Un length_nth_bin_app_bins by (metis less_le_trans not_le_imp_less)
    also have "... = Scan k (set_bins_upto bs k i \<union> {x})"
      using Predict.hyps(1,2) Predict.prems(2) kth_app_bins set_bins_upto_kth_nth_id by simp
    also have "... \<subseteq> set_bins bs \<union> Scan k {x}"
      using Predict.prems(3,4) Scan_Un Scan_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Predict.hyps(3) \<open>length inp \<le> k \<or> inp ! k \<noteq> a\<close> Scan_def bin_def by auto
    finally show ?thesis
      using Predict.prems(2) set_bins_app_bins by auto
  qed
  moreover have "Predict k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Predict k (set_bins_upto ?bs' k (i + 1)) = Predict k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using Predict.hyps(1) set_bins_upto_Suc_Un length_nth_bin_app_bins by (metis less_le_trans not_le_imp_less)
    also have "... = Predict k (set_bins_upto bs k i \<union> {x})"
      using Predict.hyps(1,2) Predict.prems(2) kth_app_bins set_bins_upto_kth_nth_id by simp
    also have "... \<subseteq> set_bins bs \<union> Predict k {x}"
      using Predict.prems(3,4) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = set_bins bs \<union> set (Predict_it k a)"
      using Predict.hyps Predict.prems(1,2) Predict_def Predict_it_def valid_rules bin_def wf_bins_kth_bin by auto
    finally show ?thesis
      using Predict.prems(2) set_bins_app_bins by auto
  qed
  moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un len by force
    also have "... = Complete k (set_bins_upto bs k i \<union> {x})"
      using kth_app_bins Predict.hyps(1,2) Predict.prems(2) set_bins_upto_kth_nth_id by auto
    also have "... = Complete k (set_bins_upto bs k i)"
      using Complete_Un_eq_nonterminal nonterm Predict.hyps(3) Predict.prems(1,2,5) set_bins_upto_sub_set_bins 
            sound_items_def subset_eq wf_bins_kth_bin x wf_bins_impl_wf_items wf_items_def by metis
    finally show ?thesis
      using set_bins_app_bins Predict.prems(2,4) Complete_\<pi>_step_mono by fastforce
  qed
  ultimately have "\<pi>_step k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i+1))"
    using Predict.IH Predict.prems(2,3) sound wf \<pi>_step_def set_bins_upto_sub_set_bins by simp
  thus ?case
    using set_bins_app_bins \<pi>_step_sub_mono \<pi>_it'_simps(5) Predict.hyps Predict.prems(2,3)
    by (auto, meson Un_upper1 subsetD)
qed

lemma \<pi>_step_sub_\<pi>_it:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs"
  assumes "sound_items (set_bins bs)"
  shows "\<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using assms \<pi>_step_sub_\<pi>_it' \<pi>_it_def by metis

lemma \<pi>_it'_idem:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1" "i \<le> j"
  assumes "sound_items (set_bins bs)"
  shows "\<pi>_it' k (\<pi>_it' k bs i) j = \<pi>_it' k bs i"
  using assms
proof (induction k bs i arbitrary: j rule: \<pi>_it'_induct)
  case (Complete k bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by auto
  have wf: "wf_bins ?bs'"
    using Complete.hyps Complete.prems(1,2) wf_bins_Complete_it wf_bins_app_bins set_bin_def
      distinct_Complete_it wf_bins_kth_bin wf_item_def x by (metis Orderings.order_class.order.strict_trans1)
  have sound: "sound_items (set_bins ?bs')"
    using sound_Complete_it[OF _ _ _ Complete.prems(2) Complete.hyps(3)] wf_bins_impl_wf_items 
          Complete.hyps(1,2) set_bins_app_bins sound_items_def Complete.prems(1,2,5) by auto
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using wf sound Complete by simp
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Complete.prems(4) by simp
    have "\<pi>_it' k (\<pi>_it' k bs i) j = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) j"
      using \<pi>_it'_simps(2) Complete.hyps(1-3) by presburger
    also have "... = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k ?bs' (i+1)"
      have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_app_bins by (meson le_trans)
      hence 0: "\<not> length (items (bins ?bs'' ! k)) \<le> j"
        using \<open>i = j\<close> Complete.hyps(1) by linarith
      have "x = items (bins ?bs' ! k) ! j"
        using \<open>i = j\<close> kth_app_bins Complete.hyps(1,2) by auto
      hence 1: "x = items (bins ?bs'' ! k) ! j"
        using \<open>i = j\<close> kth_\<pi>_it'_bins length_nth_bin_app_bins Complete.hyps(1) by (metis leI order_trans)
      have "\<pi>_it' k ?bs'' j = \<pi>_it' k (app_bins ?bs'' k (Complete_it k x ?bs'')) (j+1)"
        using \<pi>_it'_simps(2) 0 1 Complete.hyps(3) by blast
      moreover have "app_bins ?bs'' k (Complete_it k x ?bs'') = ?bs''"
      proof -
        have "set (Complete_it k x ?bs'') = set (Complete_it k x bs)"
        proof (cases "item_origin x = k")
          case True
          thus ?thesis
            using impossible_complete_item True kth_bin_in_bins Complete.hyps(3) Complete.prems(1,2,5) 
                  wf_bins_kth_bin x sound_items_def next_symbol_def by fastforce
        next
          case False
          hence "item_origin x < k"
            using x Complete.prems(1,2) wf_bins_kth_bin wf_item_def by force
          hence "set_bin (bins bs ! item_origin x) = set_bin (bins ?bs'' ! item_origin x)"
            using False app_bins_def set_bin_\<pi>_it'_eq by force
          thus ?thesis
            using Complete_it_eq_item_origin by blast
        qed
        also have "... \<subseteq> set_bin (bins ?bs' ! k)"
          using Complete.prems(2) app_bins_def set_bin_app_bin by auto
        also have "... \<subseteq> set_bin (bins ?bs'' ! k)"
          using Complete.prems(2) nth_bin_sub_\<pi>_it' by auto
        finally have "set (Complete_it k x ?bs'') \<subseteq> set_bin (bins ?bs'' ! k)" .
        thus ?thesis
          using app_bins_eq Complete.prems(2) length_bins_\<pi>_it' length_bins_app_bins by presburger
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k ?bs' (i + 1)"
      using Complete.IH Complete.prems(1-3) \<open>i = j\<close> Complete.hyps length_bins_app_bins 
            wf_bins_Complete_it wf_bins_app_bins x wf sound by force
    finally show ?thesis
      using Complete.hyps by simp
  qed
next
  case (Scan k bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k a x)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by auto
  have wf: "wf_bins ?bs'"
    using Scan.prems(1,2) Scan.hyps wf_bins_app_bins wf_bins_Scan_it x distinct_Scan_it by (metis Option.option.discI nat_less_le)
  have sound: "sound_items (set_bins ?bs')"
    using sound_Scan_it[OF Scan.prems(1) _ x Scan.prems(2)] Scan.hyps(3,5) Scan.prems(1,3,5) 
          set_bins_app_bins sound_items_def wf_bins_impl_wf_items by fastforce
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using wf sound Scan by simp
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Scan.prems(4) by auto
    have "\<pi>_it' k (\<pi>_it' k bs i) j = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) j"
      using Scan.hyps by simp
    also have "... = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k ?bs' (i+1)"
      have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_app_bins order_trans by blast
      hence "\<pi>_it' k ?bs'' j = \<pi>_it' k (app_bins ?bs'' (k+1) (Scan_it k a x)) (j+1)"
        using \<open>i = j\<close> kth_\<pi>_it'_bins nth_app_bin \<pi>_it'_simps(3) Scan.hyps by (smt (z3) le_less_trans not_le)
      moreover have "app_bins ?bs'' (k+1) (Scan_it k a x) = ?bs''"
      proof -
        have "set (Scan_it k a x) = set (Scan_it k a x)"
          unfolding Scan_it_def by blast
        also have "... \<subseteq> set_bin (bins ?bs' ! (k+1))"
          using Scan.hyps(5) Scan.prems(3) app_bins_def set_bin_app_bin by auto
        also have "... \<subseteq> set_bin (bins ?bs'' ! (k+1))"
          using Scan.hyps(5) Scan.prems(3) nth_bin_sub_\<pi>_it' by auto
        ultimately have "set (Scan_it k a x) \<subseteq> set_bin (bins ?bs'' ! (k+1))"
          using \<open>set (Scan_it k a x) \<subseteq> set_bin (bins (app_bins bs (k + 1) (Scan_it k a x)) ! (k + 1))\<close> by blast
        thus ?thesis
          using app_bins_eq Scan.hyps(5) Scan.prems(3) length_bins_\<pi>_it' by simp
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k ?bs' (i + 1)"
      using \<open>i = j\<close> Scan.IH Scan.prems(2,3) sound wf by simp
    finally show ?thesis
      using Scan.hyps by simp
  qed
next
  case (Pass k bs i x a)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using Pass by simp
  next
    assume "\<not> i+1 \<le> j"
    show ?thesis
      using Pass \<pi>_it'_simps(1,4) kth_\<pi>_it'_bins by (metis Suc_eq_plus1 Suc_leI antisym_conv2 not_le_imp_less)
  qed
next
  case (Predict k bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k a)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by auto
  have len: "i < length (items (bins ?bs' ! k))"
    using length_nth_bin_app_bins Predict.hyps(1) by (meson leI le_trans)
  have wf: "wf_bins ?bs'"
    using Predict.prems(1-3) wf_bins_Predict_it wf_bins_app_bins distinct_Predict_it by force
  have sound: "sound_items (set_bins ?bs')" 
    using sound_Predict_it[OF _ _ x] Predict.hyps(3) Predict.prems(1,2,5) set_bins_app_bins sound_items_def by auto
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using sound wf Predict by simp
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Predict.prems(4) by auto
    have "\<pi>_it' k (\<pi>_it' k bs i) j = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) j"
      using Predict.hyps by simp
    also have "... = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k ?bs' (i+1)"
      have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_app_bins by (meson order_trans)
      hence "\<pi>_it' k ?bs'' j = \<pi>_it' k (app_bins ?bs'' k (Predict_it k a)) (j+1)"
        using \<open>i = j\<close> kth_\<pi>_it'_bins nth_app_bin \<pi>_it'_simps(5) Predict.hyps
        by (smt (z3) Orderings.order_class.order.trans not_le)
      moreover have "app_bins ?bs'' k (Predict_it k a) = ?bs''"
      proof -
        have "set (Predict_it k a) = set (Predict_it k a)"
          unfolding Predict_it_def by blast
        also have "... \<subseteq> set_bin (bins ?bs' ! k)"
          using Predict.prems(2) app_bins_def set_bin_app_bin by auto
        also have "... \<subseteq> set_bin (bins ?bs'' ! k)"
          using Predict.prems(2) nth_bin_sub_\<pi>_it' by simp
        ultimately have "set (Predict_it k a) \<subseteq> set_bin (bins ?bs'' ! k)"
          using \<open>set (Predict_it k a) \<subseteq> set_bin (bins (app_bins bs k (Predict_it k a)) ! k)\<close> by blast
        thus ?thesis
          using app_bins_eq Predict.prems(2) length_bins_\<pi>_it' by simp
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k ?bs' (i + 1)"
      using \<open>i = j\<close> Predict.IH Predict.prems(2,3) sound wf by simp
    finally show ?thesis
      using Predict.hyps by simp
  qed
qed simp

lemma \<pi>_it_idem:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1" "sound_items (set_bins bs)"
  shows "\<pi>_it k (\<pi>_it k bs) = \<pi>_it k bs"
  using assms \<pi>_it'_idem \<pi>_it_def le0 by metis

lemma funpower_\<pi>_step_sub_\<pi>_it:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs" "sound_items (set_bins bs)"
  shows "funpower (\<pi>_step k) n (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using assms
proof (induction n)
  case 0
  thus ?case
    using \<pi>_it'_mono \<pi>_it_def by simp
next
  case (Suc n)
  have 0: "\<pi>_step k (set_bins_upto (\<pi>_it k bs) k 0) \<subseteq> set_bins (\<pi>_it k bs)"
    using \<pi>_it'_mono set_bins_upto_k0_\<pi>_it'_eq \<pi>_it_def Suc.prems(2-4) order_trans by metis
  have "funpower (\<pi>_step k) (Suc n) (set_bins bs) \<subseteq> (\<pi>_step k) (set_bins (\<pi>_it k bs))"
    using \<pi>_step_sub_mono Suc by auto
  also have "... \<subseteq> set_bins (\<pi>_it k (\<pi>_it k bs))"
    using \<pi>_step_sub_\<pi>_it Suc.prems(1-3,5) wf_bins_\<pi>_it sound_\<pi>_it 0 by simp
  also have "... \<subseteq> set_bins (\<pi>_it k bs)"
    using \<pi>_it_idem Suc.prems by simp
  finally show ?case .
qed

lemma \<pi>_sub_\<pi>_it:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs" "sound_items (set_bins bs)"
  shows "\<pi> k (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using assms funpower_\<pi>_step_sub_\<pi>_it \<pi>_def elem_limit_simp by fastforce

lemma \<I>_sub_\<I>_it:
  "k < length (bins Init_it) \<Longrightarrow> \<I> k \<subseteq> set_bins (\<I>_it k)"
proof (induction k)
  case 0
  hence "\<pi> 0 Init \<subseteq> set_bins (\<pi>_it 0 Init_it)"
    using wf_bins_Init_it \<pi>_sub_\<pi>_it Init_it_eq_Init length_bins_Init_it Init_it_eq_Init 
          sound_Init set_bins_upto_empty \<pi>_step_empty set_bins_upto_sub_set_bins by metis
  thus ?case
    by simp
next
  case (Suc k)
  have wf: "wf_bins (\<I>_it k)"
    using length_bins_Init_it Suc.prems wf_bins_\<I>_it by force
  have sub: "\<pi>_step (Suc k) (set_bins_upto (\<I>_it k) (Suc k) 0) \<subseteq> set_bins (\<I>_it k)"
  proof -
    have "bin (set_bins_upto (\<I>_it k) (Suc k) 0) (Suc k) = {}"
      using kth_bin_set_bins_upto_empty wf Suc.prems by auto
    hence "\<pi>_step (Suc k) (set_bins_upto (\<I>_it k) (Suc k) 0) = set_bins_upto (\<I>_it k) (Suc k) 0"
      unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast
    also have "... \<subseteq> set_bins (\<I>_it k)"
      using wf Suc.prems set_bins_upto_sub_set_bins wf_bins_def by simp
    finally show ?thesis .
  qed
  have sound: "sound_items (set_bins (\<I>_it k))"
    using Suc sound_\<I> \<I>_it_sub_\<I> by (metis Suc_lessD subset_antisym)
  have "\<I> (Suc k) \<subseteq> \<pi> (Suc k) (set_bins (\<I>_it k))"
    using Suc \<pi>_sub_mono by simp
  also have "... \<subseteq> set_bins (\<pi>_it (Suc k) (\<I>_it k))"
    using \<pi>_sub_\<pi>_it wf sub sound Suc.prems by simp
  finally show ?case
    by simp
qed

lemma \<II>_sub_\<II>_it:
  "\<II> \<subseteq> set_bins \<II>_it"
  using \<I>_sub_\<I>_it \<II>_def \<II>_it_def by simp

subsection \<open>Correctness\<close>

corollary correctness_list:
  "earley_recognized (set_bins \<II>_it) \<longleftrightarrow> derives [\<SS>] inp"
  using \<II>_it_sub_\<II> \<II>_sub_\<II>_it correctness by simp

end

end
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
  "set_bin b = set_bin_upto b (length (items b))"

definition set_bins_upto :: "bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> items" where
  "set_bins_upto bs k i = \<Union> { set_bin (bins bs ! l) | l. l < k } \<union> set_bin_upto (bins bs ! k) i"

definition set_bins :: "bins \<Rightarrow> items" where
  "set_bins bs = set_bins_upto bs (length (bins bs) - 1) (length (items (bins bs ! (length (bins bs) - 1))))"

definition app_bin :: "bin \<Rightarrow> item list \<Rightarrow> bin" where
  "app_bin b is = Bin (items b @ (filter (\<lambda>i. i \<notin> set (items b)) is))"

definition app_bins :: "bins \<Rightarrow> nat \<Rightarrow> item list \<Rightarrow> bins" where
  "app_bins bs k is = Bins ((bins bs)[k := app_bin ((bins bs)!k) is])"

lemma length_bins_app_bins:
  "length (bins (app_bins bs k is)) = length (bins bs)"
  unfolding app_bins_def by simp

lemma length_kth_bin_app_bins:
  "k < length (bins bs) \<Longrightarrow> length (items (bins (app_bins bs k is) ! k)) \<ge> length (items (bins bs ! k))"
  unfolding app_bins_def app_bin_def by simp

lemma set_bin_conv_set:
  "set_bin b = set (items b)"
  unfolding set_bin_upto_def set_bin_def using set_conv_nth by fast

lemma set_bin_app_bin:
  "set_bin (app_bin b is) = set_bin b \<union> set is"
  unfolding app_bin_def set_bin_conv_set by auto

lemma set_bins_app_bins:
  assumes "k < length (bins bs)"
  shows "set_bins (app_bins bs k is) = set_bins bs \<union> set is"
  unfolding set_bins_def set_bins_upto_def app_bins_def set_bin_app_bin
  using assms length_bins_app_bins set_bin_app_bin set_bin_def
  apply (auto simp: nth_list_update, metis, metis Un_iff)
  by (metis Suc_pred Un_iff diff_self_eq_0 less_Suc_eq less_imp_diff_less)

lemma set_bin_upto_sub_set_bin:
  "set_bin_upto b i \<subseteq> set_bin b"
  unfolding set_bin_def set_bin_upto_def by blast

lemma kth_bin_in_bins:
  "k < length (bins bs) \<Longrightarrow> set_bin (bins bs ! k) \<subseteq> set_bins bs"
  unfolding set_bin_conv_set set_bins_def set_bins_upto_def set_bin_upto_def
  by (auto; metis Nat.minus_nat.diff_0 diff_Suc_Suc in_set_conv_nth lessE)

lemma kth_bin_nth_id:
  assumes "k < length (bins bs)" "i < length (items (bins bs ! k))"
  shows "items (bins (app_bins bs k is) ! k) ! i = items (bins bs ! k) ! i"
  unfolding app_bins_def app_bin_def using assms by (auto simp: nth_append)

lemma set_bins_upto_kth_nth_id:
  assumes "l < length (bins bs)" "k \<le> l" "i < length (items (bins bs ! k))"
  shows "set_bins_upto (app_bins bs l is) k i = set_bins_upto bs k i"
  unfolding set_bins_upto_def set_bin_def set_bin_upto_def app_bins_def app_bin_def
  using assms apply (auto simp: nth_append nth_list_update)
  using nat_neq_iff apply blast
  by (metis not_less nth_mem set_conv_nth)

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

definition Scan_it :: "nat \<Rightarrow> symbol \<Rightarrow> item \<Rightarrow> bins \<Rightarrow> item list" where \<comment>\<open>TODO: remove bs\<close>
  "Scan_it k a x bs = (
    if k < length inp \<and> inp!k = a then
      let x' = inc_item x (k+1) in
      [x']
    else [])"

definition Predict_it :: "nat \<Rightarrow> symbol \<Rightarrow> bins \<Rightarrow> item list" where \<comment>\<open>TODO: remove bs\<close>
  "Predict_it k X bs = (
    let rs = filter (\<lambda>r. rule_head r = X) rules in
    map (\<lambda>r. init_item r k) rs)"

definition Complete_it :: "nat \<Rightarrow> item \<Rightarrow> bins \<Rightarrow> item list" where \<comment>\<open>TODO: reduce bs???\<close>
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
              if k < length inp then app_bins bs (k+1) (Scan_it k a x bs)
              else bs
            else app_bins bs k (Predict_it k a bs)
        | None \<Rightarrow> app_bins bs k (Complete_it k x bs)
      in \<pi>_it' k bs' (i+1))"
  by pat_completeness simp
termination
  sorry
(* while_option :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option"
   while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" *)

lemma \<pi>_it'_simps[simp]:
  "length (items (bins bs ! k)) \<le> i \<Longrightarrow> \<pi>_it' k bs i = bs"
  "\<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = None \<Longrightarrow> 
    \<pi>_it' k bs i = \<pi>_it' k (app_bins bs k (Complete_it k x bs)) (i+1)"
  "\<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    is_terminal a \<Longrightarrow> k < length inp \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k (app_bins bs (k+1) (Scan_it k a x bs)) (i+1)"
  "\<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    is_terminal a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
  "\<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    \<not> is_terminal a \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k (app_bins bs k (Predict_it k a bs)) (i+1)"
  by (simp_all, simp_all add: Let_def)

lemma \<pi>_it'_induct[case_names Base Complete Scan Pass Predict]:
  assumes base: "\<And>k bs i. length (items (bins bs ! k)) \<le> i \<Longrightarrow> P k bs i"
  assumes complete: "\<And>k bs i x. \<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = None \<Longrightarrow> (\<And>xa. xa = app_bins bs k (Complete_it k x bs) \<Longrightarrow> P k xa (i+1)) \<Longrightarrow> P k bs i"
  assumes scan: "\<And>k bs i x a. \<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal a \<Longrightarrow> k < length inp \<Longrightarrow> 
            (\<And>xa. xa = app_bins bs (k+1) (Scan_it k a x bs) \<Longrightarrow> P k xa (i+1)) \<Longrightarrow> P k bs i"
  assumes pass: "\<And>k bs i x a. \<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> P k bs (i+1) \<Longrightarrow> P k bs i"
  assumes predict: "\<And>k bs i x a. \<not> length (items (bins bs ! k)) \<le> i \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> \<not> is_terminal a \<Longrightarrow> 
            (\<And>xa. xa = app_bins bs k (Predict_it k a bs) \<Longrightarrow> P k xa (i+1)) \<Longrightarrow> P k bs i"
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

definition \<pi>_it :: "nat \<Rightarrow> bins \<Rightarrow> bins" where
  "\<pi>_it k bs = \<pi>_it' k bs 0"

fun \<I>_it :: "nat \<Rightarrow> bins" where
  "\<I>_it 0 = \<pi>_it 0 Init_it"
| "\<I>_it (Suc n) = \<pi>_it (Suc n) (\<I>_it n)"

definition \<II>_it :: "bins" where
  "\<II>_it = \<I>_it (length inp)"

subsection \<open>Wellformed Bins\<close>

\<comment>\<open>TODO: add distinct condition on bin\<close>
definition wf_bin :: "nat \<Rightarrow> bin \<Rightarrow> bool" where
  "wf_bin k b \<longleftrightarrow> (\<forall>x \<in> set (items b). wf_item x \<and> item_end x = k)"

definition wf_bins :: "bins \<Rightarrow> bool" where
  "wf_bins bs \<longleftrightarrow> 0 < length (bins bs) \<and> (\<forall>k < length (bins bs). wf_bin k (bins bs ! k))"

lemma wf_bins_app_bins:
  "wf_bins bs \<Longrightarrow> \<forall>x \<in> set xs. wf_item x \<and> item_end x = k \<Longrightarrow> wf_bins (app_bins bs k xs)"
  unfolding wf_bins_def wf_bin_def app_bins_def using set_bin_app_bin set_bin_conv_set
  by (metis bins.sel Un_iff length_list_update nth_list_update_eq nth_list_update_neq)

lemma wf_bins_kth_bin:
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> x \<in> set_bin (bins bs ! k) \<Longrightarrow> wf_item x \<and> item_end x = k"
  using set_bin_conv_set wf_bin_def wf_bins_def by blast

lemma length_bins_Init_it:
  "length (bins Init_it) = length inp + 1"
  unfolding Init_it_def using length_bins_app_bins by force

lemma length_bins_\<pi>_it':
  "length (bins (\<pi>_it' k bs i)) = length (bins bs)"
  by (induction k bs i rule: \<pi>_it'.induct)
     (auto simp: length_bins_app_bins Let_def split: if_splits option.splits)

lemma length_bins_\<pi>_it:
  "length (bins (\<pi>_it k bs)) = length (bins bs)"
  unfolding \<pi>_it_def using length_bins_\<pi>_it' by blast

lemma length_bins_\<I>_it:
  "length (bins (\<I>_it k)) = length (bins Init_it)"
  by (induction k) (auto simp: length_bins_\<pi>_it)

lemma wf_bins_Init_it:
  "wf_bins Init_it"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS>) rules"
  let ?b0 = "Bin (map (\<lambda>r. init_item r 0) ?rs)"
  let ?bs = "replicate (length inp + 1) (Bin [])"
  have "wf_bin 0 ?b0"
    unfolding wf_bin_def wf_item_def using valid_rules by (auto simp: init_item_def)
  moreover have "wf_bins (Bins ?bs)"
    unfolding wf_bins_def wf_bin_def using less_Suc_eq_0_disj by force
  ultimately show ?thesis
    using wf_bins_app_bins unfolding wf_bin_def by (simp add: Init_it_def)
qed

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
  shows "\<forall>y \<in> set (Scan_it k a x bs). wf_item y \<and> item_end y = (k+1)" 
  using wf_bins_Scan_it'[OF assms(1-3) _ assms(5)] 
  by (metis List.list.set(1,2) Scan_it_def empty_iff insert_iff)

lemma wf_bins_Predict_it:
  assumes "wf_bins bs" "k < length (bins bs)" "k \<le> length inp"
  shows "\<forall>y \<in> set (Predict_it k X bs). wf_item y \<and> item_end y = k"
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
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof (cases "\<not> length (items (bins bs ! k)) \<le> i")
    case True
    let ?x = "items (bins bs ! k) ! i"
    have "?x \<in> set_bin (bins bs ! k)"
      using True set_bin_conv_set by simp
    thus ?thesis
      using True 1 wf_bins_Scan_it wf_bins_Predict_it wf_bins_Complete_it
            wf_bins_app_bins length_bins_app_bins
      by (auto simp: Let_def split: option.split)
  qed (auto simp: "1.prems"(1))
qed

lemma wf_bins_\<pi>_it:
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> k \<le> length inp \<Longrightarrow> wf_bins (\<pi>_it k bs)"
  using \<pi>_it_def wf_bins_\<pi>_it' by presburger

lemma wf_bins_\<I>_it:
  "k \<le> length inp \<Longrightarrow> wf_bins (\<I>_it k)"
  by (induction k) (auto simp: wf_bins_Init_it wf_bins_\<pi>_it length_bins_Init_it length_bins_\<I>_it)

lemma wf_bins_\<II>_it:
  "wf_bins \<II>_it"
  unfolding \<II>_it_def using wf_bins_\<I>_it length_bins_Init_it by auto

subsection \<open>Soundness\<close>

lemma Init_it_eq_Init:
  "set_bins Init_it = Init"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS>) rules"
  let ?b0 = "map (\<lambda>r. init_item r 0) ?rs"
  let ?bs = "Bins (replicate (length inp + 1) (Bin []))"
  have "set_bins ?bs = {}"
    unfolding set_bins_def set_bins_upto_def set_bin_conv_set set_bin_upto_def
    by (auto simp del: replicate_Suc)
  hence "set_bins Init_it = set ?b0"
    using Init_it_def set_bins_app_bins by simp
  thus ?thesis
    unfolding Init_def rule_head_def using valid_rules by auto
qed

lemma Scan_it_sub_Scan:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some a"
  shows "set (Scan_it k a x bs) \<subseteq> Scan k I"
proof standard
  fix y
  assume *: "y \<in> set (Scan_it k a x bs)"
  have "x \<in> bin I k"
    using kth_bin_in_bins assms(1-4) set_bin_conv_set wf_bin_def wf_bins_def bin_def by blast
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
  shows "set (Predict_it k X bs) \<subseteq> Predict k I"
proof standard
  fix y
  assume *: "y \<in> set (Predict_it k X bs)"
  have "x \<in> bin I k"
    using kth_bin_in_bins assms(1-4) set_bin_conv_set wf_bin_def wf_bins_def bin_def by blast
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
    using kth_bin_in_bins assms set_bin_conv_set wf_bin_def wf_bins_def bin_def by blast
  let ?orig = "bins bs ! item_origin y"
  let ?xs = "filter (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"
  have "item_origin y < length (bins bs)"
    using set_bin_conv_set wf_bins_def wf_bin_def wf_item_def assms(1,3,4) by force
  hence "\<forall>z \<in> set ?xs. z \<in> bin I (item_origin y)"
     using wf_bin_def wf_bins_def bin_def assms kth_bin_in_bins set_bin_conv_set by fastforce
  then obtain z where "x = inc_item z k" "next_symbol z = Some (item_rule_head y)" "z \<in> bin I (item_origin y)"
    using * Complete_it_def by auto
  thus "x \<in> Complete k I"
    using \<open>y \<in> bin I k\<close> assms(5) unfolding Complete_def next_symbol_def by (auto split: if_splits)
qed

lemma \<pi>_it'_sub_\<pi>:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "length (bins bs) = length inp + 1" "k < length (bins bs)"
  shows "set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k I"
  using assms
proof (induction k bs i arbitrary: I rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof (cases "i \<ge> length (items (bins bs ! k)) ")
    case True
    thus ?thesis
      using "1.prems" \<pi>_mono by auto
  next
    case False
    let ?x = "items (bins bs ! k) ! i"
    have x_in_kth_bin: "?x \<in> set_bin (bins bs ! k)"
      using False set_bin_conv_set by auto
    show ?thesis
    proof cases
      assume *: "next_symbol ?x = None"
      hence "set_bins (app_bins bs k (Complete_it k ?x bs)) \<subseteq> I \<union> Complete k I"
        using set_bins_app_bins "1.prems"(1,2,4) Complete_it_sub_Complete x_in_kth_bin by blast
      moreover have "wf_bins (app_bins bs k (Complete_it k (items (bins bs ! k) ! i) bs))"
        using "1.prems"(1,4) wf_bins_Complete_it wf_bins_app_bins x_in_kth_bin by presburger
      ultimately have "set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k (I \<union> Complete k I)"
        using False * \<pi>_it'_simps(2) 1 length_bins_app_bins by (auto simp del: \<pi>_it'.simps)
      thus ?thesis
        using Complete_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
    next
      assume *: "\<not> next_symbol ?x = None"
      then obtain a where a_def: "next_symbol ?x = Some a"
        by blast
      show ?thesis
      proof cases
        assume #: "is_terminal a"
        {
          assume "k < length inp"
          hence "set_bins (app_bins bs (k+1) (Scan_it k a ?x bs)) \<subseteq> I \<union> Scan k I"
            using set_bins_app_bins Scan_it_sub_Scan[OF "1.prems"(1,2) x_in_kth_bin] a_def "1.prems"(2,3) by auto
          moreover have "wf_bins (app_bins bs (k+1) (Scan_it k a ?x bs))"
            using "1.prems"(1,4) wf_bins_Scan_it wf_bins_app_bins x_in_kth_bin * \<open>k < length inp\<close> less_or_eq_imp_le by presburger         
          ultimately have "set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k (I \<union> Scan k I)"
            using a_def # False \<pi>_it'_simps(3) \<open>k < length inp\<close> length_bins_app_bins 1 by (auto simp del: \<pi>_it'.simps)
          hence ?thesis
            using Scan_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
        }
        hence "k < length inp \<Longrightarrow> ?thesis" .
        {
          assume "\<not> k < length inp"
          hence "set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k (I \<union> Scan k I)"
            using a_def # False \<pi>_it'_simps(4) Scan_def 1 by simp
          hence ?thesis
            using Scan_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
        }
        thus ?thesis
          using \<open>k < length inp \<Longrightarrow> ?thesis\<close> by blast
      next
        assume #: "\<not> is_terminal a"
        have "set_bins (app_bins bs k (Predict_it k a bs)) \<subseteq> I \<union> Predict k I"
          using set_bins_app_bins Predict_it_sub_Predict x_in_kth_bin a_def "1.prems" by blast
        moreover have "wf_bins (app_bins bs k (Predict_it k a bs))"
          using "1.prems"(1,4) wf_bins_Predict_it wf_bins_app_bins wf_bins_kth_bin wf_item_def x_in_kth_bin by metis
        ultimately have "set_bins (\<pi>_it' k bs i)  \<subseteq> \<pi> k (I \<union> Predict k I)"
          using False a_def # \<pi>_it'_simps(5) 1 length_bins_app_bins by simp
        thus ?thesis
          using Predict_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
      qed
    qed
  qed
qed

lemma \<pi>_it_sub_\<pi>:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "length (bins bs) = length inp + 1" "k < length (bins bs)"
  shows "set_bins (\<pi>_it k bs) \<subseteq> \<pi> k I"
  using assms \<pi>_it'_sub_\<pi> \<pi>_it_def by metis

lemma \<I>_it_sub_\<I>:
  "k < length (bins Init_it) \<Longrightarrow> set_bins (\<I>_it k) \<subseteq> \<I> k"
proof (induction k)
  case 0
  thus ?case
    by (simp add: Init_it_eq_Init \<pi>_it_sub_\<pi> length_bins_Init_it wf_bins_Init_it)
next
  case (Suc k)
  hence "set_bins (\<I>_it k) \<subseteq> \<I> k"
    by (simp add: Suc_lessD)
  moreover have "Suc k < length (bins (\<I>_it k))"
    using length_bins_\<I>_it Suc.prems by force
  ultimately show ?case
    using \<pi>_it_sub_\<pi> length_bins_Init_it length_bins_\<I>_it Suc.prems(1) wf_bins_\<I>_it by simp
qed

lemma \<II>_it_sub_\<II>:
  "set_bins \<II>_it \<subseteq> \<II>"
  using \<I>_it_sub_\<I> \<II>_def \<II>_it_def length_bins_Init_it by auto

subsection \<open>Completeness\<close>

subsubsection \<open>Auxiliary\<close>

lemma Scan_bin_absorb:
  "Scan k (bin I k) = Scan k I"
  unfolding Scan_def bin_def by simp

lemma Predict_bin_absorb:
  "Predict k (bin I k) = Predict k I"
  unfolding Predict_def bin_def by simp

lemma Complete_bin_absorb:
  "Complete k (bin I k) \<subseteq> Complete k I"
  unfolding Complete_def bin_def by blast

lemma AUX1:
  assumes "k < length (bins bs)" "0 < length (bins bs)"
  shows "set_bins_upto bs k i \<subseteq> set_bins bs"
  unfolding set_bins_def set_bins_upto_def using assms
  apply (auto, force)
  by (metis Suc_pred assms(2) in_mono less_antisym set_bin_def set_bin_upto_sub_set_bin)

lemma BUX11:
  assumes "x \<in> set_bins bs" "0 < length (bins bs)"
  shows "\<exists>k < length (bins bs). x \<in> set_bin (bins bs ! k)"
proof -
  let ?k = "length (bins bs) - 1"
  let ?i = "length (items (bins bs ! (length (bins bs) - 1)))"
  have *: "x \<in> set_bins_upto bs ?k ?i"
    using assms unfolding set_bins_def by blast
  thus ?thesis
  proof cases
    assume "x \<in> \<Union> { set_bin b | b l. l < ?k \<and> b = bins bs ! l }"
    then obtain k where "k < ?k" "x \<in> set_bin (bins bs ! k)"
      by blast
    thus ?thesis
      using diff_le_self less_le_trans by blast
  next
    assume "\<not> x \<in> \<Union> { set_bin b | b l. l < ?k \<and> b = bins bs ! l }"
    hence "x \<in> set_bin_upto (bins bs ! ?k) ?i"
      using * unfolding set_bins_upto_def by blast
    hence 0: "x \<in> set_bin (bins bs ! ?k)"
      using set_bin_upto_sub_set_bin by blast
    thus ?thesis
      by (meson assms(2) diff_less zero_less_one)
  qed
qed

lemma BUX1:
  assumes "wf_bins bs" "x \<in> set_bins bs" "item_end x = k"
  shows "x \<in> set_bin (bins bs ! k)"
  using BUX11 assms wf_bins_kth_bin wf_bins_def by blast

lemma AUX2:
  assumes "wf_bins bs" "k < length (bins bs)" "i \<ge> length (items (bins bs ! k))"
  shows "bin (set_bins_upto bs k i) k = bin (set_bins bs) k"
  using assms
  unfolding set_bins_upto_def set_bins_def set_bin_upto_def bin_def set_bin_conv_set
  apply (auto simp: nth_list_update)
  apply (metis Orderings.order_class.dual_order.strict_trans less_not_refl set_bin_conv_set wf_bins_kth_bin)
  apply (metis One_nat_def Suc_eq_plus1 Suc_lessI diff_Suc_1 in_set_conv_nth less_diff_conv)
  apply (metis One_nat_def Orderings.order_class.order.strict_trans2 Suc_eq_plus1 Suc_lessD in_set_conv_nth less_diff_conv set_bin_conv_set wf_bins_kth_bin)
  by (smt (verit, best) wf_bins_kth_bin diff_less less_Suc_eq less_le_trans nth_mem set_bin_conv_set wf_bins_def)

lemma AUX31:
  "i < length (items (bins bs ! k)) \<Longrightarrow> set_bins_upto bs k (i+1) = set_bins_upto bs k i \<union> { items (bins bs ! k) ! i }"
  unfolding set_bins_upto_def set_bin_upto_def using less_Suc_eq by auto

lemma AUX32:
  "i \<ge> length (items (bins bs ! k)) \<Longrightarrow> set_bins_upto bs k (i+1) = set_bins_upto bs k i"
  unfolding set_bins_upto_def set_bin_upto_def by auto

lemma AUX3:
  "set_bins_upto bs k (i+1) \<subseteq> set_bins_upto bs k i \<union> { items (bins bs ! k) !i }"
  using AUX31 AUX32 leI by blast

subsubsection \<open>Main lemmas\<close>

lemma A:
  assumes "k < length (bins bs)" "length (bins bs) = length inp + 1"
  shows "set_bins bs \<subseteq> set_bins (\<pi>_it' k bs i)"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof (cases "i < length (items (bins bs ! k))")
    case True
    let ?x = "items (bins bs ! k) ! i"
    show ?thesis
    proof cases
      assume "next_symbol ?x = None"
      thus ?thesis
        using 1 True \<pi>_it'_simps(2) length_bins_app_bins set_bins_app_bins by (simp add: Let_def)
    next
      assume "\<not> next_symbol ?x = None"
      then obtain a where "next_symbol ?x = Some a"
        by blast
      thus ?thesis
        using 1 True \<pi>_it'_simps(3,4,5) length_bins_app_bins set_bins_app_bins
        by (cases "is_terminal a"; cases "k < length inp") (simp_all add: Let_def)
    qed
  qed simp
qed

lemma B:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "Scan k (set_bins_upto bs k i) \<subseteq> set_bins bs"
  shows "Scan k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    hence "set_bins (\<pi>_it' k bs i) = set_bins bs"
      by simp
    moreover have "bin (set_bins bs) k = bin (set_bins_upto bs k i) k"
      using AUX2 a1 "1.prems"(1,2) by blast
    ultimately show ?thesis
      using Scan_bin_absorb "1.prems"(3,4) by metis
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    have x_in_kth_bin: "?x \<in> set_bin (bins bs ! k)"
      using a1 set_bin_conv_set by auto
    have x_in_kth_bin': "?x \<in> bin (set_bins bs) k"
      using "1.prems"(1,2) bin_def kth_bin_in_bins wf_bins_kth_bin x_in_kth_bin by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
        using a1 a2 \<pi>_it'_simps(2) by blast
      have "i < length (items (bins ?bs' ! k))"
        using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
      have "wf_bins ?bs'"
        using "1.prems"(1,2) wf_bins_Complete_it wf_bins_app_bins x_in_kth_bin by presburger
      moreover have "k < length (bins ?bs')"
        using "1.prems"(2) length_bins_app_bins by simp
      moreover have "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
      proof -
        have 0: "?x = items (bins ?bs' ! k) ! i"
          using "1.prems"(2) kth_bin_nth_id a1 by simp
        have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
          using "1.prems"(2) a1 set_bins_upto_kth_nth_id by simp
        have "Scan k (set_bins_upto ?bs' k (i + 1)) = Scan k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
          using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
        also have "... = Scan k (set_bins_upto bs k i \<union> {?x})"
          using 0 1 by simp
        also have "... = Scan k (set_bins_upto bs k i) \<union> Scan k {?x}"
          using Scan_Un by blast
        also have "... \<subseteq> set_bins bs \<union> Scan k {?x}"
          using "1.prems"(3,4) by blast
        also have "... = set_bins bs"
          using x_in_kth_bin' a2 unfolding Scan_def bin_def by simp
        finally show ?thesis
          using "1.prems"(2) set_bins_app_bins by blast
      qed
      ultimately have 1: "Scan k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
        using "1.IH" a1 a2 "1.prems"(3) length_bins_app_bins by auto
      show ?thesis
        using 0 1 "1.prems"(2) set_bins_app_bins Scan_Un by simp
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) by blast
          have "i < length (items (bins ?bs' ! k))"
            using a1 "1.prems"(2) length_kth_bin_app_bins app_bins_def by auto
          have "wf_bins ?bs'"
            using "1.prems"(1,2) wf_bins_Scan_it wf_bins_app_bins x_in_kth_bin a2 a4 less_or_eq_imp_le by presburger
          moreover have "k < length (bins ?bs')"
            using "1.prems"(2) length_bins_app_bins by simp
          moreover have "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
          proof -
            have 0: "?x = items (bins ?bs' ! k) ! i"
              using "1.prems"(2) kth_bin_nth_id a1 by (simp add: app_bins_def)
            have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
              using "1.prems"(2,3) a1 set_bins_upto_kth_nth_id a4 by auto
            have "Scan k (set_bins_upto ?bs' k (i + 1)) = Scan k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
              using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
            also have "... = Scan k (set_bins_upto bs k i \<union> {?x})"
              using 0 1 by simp
            also have "... = Scan k (set_bins_upto bs k i) \<union> Scan k {?x}"
              using Scan_Un by blast
            also have "... \<subseteq> set_bins bs \<union> Scan k {?x}"
              using "1.prems"(3,4) by blast
            finally have 2: "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs \<union> Scan k {?x}" .
            show ?thesis
            proof cases
              assume a5: "inp!k = a"
              hence "Scan k {?x} = {inc_item ?x (k+1)}"
                unfolding Scan_def using a_def x_in_kth_bin' a4 bin_def by auto
              hence "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs \<union> {inc_item ?x (k+1)}"
                using 2 by blast
              also have "... = set_bins bs \<union> set (Scan_it k a ?x bs)"
                unfolding Scan_it_def using a4 a5 by simp
              also have "... = set_bins ?bs'"
                using set_bins_app_bins "1.prems"(3) a4 by force
              finally show ?thesis .
            next
              assume a5: "\<not> inp!k = a"
              hence "Scan k {?x} = {}"
                unfolding Scan_def using bin_def a_def by force
              hence "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs"
                using 2 by blast
              also have "... \<subseteq> set_bins ?bs'"
                using "1.prems"(3) a4 set_bins_app_bins by simp
              finally show ?thesis .
            qed
          qed
          ultimately have 1: "Scan k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
            using "1.IH" a1 a2 a3 a4 a_def "1.prems"(3) length_bins_app_bins by auto
          show ?thesis
            using 0 1 "1.prems"(3) a4 set_bins_app_bins Scan_Un by simp
        next
          assume a4: "\<not> k < length inp"
          thus ?thesis
            using Scan_def by blast
        qed
      next
        assume a3: "\<not> is_terminal a"
        hence "k \<ge> length inp \<or> \<not> inp!k = a"
          using valid_inp unfolding is_terminal_def by force
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have "i < length (items (bins ?bs' ! k))"
          using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
        have "wf_bins ?bs'"
          using "1.prems"(1,2) wf_bins_Predict_it wf_bins_app_bins x_in_kth_bin by (metis wf_bins_kth_bin wf_item_def)
        moreover have "k < length (bins ?bs')"
          using "1.prems"(2) length_bins_app_bins by simp
        moreover have "Scan k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
        proof -
          have 0: "?x = items (bins ?bs' ! k) ! i"
            using "1.prems"(2) kth_bin_nth_id a1 by simp
          have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
            using "1.prems"(2) a1 set_bins_upto_kth_nth_id by simp
          have "Scan k (set_bins_upto ?bs' k (i + 1)) = Scan k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
            using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
          also have "... = Scan k (set_bins_upto bs k i \<union> {?x})"
            using 0 1 by simp
          also have "... = Scan k (set_bins_upto bs k i) \<union> Scan k {?x}"
            using Scan_Un by blast
          also have "... \<subseteq> set_bins bs \<union> Scan k {?x}"
            using "1.prems"(3,4) by blast
          also have "... = set_bins bs"
            unfolding Scan_def bin_def using \<open>length inp \<le> k \<or> inp ! k \<noteq> a\<close> a_def by auto
          finally show ?thesis
            using "1.prems"(2) set_bins_app_bins by blast
        qed
        ultimately have 1: "Scan k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
          using "1.IH" a1 a2 a3 a_def "1.prems"(3) length_bins_app_bins by auto
        show ?thesis
          using 0 1 "1.prems"(2) set_bins_app_bins Scan_Un by simp
      qed
    qed
  qed
qed

lemma C:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "Predict k (set_bins_upto bs k i) \<subseteq> set_bins bs"
  shows "Predict k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    hence "set_bins (\<pi>_it' k bs i) = set_bins bs"
      by simp
    moreover have "bin (set_bins bs) k = bin (set_bins_upto bs k i) k"
      using AUX2 a1 "1.prems"(1,2) by blast
    ultimately show ?thesis
      using Predict_bin_absorb "1.prems"(3,4) by metis
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    have x_in_kth_bin: "?x \<in> set_bin (bins bs ! k)"
      using a1 set_bin_conv_set by auto
    have x_in_kth_bin': "?x \<in> bin (set_bins bs) k"
      using "1.prems"(1,2) bin_def kth_bin_in_bins wf_bins_kth_bin x_in_kth_bin by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
        using a1 a2 \<pi>_it'_simps(2) by blast
      have "i < length (items (bins ?bs' ! k))"
        using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
      have "wf_bins ?bs'"
        using "1.prems"(1,2) wf_bins_Complete_it wf_bins_app_bins x_in_kth_bin by presburger
      moreover have "k < length (bins ?bs')"
        using "1.prems"(2) length_bins_app_bins by simp
      moreover have "Predict k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
      proof -
        have 0: "?x = items (bins ?bs' ! k) ! i"
          using "1.prems"(2) kth_bin_nth_id a1 by simp
        have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
          using "1.prems"(2) a1 set_bins_upto_kth_nth_id by simp
        have "Predict k (set_bins_upto ?bs' k (i + 1)) = Predict k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
          using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
        also have "... = Predict k (set_bins_upto bs k i \<union> {?x})"
          using 0 1 by simp
        also have "... = Predict k (set_bins_upto bs k i) \<union> Predict k {?x}"
          using Predict_Un by blast
        also have "... \<subseteq> set_bins bs \<union> Predict k {?x}"
          using "1.prems"(3,4) by blast
        also have "... = set_bins bs"
          using x_in_kth_bin' a2 unfolding Predict_def bin_def by simp
        finally show ?thesis
          using "1.prems"(2) set_bins_app_bins by blast
      qed
      ultimately have 1: "Predict k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
        using "1.IH" a1 a2 "1.prems"(3) length_bins_app_bins by auto
      show ?thesis
        using 0 1 "1.prems"(2) set_bins_app_bins Predict_Un by simp
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) by blast
          have "i < length (items (bins ?bs' ! k))"
            using a1 "1.prems"(2) length_kth_bin_app_bins app_bins_def by auto
          have "wf_bins ?bs'"
            using "1.prems"(1,2) wf_bins_Scan_it wf_bins_app_bins x_in_kth_bin a2 a4 less_or_eq_imp_le by presburger
          moreover have "k < length (bins ?bs')"
            using "1.prems"(2) length_bins_app_bins by simp
          moreover have "Predict k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
          proof -
            have 0: "?x = items (bins ?bs' ! k) ! i"
              using "1.prems"(2) kth_bin_nth_id a1 by (simp add: app_bins_def)
            have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
              using "1.prems"(2,3) a1 set_bins_upto_kth_nth_id a4 by auto
            have "Predict k (set_bins_upto ?bs' k (i + 1)) = Predict k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
              using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
            also have "... = Predict k (set_bins_upto bs k i \<union> {?x})"
              using 0 1 by simp
            also have "... = Predict k (set_bins_upto bs k i) \<union> Predict k {?x}"
              using Predict_Un by blast
            also have "... \<subseteq> set_bins bs \<union> Predict k {?x}"
              using "1.prems"(3,4) by blast
            also have "... = set_bins bs"
              unfolding Predict_def bin_def rule_head_def
              using a_def a3 validRules valid_rules is_terminal_nonterminal by force
            finally show ?thesis
              using "1.prems"(3) a4 set_bins_app_bins by auto
          qed
          ultimately have 1: "Predict k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
            using "1.IH" a1 a2 a3 a4 a_def "1.prems"(3) length_bins_app_bins by auto
          show ?thesis
            using 0 1 "1.prems"(3) a4 set_bins_app_bins Predict_Un by simp
        next
          assume a4: "\<not> k < length inp"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(4) by blast
          have "Predict k (set_bins_upto bs k (i + 1)) \<subseteq> set_bins bs"
          proof -
            have "Predict k (set_bins_upto bs k (i + 1)) = Predict k (set_bins_upto bs k i \<union> {items (bins bs ! k) ! i})"
              using AUX31 a1 by auto
            moreover have "Predict k (set_bins_upto bs k i \<union> {items (bins bs ! k) ! i}) = Predict k (set_bins_upto bs k i \<union> {?x})"
              using 0 1 by simp
            moreover have "Predict k (set_bins_upto bs k i \<union> {?x}) = Predict k (set_bins_upto bs k i) \<union> Predict k {?x}"
              using Predict_Un by fast
            moreover have "Predict k (set_bins_upto bs k i) \<union> Predict k {?x} \<subseteq> set_bins bs \<union> Predict k {?x}"
              using "1.prems"(4) by blast
            moreover have "set_bins bs \<union> Predict k {?x} = set_bins bs"
              unfolding Predict_def bin_def rule_head_def
              using a_def a3 validRules valid_rules is_terminal_nonterminal by force
            ultimately show ?thesis
              using "1.prems"(3) a4 set_bins_app_bins by simp
          qed
          hence 1: "Predict k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs (i + 1))"
            using 1 a1 a3 a4 a_def by auto
          show ?thesis
            using 0 1 "1.prems"(3) a4 set_bins_app_bins Predict_Un by simp
        qed
      next
        assume a3: "\<not> is_terminal a"
        hence "k \<ge> length inp \<or> \<not> inp!k = a"
          using valid_inp unfolding is_terminal_def by force
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have "i < length (items (bins ?bs' ! k))"
          using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
        have "wf_bins ?bs'"
          using "1.prems"(1,2) wf_bins_Predict_it wf_bins_app_bins x_in_kth_bin by (metis wf_bins_kth_bin wf_item_def)
        moreover have "k < length (bins ?bs')"
          using "1.prems"(2) length_bins_app_bins by simp
        moreover have "Predict k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
        proof -
          have 0: "?x = items (bins ?bs' ! k) ! i"
            using "1.prems"(2) kth_bin_nth_id a1 by simp
          have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
            using "1.prems"(2) a1 set_bins_upto_kth_nth_id by simp
          have "Predict k (set_bins_upto ?bs' k (i + 1)) = Predict k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
            using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
          also have "... = Predict k (set_bins_upto bs k i \<union> {?x})"
            using 0 1 by simp
          also have "... = Predict k (set_bins_upto bs k i) \<union> Predict k {?x}"
            using Predict_Un by blast
          also have "... \<subseteq> set_bins bs \<union> Predict k {?x}"
            using "1.prems"(3,4) by blast
          also have "... = set_bins bs \<union> set (Predict_it k a bs)"
            unfolding Predict_def bin_def Predict_it_def 
            using a_def valid_rules "1.prems"(1,2) wf_bins_kth_bin x_in_kth_bin by auto
          finally show ?thesis
            using "1.prems"(2) set_bins_app_bins by simp
        qed
        ultimately have 1: "Predict k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
          using "1.IH" a1 a2 a3 a_def "1.prems"(3) length_bins_app_bins by auto
        show ?thesis
          using 0 1 "1.prems"(2) set_bins_app_bins Predict_Un by simp
      qed
    qed
  qed
qed

definition bins_upto :: "items \<Rightarrow> nat \<Rightarrow> items" where
  "bins_upto I k = \<Union> { bin I l | l. l \<le> k }"

lemma set_bins_simp:
  "0 < length (bins bs) \<Longrightarrow> set_bins bs = \<Union> {set_bin (bins bs ! k) | k. k < length (bins bs)}"
  unfolding set_bins_def set_bins_upto_def set_bin_conv_set set_bin_upto_def
  apply auto
  apply (metis diff_le_self less_le_trans)
   apply (metis diff_less length_greater_0_conv nth_mem zero_less_Suc)
  by (metis diff_Suc_Suc diff_zero in_set_conv_nth lessE)

lemma set_bin_eq_bin:
  assumes "k < length (bins bs)" "wf_bins bs"
  shows "set_bin (bins bs ! k) = bin (set_bins bs) k"
  using assms unfolding set_bins_simp
  apply auto
  using wf_bins_kth_bin bin_def
  using kth_bin_in_bins apply fastforce
  by (simp add: BUX1 bin_def)

lemma Q1:
  assumes "k < length (bins bs)" "i \<ge> length (items (bins bs ! k))" "wf_bins bs"
  shows "set_bins_upto bs k i = bins_upto (set_bins bs) k"
proof -
  have "set_bins_upto bs k i = \<Union> {set_bin (bins bs ! l) |l. l < k} \<union> set_bin_upto (bins bs ! k) i"
    unfolding set_bins_upto_def by blast
  also have "... = \<Union> {set_bin (bins bs ! l) |l. l < k} \<union> set_bin (bins bs ! k)"
    using assms unfolding set_bin_upto_def set_bin_def by auto
  also have "... = \<Union> {set_bin (bins bs ! l) |l. l \<le> k}"
    apply (induction k)
     apply auto
     apply (metis less_imp_le)
    using nat_less_le by auto
  also have "... = \<Union> {bin (set_bins bs) l | l. l \<le> k }"
    using set_bin_eq_bin[OF _ assms(3)] assms(1) by auto
  finally show ?thesis
    using bins_upto_def by auto
qed

lemma Q2:
  "Scan k (bins_upto I k) = Scan k I"
  unfolding Scan_def bins_upto_def bin_def by blast

lemma Q3:
  "Predict k (bins_upto I k) = Predict k I"
  unfolding Predict_def bins_upto_def bin_def by blast

lemma Q4:
  "wf_items I \<Longrightarrow> Complete k (bins_upto I k) = Complete k I"
  unfolding Complete_def bins_upto_def bin_def wf_items_def wf_item_def by blast

lemma Q5:
  assumes "k < length (bins bs)" "i \<ge> length (items (bins bs ! k))" "wf_bins bs"
  shows "Complete k (set_bins bs) = Complete k (set_bins_upto bs k i)"
  using Q1 Q4 assms
  by (metis BUX11 wf_bins_def wf_bins_kth_bin wf_items_def)

lemma Q6:
  assumes "next_symbol z = Some a" "is_terminal a" "wf_items I" "wf_item z"
  shows "Complete k (I \<union> {z}) = Complete k I"
proof (rule ccontr)
  assume "Complete k (I \<union> {z}) \<noteq> Complete k I"
  hence "Complete k I \<subset> Complete k (I \<union> {z})"
    by (metis Complete_sub_mono Un_upper1 psubsetI)
  then obtain x y q where *:
    "q \<in> Complete k (I \<union> {z})" "q \<notin> Complete k I" "q = inc_item x k"
    "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by fast
  show False
  proof (cases "x = z")
    case True
    hence "next_symbol z = Some (item_rule_head y)"
      using *(7) by blast
    hence "item_rule_head y = a"
      using assms(1) by simp
    have "wf_item y"
      using *(5) assms(3,4) unfolding wf_items_def bin_def by blast
    hence "is_nonterminal (item_rule_head y)"
      unfolding wf_item_def item_rule_head_def rule_head_def using validRules by auto
    thus ?thesis
      using \<open>item_rule_head y = a\<close> assms(2) is_terminal_nonterminal by auto
  next
    case False
    hence "y = z"
      using * unfolding Complete_def bin_def by blast
    thus ?thesis
      using *(6) assms(1) next_symbol_def by auto
  qed
qed

lemma Q7:
  assumes "Complete k I \<subseteq> set_bins bs" "I \<subseteq> set_bins bs" "is_complete z" "wf_bins bs" "wf_item z"
  shows "Complete k (I \<union> {z}) \<subseteq> set_bins bs \<union> set (Complete_it k z bs)"
proof standard
  fix q
  assume "q \<in> Complete k (I \<union> {z})"
  then obtain x y where *:
    "q = inc_item x k" "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by blast
  consider (A) "x = z" | (B) "y = z" | "\<not> (x = z \<or> y = z)"
    by blast
  then show "q \<in> set_bins bs \<union> set (Complete_it k z bs)"
  proof cases
    case A
    then show ?thesis
      using *(5) assms(3) next_symbol_def by auto
  next
    case B
    have "x \<noteq> z"
      using "*"(5) assms(3) next_symbol_def by force
    hence "x \<in> bin I (item_origin y)"
      using "*"(2) bin_def by auto

    let ?orig = "bins bs ! item_origin z"
    let ?is = "filter (\<lambda>x. next_symbol x = Some (item_rule_head z)) (items ?orig)"

    have "bin I (item_origin z) \<subseteq> set_bin (bins bs ! item_origin z)"
      using BUX1 assms(2) assms(4) bin_def by blast
    hence "x \<in> set ?is"
      using "*"(5) B \<open>x \<in> bin I (item_origin y)\<close> set_bin_conv_set by (simp add: in_mono)
    then show ?thesis
      unfolding Complete_it_def *(1) by simp
  next
    case 3
    hence "x \<in> bin I (item_origin y)" "y \<in> bin I k"
      using *(2,3) unfolding bin_def by simp_all
    then show ?thesis
      using assms(1) *(1,4,5) unfolding Complete_def by blast
  qed
qed

lemma Q8:
  assumes "next_symbol z = Some a" "is_nonterminal a"
  assumes "sound_items I" "item_end z = k"
  shows "Complete k (I \<union> {z}) = Complete k I"
proof (rule ccontr)
  assume "Complete k (I \<union> {z}) \<noteq> Complete k I"
  hence "Complete k I \<subset> Complete k (I \<union> {z})"
    by (metis Complete_sub_mono Un_upper1 psubsetI)
  then obtain x y q where *:
    "q \<in> Complete k (I \<union> {z})" "q \<notin> Complete k I" "q = inc_item x k"
    "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by fast
  consider (A) "x = z" | (B) "y = z" | "\<not> (x = z \<or> y = z)"
    by blast
  then show False
  proof cases
    case A
    have 0: "item_origin y = k"
      using "*"(4) A assms(4) bin_def by auto
    have 1: "item_end y = k"
      using "*"(5) bin_def by blast
    have "y \<noteq> z"
      using "*"(6) assms(1) next_symbol_def by fastforce
    hence "sound_item y"
      using "*"(5) assms(3) bin_def sound_items_def by auto
    hence "derives [a] (slice k k inp @ item_\<beta> y)"
      unfolding sound_item_def using 0 1 "*"(7) A assms(1) by auto
    hence "derives [a] (slice k k inp)"
      using "*"(6) is_complete_def item_\<beta>_def by auto
    hence "derives [a] []"
      by (simp add: slice_empty)
    then show ?thesis
      using assms(2) is_nonterminal_def nonempty_deriv by blast
  next
    case B
    then show ?thesis
      using "*"(6) assms(1) next_symbol_def by force
  next
    case 3
    hence "x \<in> bin I (item_origin y)" "y \<in> bin I k"
      using *(2,4,5) unfolding Complete_def bin_def by simp_all
    then show ?thesis
      using "*"(2) "*"(3) "*"(6) "*"(7) Complete_def by blast
  qed
qed

lemma S1:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some a"
  assumes "wf_items I" "sound_items I"
  shows "sound_items (set (Scan_it k a x bs))"
  using sound_Scan Scan_it_sub_Scan assms by (meson sound_items_def subsetD)

lemma S2:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some X"
  assumes "sound_items I"
  shows "sound_items (set (Predict_it k X bs))"
  using sound_Predict Predict_it_sub_Predict sound_items_def assms by (meson subsetD)

lemma S3:
  assumes "wf_bins bs" "set_bins bs \<subseteq> I" "y \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol y = None"
  assumes "wf_items I" "sound_items I"
  shows "sound_items (set (Complete_it k y bs))"
  using sound_Complete Complete_it_sub_Complete sound_items_def assms by (meson subsetD)

lemma S4:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "sound_items (set_bins bs)"
  shows "sound_items (set_bins (\<pi>_it' k bs i))"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    thus ?thesis
      using "1.prems"(4) by simp
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    have x_in_kth_bin: "?x \<in> set_bin (bins bs ! k)"
      using a1 set_bin_conv_set by auto
    have x_in_kth_bin': "?x \<in> bin (set_bins bs) k"
      using "1.prems"(1,2) bin_def kth_bin_in_bins wf_bins_kth_bin x_in_kth_bin by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
        using a1 a2 \<pi>_it'_simps(2) by blast
      have 1: "sound_items (set (Complete_it k ?x bs))"
        using S3[OF "1.prems"(1) _ x_in_kth_bin "1.prems"(2)]
        by (meson "1.prems"(1,4) BUX11 wf_bins_kth_bin a2 subset_refl wf_bins_def wf_items_def)
      have "i < length (items (bins ?bs' ! k))"
        using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
      have "wf_bins ?bs'"
        using "1.prems"(1,2) wf_bins_Complete_it wf_bins_app_bins x_in_kth_bin by presburger
      moreover have "k < length (bins ?bs')"
        using "1.prems"(2) length_bins_app_bins by simp
      moreover have "sound_items (set_bins ?bs')"
        using 1 "1.prems"(2,4) set_bins_app_bins sound_items_def by auto
      ultimately have 1: "sound_items (set_bins (\<pi>_it' k ?bs' (i + 1)))"
        using "1.IH" a1 a2 "1.prems"(3) length_bins_app_bins by auto
      show ?thesis
        using 0 1 by presburger
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) by blast
          have 1: "sound_items (set (Scan_it k a ?x bs))"
            using S1[OF "1.prems"(1) _ x_in_kth_bin "1.prems"(2) a_def]
            by (meson "1.prems"(1,4) BUX11 wf_bins_kth_bin subset_refl wf_bins_def wf_items_def)
          have "i < length (items (bins ?bs' ! k))"
            using a1 "1.prems"(2) length_kth_bin_app_bins app_bins_def by auto
          have "wf_bins ?bs'"
            using "1.prems"(1,2) wf_bins_Scan_it wf_bins_app_bins x_in_kth_bin a2 a4 less_or_eq_imp_le by presburger
          moreover have "k < length (bins ?bs')"
            using "1.prems"(2) length_bins_app_bins by simp
          moreover have "sound_items (set_bins ?bs')"
            using "1" "1.prems"(3,4) a4 set_bins_app_bins sound_items_def by fastforce
          ultimately have 1: "sound_items (set_bins (\<pi>_it' k ?bs' (i + 1)))"
            using "1.IH" a1 a2 a3 a4 a_def "1.prems"(3) length_bins_app_bins by auto
          show ?thesis
            using 0 1 by simp
        next
          assume a4: "\<not> k < length inp"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(4) by blast
          hence 1: "sound_items (set_bins (\<pi>_it' k bs (i + 1)))"
            using 1 a3 a4 a_def by fastforce
          show ?thesis
            using 0 1 by simp
        qed
      next
        assume a3: "\<not> is_terminal a"
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have "i < length (items (bins ?bs' ! k))"
          using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
        have "wf_bins ?bs'"
          using "1.prems"(1,2) wf_bins_Predict_it wf_bins_app_bins x_in_kth_bin by (metis wf_bins_kth_bin wf_item_def)
        moreover have "k < length (bins ?bs')"
          using "1.prems"(2) length_bins_app_bins by simp
        moreover have "sound_items (set_bins ?bs')"
          by (metis "1.prems"(1,2,4) S2 UnE Un_upper1 a_def set_bins_app_bins sound_items_def x_in_kth_bin)
        ultimately have 1: "sound_items (set_bins (\<pi>_it' k ?bs' (i + 1)))"
          using "1.IH" a1 a2 a3 a_def "1.prems"(3) length_bins_app_bins by auto
        show ?thesis
          using 0 1 by simp
      qed
    qed
  qed
qed

lemma S5:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "sound_items (set_bins bs)"
  shows "sound_items (set_bins (\<pi>_it k bs))"
  using S4 assms by (metis \<pi>_it_def)

lemma D:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "Complete k (set_bins_upto bs k i) \<subseteq> set_bins bs"
  assumes "sound_items (set_bins bs)"
  shows "Complete k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    hence "set_bins (\<pi>_it' k bs i) = set_bins bs"
      by simp
    moreover have "Complete k (set_bins bs) = Complete k (set_bins_upto bs k i)"
      using a1 "1.prems"(1,2) Q5 by force
    ultimately show ?thesis
      using "1.prems"(4) by blast
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    have x_in_kth_bin: "?x \<in> set_bin (bins bs ! k)"
      using a1 set_bin_conv_set by auto
    have x_in_kth_bin': "?x \<in> bin (set_bins bs) k"
      using "1.prems"(1,2) bin_def kth_bin_in_bins wf_bins_kth_bin x_in_kth_bin by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
        using a1 a2 \<pi>_it'_simps(2) by blast
      have 1: "sound_items (set (Complete_it k ?x bs))"
        using S3[OF "1.prems"(1) _ x_in_kth_bin "1.prems"(2)]
        by (meson "1.prems"(1,5) BUX11 a2 subset_refl wf_bins_def wf_bins_kth_bin wf_items_def)
      have "i < length (items (bins ?bs' ! k))"
        using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
      have "wf_bins ?bs'"
        using "1.prems"(1,2) wf_bins_Complete_it wf_bins_app_bins x_in_kth_bin by presburger
      moreover have "k < length (bins ?bs')"
        using "1.prems"(2) length_bins_app_bins by simp
      moreover have "sound_items (set_bins ?bs')"
        using 1 "1.prems"(2,5) set_bins_app_bins sound_items_def by auto
      moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
      proof -
        have 0: "?x = items (bins ?bs' ! k) ! i"
          using "1.prems"(2) kth_bin_nth_id a1 by simp
        have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
          using "1.prems"(2) a1 set_bins_upto_kth_nth_id by simp
        have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
          using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
        also have "... = Complete k (set_bins_upto bs k i \<union> {?x})"
          using 0 1 by simp
        also have "... \<subseteq> set_bins bs \<union> set (Complete_it k ?x bs)"
          using "1.prems"(4)
          by (metis "1.prems"(1,2) AUX1 Option.option.discI Q7 a2 next_symbol_def wf_bins_def wf_bins_kth_bin x_in_kth_bin)
        finally show ?thesis
          using "1.prems"(2) set_bins_app_bins by blast
      qed
      ultimately have 1: "Complete k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
        using "1.IH" a1 a2 "1.prems"(3) length_bins_app_bins by auto
      show ?thesis
        using 0 1 "1.prems"(2) set_bins_app_bins Complete_sub_mono
        by (metis Orderings.order_class.order.trans inf_sup_ord(3))
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) by blast
          have 1: "sound_items (set (Scan_it k a ?x bs))"
            using S1[OF "1.prems"(1) _ x_in_kth_bin "1.prems"(2) a_def]
            by (metis "1.prems"(1,4,5) BUX11 wf_bins_kth_bin Lattices.semilattice_sup_class.sup.orderE Un_upper1 wf_bins_def wf_items_def)
          have "i < length (items (bins ?bs' ! k))"
            using a1 "1.prems"(2) length_kth_bin_app_bins app_bins_def by auto
          have "wf_bins ?bs'"
            using "1.prems"(1,2) wf_bins_Scan_it wf_bins_app_bins x_in_kth_bin a2 a4 less_or_eq_imp_le by presburger
          moreover have "k < length (bins ?bs')"
            using "1.prems"(2) length_bins_app_bins by simp
          moreover have "sound_items (set_bins ?bs')"
            using 1 "local.1.prems"(3) "local.1.prems"(5) a4 set_bins_app_bins sound_items_def by auto
          moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
          proof -
            have 0: "?x = items (bins ?bs' ! k) ! i"
              using "1.prems"(2) kth_bin_nth_id a1 by (simp add: app_bins_def)
            have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
              using "1.prems"(2,3) a1 set_bins_upto_kth_nth_id a4 by auto
            have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
              using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
            also have "... = Complete k (set_bins_upto bs k i \<union> {?x})"
              using 0 1 by simp
            also have "... = Complete k (set_bins_upto bs k i)"
              using Q6 a3 a_def
              by (meson "1.prems"(1,2) AUX1 BUX11 subset_iff wf_bins_def wf_bins_kth_bin wf_items_def x_in_kth_bin)
            also have "... \<subseteq> set_bins bs"
              using "1.prems"(4) by blast
            finally show ?thesis
              using "1.prems"(3) a4 set_bins_app_bins by auto
          qed
          ultimately have 1: "Complete k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
            using "1.IH" a1 a2 a3 a4 a_def "1.prems"(3) length_bins_app_bins by auto
          show ?thesis
            using 0 1 "1.prems"(3) a4 set_bins_app_bins Complete_sub_mono
            by (metis Un_upper1 add_less_mono1 subset_trans)
        next
          assume a4: "\<not> k < length inp"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(4) by blast
          have "Complete k (set_bins_upto bs k (i + 1)) \<subseteq> set_bins bs"
          proof -
            have "Complete k (set_bins_upto bs k (i + 1)) = Complete k (set_bins_upto bs k i \<union> {items (bins bs ! k) ! i})"
              using AUX31 a1 by auto
            moreover have "Complete k (set_bins_upto bs k i \<union> {items (bins bs ! k) ! i}) = Complete k (set_bins_upto bs k i \<union> {?x})"
              using 0 1 by simp
            moreover have "Complete k (set_bins_upto bs k i \<union> {?x}) = Complete k (set_bins_upto bs k i)"
              using Q6 a3 a_def
              by (meson "1.prems"(1,2) AUX1 BUX11 subset_iff wf_bins_def wf_bins_kth_bin wf_items_def x_in_kth_bin)
            moreover have "Complete k (set_bins_upto bs k i) \<subseteq> set_bins bs"
              using "1.prems"(4) by blast
            ultimately show ?thesis
              using "1.prems"(3) a4 set_bins_app_bins by simp
          qed
          hence 1: "Complete k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs (i + 1))"
            using 1 a1 a3 a4 a_def by auto
          show ?thesis
            using 0 1 "1.prems"(3) a4 set_bins_app_bins by auto
        qed
      next
        assume a3: "\<not> is_terminal a"
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 2: "item_end ?x = k"
          using "local.1.prems"(1) "local.1.prems"(2) wf_bins_kth_bin x_in_kth_bin by force
        have 3: "is_nonterminal a"
          by (metis "local.1.prems"(1) "local.1.prems"(2) Option.option.inject Product_Type.prod.collapse
                    a2 a3 a_def is_complete_def is_sentence_symbol is_symbol_distinct item_rule_body_def
                    leI next_symbol_def rule_\<alpha>_type rule_body_def wf_bins_kth_bin wf_item_def x_in_kth_bin)
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have "i < length (items (bins ?bs' ! k))"
          using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
        have "wf_bins ?bs'"
          using "1.prems"(1,2) wf_bins_Predict_it wf_bins_app_bins x_in_kth_bin by (metis wf_bins_kth_bin wf_item_def)
        moreover have "k < length (bins ?bs')"
          using "1.prems"(2) length_bins_app_bins by simp
        moreover have "sound_items (set_bins ?bs')"
          by (metis "1.prems"(1,2,5) S2 UnE Un_upper1 a_def set_bins_app_bins sound_items_def x_in_kth_bin)
        moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
        proof -
          have 0: "?x = items (bins ?bs' ! k) ! i"
            using "1.prems"(2) kth_bin_nth_id a1 by simp
          have 1: "set_bins_upto ?bs' k i = set_bins_upto bs k i"
            using "1.prems"(2) a1 set_bins_upto_kth_nth_id by simp
          have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
            using AUX31 \<open>i < length (items (bins ?bs' ! k))\<close> by simp
          also have "... = Complete k (set_bins_upto bs k i \<union> {?x})"
            using 0 1 by simp
          also have "... = Complete k (set_bins_upto bs k i)"
            using Q8[OF a_def 3] 2
            by (metis "local.1.prems"(1) "local.1.prems"(2) "local.1.prems"(5) AUX1 in_mono sound_items_def wf_bins_def) 
          also have "... \<subseteq> set_bins bs"
            using "1.prems"(4) by blast
          finally show ?thesis
            using "1.prems"(2) set_bins_app_bins by auto
        qed
        ultimately have 1: "Complete k (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k ?bs' (i + 1))"
          using "1.IH" a1 a2 a3 a_def "1.prems"(3) length_bins_app_bins by auto
        show ?thesis
          using 0 1 "1.prems"(2) set_bins_app_bins Complete_sub_mono
          by (metis subset_trans sup_ge1)
      qed
    qed
  qed
qed

lemma ABCD':
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k i) \<subseteq> set_bins bs"
  assumes "sound_items (set_bins bs)"
  shows "\<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  using assms A B C D \<pi>_step_def by simp

lemma ABCD:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs"
  assumes "sound_items (set_bins bs)"
  shows "\<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using assms ABCD' \<pi>_it_def by metis

lemma R11:
  assumes "set is \<subseteq> set_bin (bins bs ! k)" "k < length (bins bs)"
  shows "app_bins bs k is = bs"
proof -
  have "filter (\<lambda>i. i \<notin> set (items (bins bs ! k))) is = []"
    by (metis assms(1) filter_False set_bin_conv_set subset_iff)
  thus ?thesis
    using assms unfolding app_bins_def app_bin_def set_bin_conv_set by simp
qed

lemma R12:
  assumes "k < length (bins bs)" "l < length (bins bs)"
  shows "length (items (bins (\<pi>_it' k bs i) ! l)) \<ge> length (items (bins bs ! l))"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    thus ?thesis
      by simp
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
        using a1 a2 \<pi>_it'_simps(2) by blast
      have "k < length (bins ?bs')" "l < length (bins ?bs')"
        using "1.prems" length_bins_app_bins by simp_all
      hence 1: "length (items (bins ?bs' ! l)) \<le> length (items (bins (\<pi>_it' k ?bs' (i + 1)) ! l))"
        using "1.IH" a1 a2 by simp
      show ?thesis
        using 0 1
        by (smt (z3) "local.1.prems"(1) Earley_List.bins.sel Orderings.order_class.dual_order.trans app_bins_def length_kth_bin_app_bins nth_list_update_neq)
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) by blast
          have "k < length (bins ?bs')" "l < length (bins ?bs')"
            using "1.prems" length_bins_app_bins by simp_all
          hence 1: "length (items (bins ?bs' ! l)) \<le> length (items (bins (\<pi>_it' k ?bs' (i + 1)) ! l))"
            using "1.IH" a1 a2 a3 a4 a_def by fastforce
          show ?thesis
            using 0 1
            by (smt (z3) "local.1.prems"(2) Earley_List.bins.sel Orderings.order_class.dual_order.trans app_bins_def length_kth_bin_app_bins nth_list_update_neq)
        next
          assume a4: "\<not> k < length inp"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(4) by blast
          hence 1: "length (items (bins bs ! l)) \<le> length (items (bins (\<pi>_it' k bs (i + 1)) ! l))"
            using 1 a3 a4 a_def by fastforce
          show ?thesis
            using 0 1 by simp
        qed
      next
        assume a3: "\<not> is_terminal a"
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have "k < length (bins ?bs')" "l < length (bins ?bs')"
          using "1.prems" length_bins_app_bins by simp_all
        hence 1: "length (items (bins ?bs' ! l)) \<le> length (items (bins (\<pi>_it' k ?bs' (i + 1)) ! l))"
          using "1.IH" a1 a2 a3 a_def by auto
        show ?thesis
          using 0 1
          by (smt (z3) "local.1.prems"(1) Earley_List.bins.sel Orderings.order_class.dual_order.trans app_bins_def length_kth_bin_app_bins nth_list_update_neq)
      qed
    qed
  qed
qed

lemma R13:
  assumes "k < length (bins bs)" "l < length (bins bs)" "j < length (items (bins bs ! l))"
  shows "items (bins (\<pi>_it' k bs i) ! l) ! j = items (bins bs ! l) ! j"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    thus ?thesis
      by simp
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
        using a1 a2 \<pi>_it'_simps(2) by blast
      have "k < length (bins ?bs')"
        using "1.prems"(1) length_bins_app_bins by simp
      moreover have "l < length (bins ?bs')"
        by (simp add: "local.1.prems"(2) length_bins_app_bins)
      moreover have "j < length (items (bins ?bs' ! l))"
        using length_kth_bin_app_bins "1.prems"
        by (smt (verit, best) Earley_List.bins.sel app_bins_def le_less_trans not_less_eq nth_list_update_neq)
      ultimately have 1: "items (bins (\<pi>_it' k ?bs' (i + 1)) ! l) ! j = items (bins ?bs' ! l) ! j"
        using "1.IH" a1 a2 by auto
      show ?thesis
        using 0 1 "1.prems" kth_bin_nth_id by (metis Earley_List.bins.sel app_bins_def nth_list_update_neq)
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) by blast
          have "k < length (bins ?bs')"
            using "1.prems"(1) length_bins_app_bins by simp
          moreover have "l < length (bins ?bs')"
            by (simp add: "local.1.prems"(2) length_bins_app_bins)
          moreover have "j < length (items (bins ?bs' ! l))"
            using length_kth_bin_app_bins "1.prems"
            by (smt (z3) Earley_List.bins.sel Orderings.order_class.dual_order.strict_iff_order app_bins_def leD le_trans nth_list_update_neq)
          ultimately have 1: "items (bins (\<pi>_it' k ?bs' (i + 1)) ! l) ! j = items (bins ?bs' ! l) ! j"
            using "1.IH" a1 a2 a3 a4 a_def by fastforce
          show ?thesis
            using 0 1 app_bins_def
            by (metis "local.1.prems"(2) "local.1.prems"(3) Earley_List.bins.sel kth_bin_nth_id nth_list_update_neq)
        next
          assume a4: "\<not> k < length inp"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(4) by blast
          show ?thesis
            using 0 1 a3 a4 a_def by fastforce
        qed
      next
        assume a3: "\<not> is_terminal a"
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have "k < length (bins ?bs')"
          using "1.prems"(1) length_bins_app_bins by simp
        moreover have "l < length (bins ?bs')"
          by (simp add: "local.1.prems"(2) length_bins_app_bins)
        moreover have "j < length (items (bins ?bs' ! l))"
          using length_kth_bin_app_bins "1.prems"
          by (smt (verit, best) Earley_List.bins.sel app_bins_def le_less_trans not_less_eq nth_list_update_neq)
          ultimately have 1: "items (bins (\<pi>_it' k ?bs' (i + 1)) ! l) ! j = items (bins ?bs' ! l) ! j"
            using "1.IH" a1 a2 a3 a_def by auto
        show ?thesis
          using 0 1 "1.prems" kth_bin_nth_id
          by (metis Earley_List.bins.collapse Earley_List.bins.inject app_bins_def nth_list_update_neq)
      qed
    qed
  qed
qed

lemma R14:
  assumes "k < length (bins bs)" "l < length (bins bs)"
  shows "set_bin (bins bs ! l) \<subseteq> set_bin (bins (\<pi>_it' k bs i) ! l)"
proof standard
  fix x
  assume "x \<in> set_bin (bins bs ! l)"
  hence "x \<in> set (items (bins bs ! l))"
    using set_bin_conv_set by blast
  then obtain j where *: "j < length (items (bins bs ! l))" "items (bins bs ! l) ! j = x"
    by (meson in_set_conv_nth)
  hence 0: "j < length (items (bins bs ! l))"
    by blast
  have "x = items (bins (\<pi>_it' k bs i) ! l) ! j"
    using 0 R13 assms *(2) by simp
  moreover have "j < length (items (bins (\<pi>_it' k bs i) ! l))"
    by (meson "0" R12 Suc_le_eq assms(1) assms(2) le_trans)
  ultimately have "x \<in> set (items (bins (\<pi>_it' k bs i) ! l))"
    by (meson in_set_conv_nth)
  thus "x \<in> set_bin (bins (\<pi>_it' k bs i) ! l)"
    using set_bin_conv_set by blast
qed

lemma R15:
  assumes "item_origin x < k" "set_bin (bins bs ! item_origin x) = set_bin (bins bs' ! item_origin x)"
  shows "set (Complete_it k x bs) = set (Complete_it k x bs')"
  using assms
  unfolding Complete_it_def set_bin_conv_set by simp

lemma R16:
  assumes "k < length (bins bs)" "l < k"
  shows "set_bin (bins (\<pi>_it' k bs i) ! l) = set_bin (bins bs ! l)"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    thus ?thesis
      by simp
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
        using a1 a2 \<pi>_it'_simps(2) by blast
      have "k < length (bins ?bs')"
        using "1.prems" length_bins_app_bins by simp
      hence 1: "set_bin (bins (\<pi>_it' k ?bs' (i + 1)) ! l) = set_bin (bins ?bs' ! l)"
        using "1.IH" a1 a2 "1.prems"(2) by auto
      show ?thesis
        using 0 1 "1.prems"(2) app_bins_def by auto
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) by blast
          have "k < length (bins ?bs')"
            using "1.prems" length_bins_app_bins by simp
          hence 1: "set_bin (bins (\<pi>_it' k ?bs' (i + 1)) ! l) = set_bin (bins ?bs' ! l)"
            using "1.IH" a1 a2 a3 a4 a_def "1.prems"(2) by simp
          show ?thesis
            using 0 1 "1.prems"(2) app_bins_def by simp
        next
          assume a4: "\<not> k < length inp"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(4) by blast
          hence 1: "set_bin (bins (\<pi>_it' k bs (i + 1)) ! l) = set_bin (bins bs ! l)"
            using 1 a3 a4 a_def by fastforce
          show ?thesis
            using 0 1 by simp
        qed
      next
        assume a3: "\<not> is_terminal a"
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have "k < length (bins ?bs')"
          using "1.prems" length_bins_app_bins by simp
        hence 1: "set_bin (bins (\<pi>_it' k ?bs' (i + 1)) ! l) = set_bin (bins ?bs' ! l)"
          using "1.IH" a1 a2 a3 a_def "1.prems"(2) by auto
        show ?thesis
          using 0 1 "1.prems"(2) app_bins_def by simp
      qed
    qed
  qed
qed

lemma R1:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1" "i \<le> j"
  assumes "sound_items (set_bins bs)"
  shows "\<pi>_it' k (\<pi>_it' k bs i) j = \<pi>_it' k bs i"
  using assms
proof (induction k bs i arbitrary: j rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    thus ?thesis
      using "1.prems"(4) by simp
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    have x_in_kth_bin: "?x \<in> set_bin (bins bs ! k)"
      using a1 set_bin_conv_set by auto
    have x_in_kth_bin': "?x \<in> bin (set_bins bs) k"
      using "1.prems"(1,2) bin_def kth_bin_in_bins wf_bins_kth_bin x_in_kth_bin by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have wf: "wf_bins ?bs'"
        using "1.prems"(1,2) wf_bins_Complete_it wf_bins_app_bins x_in_kth_bin by presburger
      have sound: "sound_items (set_bins ?bs')"
        using S3[OF "1.prems"(1) _ x_in_kth_bin "1.prems"(2)]
        by (metis "1.prems"(1,2,5) BUX11 UnE a2 set_bins_app_bins sound_items_def subset_refl wf_bins_def wf_bins_kth_bin wf_items_def)
      show ?thesis
      proof cases
        assume a3: "i+1 \<le> j"
        have "\<pi>_it' k (\<pi>_it' k ?bs' (i + 1)) j = \<pi>_it' k ?bs' (i + 1)"
          using "1.IH" "1.prems"(2,3) a1 a2 a3 length_bins_app_bins wf sound by auto
        thus ?thesis
          using \<pi>_it'_simps(2) a1 a2 by presburger
      next
        assume a3: "\<not> i+1 \<le> j"
        hence "i = j"
          using "1.prems"(4) by auto
        have "\<pi>_it' k (\<pi>_it' k bs i) j = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) j"
          using \<pi>_it'_simps(2) a1 a2 by presburger
        also have "... = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) (j+1)"
        proof -
          let ?bs'' = "\<pi>_it' k ?bs' (i+1)"

          have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
            by (metis "local.1.prems"(2) R12 \<pi>_it'_simps(2) a1 a2)
          hence 0: "\<not> length (items (bins ?bs'' ! k)) \<le> j"
            using \<open>i = j\<close> a1 by linarith
          have "?x = items (bins ?bs' ! k) ! j"
            using "local.1.prems"(2) a1 kth_bin_nth_id \<open>i = j\<close> by auto
          hence 1: "?x = items (bins ?bs'' ! k) ! j"
            using R13 by (metis "local.1.prems"(2) \<open>i = j\<close> \<pi>_it'_simps(2) a1 a2 leI)

          have "\<pi>_it' k ?bs'' j = \<pi>_it' k (app_bins ?bs'' k (Complete_it k ?x ?bs'')) (j+1)"
            using 1 \<pi>_it'_simps(2)[OF 0 1 a2] by blast
          moreover have "app_bins ?bs'' k (Complete_it k ?x ?bs'') = ?bs''"
          proof -
            have "set (Complete_it k ?x ?bs'') = set (Complete_it k ?x bs)"
            proof (cases "item_origin ?x = k")
              case True
              moreover have "item_end ?x = k"
                using "1.prems"(1,2) wf_bins_kth_bin x_in_kth_bin by auto
              moreover have "is_complete ?x"
                by (metis a2 next_symbol_def not_Some_eq)
              ultimately have "derives [item_rule_head ?x] []"
                using "1.prems"(2,5) kth_bin_in_bins sound_items_def x_in_kth_bin sound_item_def slice_empty
                using is_complete_def item_\<beta>_def by (metis drop_all_iff in_mono order_refl self_append_conv)
              moreover have "wf_item ?x"
                using "local.1.prems"(1) "local.1.prems"(2) wf_bins_kth_bin x_in_kth_bin by blast
              ultimately have "False"
                unfolding item_rule_head_def rule_head_def wf_item_def using validRules
                using nonempty_deriv by fastforce
              then show ?thesis
                by blast
            next
              case False
              have "item_origin ?x < k"
                by (metis "1.prems"(1,2) False le_neq_implies_less wf_bins_kth_bin wf_item_def x_in_kth_bin)
              moreover have "set_bin (bins bs ! item_origin ?x) = set_bin (bins ?bs' ! item_origin ?x)"
                using False app_bins_def by force
              moreover have "set_bin (bins ?bs' ! item_origin ?x) = set_bin (bins ?bs'' ! item_origin ?x)"
                using "local.1.prems"(2) R16 calculation(1) length_bins_app_bins by presburger
              ultimately show ?thesis
                using R15 by blast
            qed
            also have "... \<subseteq> set_bin (bins ?bs' ! k)"
              by (simp add: "local.1.prems"(2) app_bins_def set_bin_app_bin)
            also have "... \<subseteq> set_bin (bins ?bs'' ! k)"
              using "local.1.prems"(2) R14 length_bins_app_bins by auto
            finally have "set (Complete_it k ?x ?bs'') \<subseteq> set_bin (bins ?bs'' ! k)" .
            thus ?thesis
              using R11 "1.prems"(2) length_bins_\<pi>_it' length_bins_app_bins by presburger
          qed
          ultimately show ?thesis
            by presburger
        qed
        also have "... = \<pi>_it' k ?bs' (i + 1)"
          using "1.IH" "1.prems"(1-3) \<open>i = j\<close> a1 a2 length_bins_app_bins wf_bins_Complete_it wf_bins_app_bins x_in_kth_bin
          using wf sound by force
        finally show ?thesis
          by (metis \<pi>_it'_simps(2) a1 a2)
      qed
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a2 a3 a_def \<pi>_it'_simps(3) a4 by blast
          have wf: "wf_bins ?bs'"
            using "1.prems"(1,2) a2 a4 wf_bins_app_bins wf_bins_Scan_it x_in_kth_bin by simp
          have sound: "sound_items (set_bins ?bs')"
            using S1[OF "1.prems"(1) _ x_in_kth_bin "1.prems"(2) a_def]
            by (metis (full_types) 0 "1.prems"(1,2,3,5) A sound_defs(1) S4 length_bins_app_bins subsetD)
          show ?thesis
          proof cases
            assume a5: "i+1 \<le> j"
            have "\<pi>_it' k (\<pi>_it' k ?bs' (i + 1)) j = \<pi>_it' k ?bs' (i + 1)"
              using "1.IH" "1.prems"(2,3) a1 a2 a3 length_bins_app_bins a4 a5 a_def wf sound by simp
            thus ?thesis
              using \<pi>_it'_simps(3) a1 a3 a4 a_def by presburger   
          next
            assume a5: "\<not> i+1 \<le> j"
            hence "i = j"
              using "1.prems"(4) by auto
            have "\<pi>_it' k (\<pi>_it' k bs i) j = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) j"
              using 0 by auto
            also have "... = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) (j+1)"
            proof -
              let ?bs'' = "\<pi>_it' k ?bs' (i+1)"

              have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
                by (metis "0" "local.1.prems"(2) R12)
              hence 0: "\<not> length (items (bins ?bs'' ! k)) \<le> j"
                using \<open>i = j\<close> a1 by linarith
              have "?x = items (bins ?bs' ! k) ! j"
                using "local.1.prems"(2) a1 kth_bin_nth_id \<open>i = j\<close> by (simp add: app_bins_def)
              hence 1: "?x = items (bins ?bs'' ! k) ! j"
                by (metis "local.1.prems"(2) R13 \<open>i = j\<close> \<pi>_it'_simps(3) a1 a3 a4 a_def not_less)

              have "k+1 < length (bins bs)"
                using "1.prems"(3) a4 by auto
              hence 2: "k+1 < length (bins ?bs')"
                using length_bins_app_bins by presburger

              have "\<pi>_it' k ?bs'' j = \<pi>_it' k (app_bins ?bs'' (k+1) (Scan_it k a ?x ?bs'')) (j+1)"
                using "0" "1" \<pi>_it'_simps(3) a3 a4 a_def by blast
              moreover have "app_bins ?bs'' (k+1) (Scan_it k a ?x ?bs'') = ?bs''"
              proof -
                have "set (Scan_it k a ?x ?bs'') = set (Scan_it k a ?x bs)"
                  unfolding Scan_it_def by blast
                also have "... \<subseteq> set_bin (bins ?bs' ! (k+1))"
                  by (simp add: "local.1.prems"(3) a4 app_bins_def set_bin_app_bin)
                also have "... \<subseteq> set_bin (bins ?bs'' ! (k+1))"
                  using "2" R14 by auto
                finally have "set (Scan_it k a ?x ?bs'') \<subseteq> set_bin (bins ?bs'' ! (k+1))" .
                thus ?thesis
                  using R11 \<open>k+1 < length (bins bs)\<close> length_bins_\<pi>_it' length_bins_app_bins by presburger
              qed
              ultimately show ?thesis
                by presburger
            qed
            also have "... = \<pi>_it' k ?bs' (i + 1)"
              using "1.IH" "1.prems"(2,3) \<open>i = j\<close> a1 a3 a_def length_bins_app_bins wf a4 sound by force
            finally show ?thesis
              by (metis "0")
          qed
        next
          assume a4: "\<not> k < length inp"
          show ?thesis
            proof cases
              assume a5: "i+1 \<le> j"
              show ?thesis
                using 1 a1 a3 a4 a5 a_def by auto
            next
              assume a5: "\<not> i+1 \<le> j"
              show ?thesis
                by (smt (z3) 1 Option.option.simps(5) R13 Suc_eq_plus1 \<pi>_it'_simps(1) \<pi>_it'_simps(4) a3 a4 a5 a_def le_Suc_eq le_antisym le_eq_less_or_eq not_le_imp_less)
            qed
        qed
      next
        assume a3: "\<not> is_terminal a"
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have len: "i < length (items (bins ?bs' ! k))"
          using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
        have wf: "wf_bins ?bs'"
          using "1.prems"(1,2) wf_bins_Predict_it wf_bins_app_bins x_in_kth_bin by (metis wf_bins_kth_bin wf_item_def)
        have sound: "sound_items (set_bins ?bs')"
          using S2 by (metis 0 "1.prems"(1,2,3,5) A S4 length_bins_app_bins sound_items_def subsetD)
        show ?thesis
        proof cases
          assume a4: "i+1 \<le> j"
          hence "\<pi>_it' k (\<pi>_it' k ?bs' (i + 1)) j = \<pi>_it' k ?bs' (i + 1)"
            using "1.IH" "1.prems"(2,3) a1 a2 a3 length_bins_app_bins a_def wf sound by simp
          thus ?thesis
            using \<pi>_it'_simps(5) a1 a2 a3 a_def by presburger
        next
          assume a4: "\<not> i+1 \<le> j"
          hence "i = j"
            using "1.prems"(4) by auto
          have "\<pi>_it' k (\<pi>_it' k bs i) j = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) j"
            using \<pi>_it'_simps(5) a1 a2 a3 a_def by presburger
          also have "... = \<pi>_it' k (\<pi>_it' k ?bs' (i+1)) (j+1)"
          proof -
            let ?bs'' = "\<pi>_it' k ?bs' (i+1)"

            have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
              by (metis "0" "local.1.prems"(2) R12)
            hence 0: "\<not> length (items (bins ?bs'' ! k)) \<le> j"
              using \<open>i = j\<close> a1 by linarith
            have "?x = items (bins ?bs' ! k) ! j"
              using "local.1.prems"(2) a1 kth_bin_nth_id \<open>i = j\<close> by auto
            hence 1: "?x = items (bins ?bs'' ! k) ! j"
              using R13 by (metis "local.1.prems"(2) \<open>i = j\<close> calculation len length_bins_\<pi>_it')

            have "\<pi>_it' k ?bs'' j = \<pi>_it' k (app_bins ?bs'' k (Predict_it k a ?bs'')) (j+1)"
              using "0" "1" \<pi>_it'_simps(5) a3 a_def by blast
            moreover have "app_bins ?bs'' k (Predict_it k a ?bs'') = ?bs''"
            proof -
              have "set (Predict_it k a ?bs'') = set (Predict_it k a bs)"
                unfolding Predict_it_def by blast
              also have "... \<subseteq> set_bin (bins ?bs' ! k)"
                by (simp add: "local.1.prems"(2) app_bins_def set_bin_app_bin)
              also have "... \<subseteq> set_bin (bins ?bs'' ! k)"
                by (metis "local.1.prems"(2) R14 length_bins_app_bins)
              finally have "set (Predict_it k a ?bs'') \<subseteq> set_bin (bins ?bs'' ! k)" .
              thus ?thesis
                using R11 "1.prems"(2) length_bins_\<pi>_it' length_bins_app_bins by presburger
            qed
            ultimately show ?thesis
              by presburger
          qed
          also have "... = \<pi>_it' k ?bs' (i + 1)"
            using "1.IH" "1.prems"(2,3) \<open>i = j\<close> a1 a3 a_def length_bins_app_bins wf sound by force
          finally show ?thesis
            by (metis "0")
        qed
      qed
    qed
  qed
qed

lemma R2:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "sound_items (set_bins bs)"
  shows "\<pi>_it k (\<pi>_it k bs) = \<pi>_it k bs"
  using assms R1 \<pi>_it_def le0 by metis

lemma R3:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  shows "set_bins_upto (\<pi>_it' k bs i) k 0 = set_bins_upto bs k 0"
  using assms
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof cases
    assume a1: "i \<ge> length (items (bins bs ! k))"
    thus ?thesis
      by simp
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    have x_in_kth_bin: "?x \<in> set_bin (bins bs ! k)"
      using a1 set_bin_conv_set by auto
    have x_in_kth_bin': "?x \<in> bin (set_bins bs) k"
      using "1.prems"(1,2) bin_def kth_bin_in_bins wf_bins_kth_bin x_in_kth_bin by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
        using a1 a2 \<pi>_it'_simps(2) by blast
      have "i < length (items (bins ?bs' ! k))"
        using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
      have "wf_bins ?bs'"
        using "1.prems"(1,2) wf_bins_Complete_it wf_bins_app_bins x_in_kth_bin by presburger
      moreover have "k < length (bins ?bs')"
        using "1.prems"(2) length_bins_app_bins by simp
      ultimately have 1: "set_bins_upto (\<pi>_it' k ?bs' (i + 1)) k 0 = set_bins_upto ?bs' k 0"
        using "1.IH" a1 a2 "1.prems"(3) length_bins_app_bins by auto
      show ?thesis
        using 0 1 by (metis "1.prems"(2) a1 le_add2 le_add_same_cancel2 le_eq_less_or_eq set_bins_upto_kth_nth_id)
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k a ?x bs)"
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) by blast
          have "i < length (items (bins ?bs' ! k))"
            using a1 "1.prems"(2) length_kth_bin_app_bins app_bins_def by auto
          have "wf_bins ?bs'"
            using "1.prems"(1,2) wf_bins_Scan_it wf_bins_app_bins x_in_kth_bin a2 a4 less_or_eq_imp_le by presburger
          moreover have "k < length (bins ?bs')"
            using "1.prems"(2) length_bins_app_bins by simp
          ultimately have 1: "set_bins_upto (\<pi>_it' k ?bs' (i + 1)) k 0 = set_bins_upto ?bs' k 0"
            using "1.IH" a1 a2 a3 a4 a_def "1.prems"(3) length_bins_app_bins by auto
          show ?thesis
            using 0 1 by (metis "1.prems"(3) Suc_eq_plus1 a1 a4 le0 le_eq_less_or_eq less_not_refl2 not_less_eq set_bins_upto_kth_nth_id)
        next
          assume a4: "\<not> k < length inp"
          thus ?thesis
            using 1 a3 a_def by force
        qed
      next
        assume a3: "\<not> is_terminal a"
        let ?bs' = "app_bins bs k (Predict_it k a bs)"
        have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
          using a1 a2 a3 a_def \<pi>_it'_simps(5) by blast
        have "i < length (items (bins ?bs' ! k))"
          using a1 "1.prems"(2) length_kth_bin_app_bins by (meson less_le_trans not_le_imp_less)
        have "wf_bins ?bs'"
          using "1.prems"(1,2) wf_bins_Predict_it wf_bins_app_bins x_in_kth_bin by (metis wf_bins_kth_bin wf_item_def)
        moreover have "k < length (bins ?bs')"
          using "1.prems"(2) length_bins_app_bins by simp
        ultimately have 1: "set_bins_upto (\<pi>_it' k ?bs' (i + 1)) k 0 = set_bins_upto ?bs' k 0"
          using "1.IH" a1 a2 a3 a_def "1.prems"(3) length_bins_app_bins by auto
        show ?thesis
          using 0 1 by (metis "1.prems"(2) a1 le0 not_gr_zero order_refl set_bins_upto_kth_nth_id)
      qed
    qed
  qed
qed

lemma R4:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  shows "set_bins_upto (\<pi>_it k bs) k 0 = set_bins_upto bs k 0"
  using assms R3 by (metis \<pi>_it_def)

lemma funpower_ABCD:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs"
  assumes "sound_items (set_bins bs)"
  shows "funpower (\<pi>_step k) n (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using assms
proof (induction n)
  case 0
  have "funpower (\<pi>_step k) 0 (set_bins bs) = set_bins bs"
    by simp
  then show ?case
    using A[OF 0(2,3)] \<pi>_it_def by metis
next
  case (Suc n)

  have 0: "wf_bins (\<pi>_it k bs)"
    using assms(1) assms(2) assms(3) wf_bins_\<pi>_it by auto
  have 1: "k < length (bins (\<pi>_it k bs))"
    by (simp add: assms(2) length_bins_\<pi>_it)
  have 2: "length (bins (\<pi>_it k bs)) = length inp + 1"
    by (simp add: assms(3) length_bins_\<pi>_it)
  have 3: "\<pi>_step k (set_bins_upto (\<pi>_it k bs) k 0) \<subseteq> set_bins (\<pi>_it k bs)"
    using Suc(5) using R4 by (metis A \<pi>_it_def assms(1-3) order_trans)
  have 4: "sound_items (set_bins (\<pi>_it k bs))"
    using Suc(6) S5 assms(1) assms(2) assms(3) by blast

  have "funpower (\<pi>_step k) (Suc n) (set_bins bs) = (\<pi>_step k) (funpower (\<pi>_step k) n (set_bins bs))"
    by simp
  also have "... \<subseteq> (\<pi>_step k) (set_bins (\<pi>_it k bs))"
    by (meson \<pi>_step_sub_mono assms(1-5) local.Suc.IH)
  also have "... \<subseteq> set_bins (\<pi>_it k (\<pi>_it k bs))"
    using ABCD[OF 0 1 2 3 4] by simp
  also have "... \<subseteq> set_bins (\<pi>_it k bs)"
    using R2 assms(1) assms(2) assms(3)
    using assms(5) by auto
  finally show ?case .
qed

lemma \<pi>_ABCD:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs"
  assumes "sound_items (set_bins bs)"
  shows "\<pi> k (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using assms funpower_ABCD \<pi>_def elem_limit_simp by fastforce

lemma F1:
  "set_bins_upto bs 0 0 = {}"
  unfolding set_bins_upto_def set_bin_upto_def by simp

lemma F2:
  "\<pi>_step k {} = {}"
  unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast

lemma F31:
  assumes "wf_bins bs" "x \<in> set_bin ((bins bs) ! k)" "k < length (bins bs)"
  shows "item_end x = k"
  using assms by (meson wf_bins_kth_bin)

lemma F3:
  assumes "wf_bins bs" "k < length (bins bs)"
  shows "bin (set_bins_upto bs k 0) k = {}"
proof -
  {
    fix x
    assume "x \<in> set_bins_upto bs k 0"
    hence "x \<in> \<Union> {set_bin (bins bs ! l) |l. l < k}"
      unfolding set_bins_upto_def set_bin_upto_def by blast
    thm set_bins_upto_def
    hence "item_end x < k"
      using F31 assms by force
  }
  thus ?thesis
    using bin_def by auto
qed

lemma \<I>_sub_\<I>_it:
  assumes "k < length (bins Init_it)"
  shows "\<I> k \<subseteq> set_bins (\<I>_it k)"
  using assms
proof (induction k)
  case 0
  have 1: "wf_bins Init_it"
    by (simp add: wf_bins_Init_it)
  have 2: "0 < length (bins Init_it)"
    using 0 by blast
  have 3: "length (bins Init_it) = length inp + 1"
    by (simp add: length_bins_Init_it)
  have 4: "\<pi>_step 0 (set_bins_upto Init_it 0 0) \<subseteq> set_bins Init_it"
    using F1 F2 by simp
  have 5: "sound_items (set_bins Init_it)"
    by (simp add: Init_it_eq_Init sound_Init)
  have "\<I> 0 = \<pi> 0 Init"
    by simp
  also have "... \<subseteq> set_bins (\<pi>_it 0 Init_it)"
    using \<pi>_ABCD[OF 1 2 3 4 5] Init_it_eq_Init by simp
  also have "... = set_bins (\<I>_it 0)"
    by simp
  finally show ?case .
next
  case (Suc k)
  have 1: "wf_bins (\<I>_it k)"
    using length_bins_Init_it local.Suc.prems wf_bins_\<I>_it by force
  have 2: "Suc k < length (bins (\<I>_it k))"
    by (simp add: length_bins_\<I>_it Suc.prems)
  have 3: "length (bins (\<I>_it k)) = length inp + 1"
    by (simp add: length_bins_Init_it length_bins_\<I>_it)
  have 4: "\<pi>_step (Suc k) (set_bins_upto (\<I>_it k) (Suc k) 0) \<subseteq> set_bins (\<I>_it k)"
  proof -
    have "bin (set_bins_upto (\<I>_it k) (Suc k) 0) (Suc k) = {}"
      using F3 1 2 by auto
    hence "\<pi>_step (Suc k) (set_bins_upto (\<I>_it k) (Suc k) 0) = set_bins_upto (\<I>_it k) (Suc k) 0"
      unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast
    also have "... \<subseteq> set_bins (\<I>_it k)"
      using 1 2 AUX1 wf_bins_def by blast
    finally show ?thesis .
  qed
  have 5: "sound_items (set_bins (\<I>_it k))"
    by (metis Suc_lessD \<I>_it_sub_\<I> Suc sound_\<I> subset_antisym)
  have "\<I> (Suc k) = \<pi> (Suc k) (\<I> k)"
    by simp
  also have "... \<subseteq> \<pi> (Suc k) (set_bins (\<I>_it k))"
    using Suc \<pi>_sub_mono by simp
  also have "... \<subseteq> set_bins (\<pi>_it (Suc k) (\<I>_it k))"
    using \<pi>_ABCD[OF 1 2 3 4 5] by blast
  also have "... = set_bins (\<I>_it (Suc k))"
    by simp
  finally show ?case .
qed

lemma \<II>_sub_\<II>_it:
  "\<II> \<subseteq> set_bins \<II>_it"
  using \<I>_sub_\<I>_it \<II>_def \<II>_it_def by (simp add: length_bins_Init_it)

subsection \<open>Correctness\<close>

corollary correctness_list:
  "earley_recognized (set_bins \<II>_it) \<longleftrightarrow> derives [\<SS>] inp"
  using \<II>_it_sub_\<II> \<II>_sub_\<II>_it correctness by simp

end

end
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
  "i \<ge> length (items (bins bs ! k)) \<Longrightarrow> \<pi>_it' k bs i = bs"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = None \<Longrightarrow> 
    \<pi>_it' k bs i = \<pi>_it' k (app_bins bs k (Complete_it k x bs)) (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    is_terminal a \<Longrightarrow> k < length inp \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k (app_bins bs (k+1) (Scan_it k a x bs)) (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    is_terminal a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k bs (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow> 
    \<not> is_terminal a \<Longrightarrow> \<pi>_it' k bs i = \<pi>_it' k (app_bins bs k (Predict_it k a bs)) (i+1)"
  by (simp_all, simp_all add: Let_def)

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
  "length (bins bs) = length inp + 1 \<Longrightarrow> k < length (bins Init_it) \<Longrightarrow> set_bins (\<I>_it k) \<subseteq> \<I> k"
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

lemma D:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "Complete k (set_bins_upto bs k i) \<subseteq> set_bins bs"
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

      (*
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
      *)

      show ?thesis
        sorry
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
          let ?bs' = "app_bins bs k (Complete_it k ?x bs)"

          (*
          have 0: "\<pi>_it' k bs i = \<pi>_it' k ?bs' (i+1)"
            using a1 a_def a3 a4 \<pi>_it'_simps(3) sledgehammer
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
          *)

          show ?thesis
            sorry
        next
          assume a4: "\<not> k < length inp"

          (*
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
          *)
          show ?thesis
            sorry

        qed
      next
        assume a3: "\<not> is_terminal a"
        let ?bs' = "app_bins bs k (Predict_it k a bs)"

        (*
        have "k \<ge> length inp \<or> \<not> inp!k = a"
          using a3 valid_inp unfolding is_terminal_def by force
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
        *)

        show ?thesis
          sorry
      qed
    qed
  qed
qed

lemma ABCD':
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k i) \<subseteq> set_bins bs"
  shows "\<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  using assms A B C D \<pi>_step_def by simp

lemma ABCD:
  assumes "wf_bins bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs"
  shows "\<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using assms ABCD' \<pi>_it_def by metis

lemma funpower_ABCD:
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs"
  shows "funpower (\<pi>_step k) n (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  sorry

lemma \<pi>_ABCD:
  assumes "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs"
  shows "\<pi> k (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using assms funpower_ABCD \<pi>_def elem_limit_simp by fastforce

lemma \<I>_sub_\<I>_it:
  "\<I> k \<subseteq> set_bins (\<I>_it k)"
  sorry

lemma \<II>_sub_\<II>_it:
  "\<II> \<subseteq> set_bins \<II>_it"
  by (simp add: \<I>_sub_\<I>_it \<II>_def \<II>_it_def)

subsection \<open>Correctness\<close>

corollary correctness_list:
  "earley_recognized (set_bins \<II>_it) \<longleftrightarrow> derives [\<SS>] inp"
  using \<II>_it_sub_\<II> \<II>_sub_\<II>_it correctness by simp

end

end
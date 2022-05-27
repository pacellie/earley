theory Earley_List
  imports 
    Earley_Set
    (* "HOL-Library.While_Combinator" \<comment>\<open>TODO: Use?\<close> *)
begin

subsection \<open>Bins\<close>

datatype bin = Bin (items: "item list")

datatype bins = Bins (bins: "bin list")

definition set_bin_upto :: "bin \<Rightarrow> nat \<Rightarrow> items" where
  "set_bin_upto b i = { x | x j. j < i \<and> x = items b ! j }"

definition set_bin :: "bin \<Rightarrow> items" where
  "set_bin b = set_bin_upto b (length (items b))"

definition set_bins_upto :: "bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> items" where
  "set_bins_upto bs k i = \<Union> { set_bin b | b l. l < k \<and> b = bins bs ! l } \<union> set_bin_upto (bins bs ! k) i"

definition set_bins :: "bins \<Rightarrow> items" where
  "set_bins bs = set_bins_upto bs (length (bins bs) - 1) (length (items (bins bs ! (length (bins bs) - 1))))"

definition app_bin :: "bin \<Rightarrow> item list \<Rightarrow> bin" where
  "app_bin b is = Bin (items b @ (filter (\<lambda>i. i \<notin> set (items b)) is))"

definition app_bins :: "bins \<Rightarrow> nat \<Rightarrow> item list \<Rightarrow> bins" where
  "app_bins bs k is = Bins ((bins bs)[k := app_bin ((bins bs)!k) is])"

lemma length_bins_app_bins:
  "length (bins (app_bins bs k is)) = length (bins bs)"
  unfolding app_bins_def by simp

lemma set_bin_conv_set:
  "set_bin b = set (items b)"
  unfolding set_bin_upto_def set_bin_def using set_conv_nth by fast

lemma set_bin_app_bin:
  "set_bin (app_bin b is) = set_bin b \<union> set is"
  unfolding app_bin_def set_bin_conv_set by auto

lemma set_bins_app_bins:
  assumes "k < length (bins bs)"
  shows "set_bins (app_bins bs k is) = set_bins bs \<union> set is"
  unfolding set_bins_def set_bins_upto_def app_bins_def
  using assms length_bins_app_bins set_bin_app_bin set_bin_def
  by (auto; metis Un_iff nth_list_update_eq nth_list_update_neq zero_less_Suc Suc_pred lessE less_Suc_eq)+

lemma kth_bin_in_bins:
  "k < length (bins bs) \<Longrightarrow> set_bin (bins bs ! k) \<subseteq> set_bins bs"
  unfolding set_bin_conv_set set_bins_def set_bins_upto_def set_bin_upto_def
  by (auto; metis Nat.minus_nat.diff_0 diff_Suc_Suc in_set_conv_nth lessE)

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

definition Scan_it :: "nat \<Rightarrow> symbol \<Rightarrow> item \<Rightarrow> bins \<Rightarrow> item list" where
  "Scan_it k a x bs = (
    if k < length inp \<and> inp!k = a then
      let x' = inc_item x (k+1) in
      [x']
    else [])"

definition Predict_it :: "nat \<Rightarrow> symbol \<Rightarrow> bins \<Rightarrow> item list" where
  "Predict_it k X bs = (
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
  "wf_bins bs \<longleftrightarrow> (\<forall>k < length (bins bs). wf_bin k (bins bs ! k))"

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
    unfolding wf_bins_def wf_bin_def
    by (metis bin.sel bins.sel List.list.set(1) empty_iff length_replicate nth_replicate)
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

lemma A:
  "Scan k (set_bins_upto bs k i) \<subseteq> set_bins bs \<Longrightarrow> Scan k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  sorry

lemma B:
  "Predict k (set_bins_upto bs k i) \<subseteq> set_bins bs \<Longrightarrow> Predict k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  sorry

lemma C:
  "Complete k (set_bins_upto bs k i) \<subseteq> set_bins bs \<Longrightarrow> Complete k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  sorry

lemma D:
  "set_bins bs \<subseteq> set_bins (\<pi>_it' k bs i)"
  sorry

lemma ABCD':
  "\<pi>_step k (set_bins_upto bs k i) \<subseteq> set_bins bs \<Longrightarrow> \<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it' k bs i)"
  using A B C D \<pi>_step_def by simp+

lemma ABCD:
  "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs \<Longrightarrow> \<pi>_step k (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using ABCD' \<pi>_it_def by presburger

lemma funpower_ABCD:
  "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs \<Longrightarrow> funpower (\<pi>_step k) n (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  sorry

lemma \<pi>_ABCD:
  "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs \<Longrightarrow> \<pi> k (set_bins bs) \<subseteq> set_bins (\<pi>_it k bs)"
  using funpower_ABCD \<pi>_def elem_limit_simp by fastforce

lemma \<I>_sub_\<I>_it:
  "I k \<subseteq> set_bins (\<I>_it k)"
  sorry

lemma \<II>_sub_\<II>_it:
  "\<II> \<subseteq> set_bins \<II>_it"
  by (simp add: \<I>_sub_\<I>_it \<II>_def \<II>_it_def)

subsection \<open>Correctness\<close>

corollary correctness_list:
  "earley_recognized (set_bins \<II>_it) \<longleftrightarrow> derives [\<SS>] inp"
  using \<II>_it_sub_\<II> \<II>_sub_\<II>_it correctness by simp

subsection \<open>Random thoughts\<close>

(*
lemma A:
  "Scan k (set_bins_upto bs k i) \<subseteq> set_bins bs \<Longrightarrow> I = set_bins (\<pi>_it' k bs i) \<Longrightarrow> Scan k I = I"
  sorry

lemma B:
  "Predict k (set_bins_upto bs k i) \<subseteq> set_bins bs \<Longrightarrow> I = set_bins (\<pi>_it' k bs i) \<Longrightarrow> Predict k I = I"
  sorry

lemma C:
  "Complete k (set_bins_upto bs k i) \<subseteq> set_bins bs \<Longrightarrow>  I = set_bins (\<pi>_it' k bs i) \<Longrightarrow> Complete k I = I"
  sorry

lemma ABC':
  "\<pi>_step k (set_bins_upto bs k i) \<subseteq> set_bins bs \<Longrightarrow> I = set_bins (\<pi>_it' k bs i) \<Longrightarrow> \<pi>_step k I = I"
  using A B C \<pi>_step_def by auto

lemma ABC:
  "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs \<Longrightarrow> I = set_bins (\<pi>_it k bs) \<Longrightarrow> \<pi>_step k I = I"
  using ABC' \<pi>_it_def by presburger

lemma \<pi>_ABC:
  "\<pi>_step k (set_bins_upto bs k 0) \<subseteq> set_bins bs \<Longrightarrow> I = set_bins (\<pi>_it k bs) \<Longrightarrow> \<pi> k I = I"
  by (simp add: ABC fix_is_fix_of_limit \<pi>_def)
*)

end

end
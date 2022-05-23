theory Earley_List
  imports 
    Earley_Set
    (* "HOL-Library.While_Combinator" \<comment>\<open>TODO: Use?\<close> *)
begin

\<comment>\<open>TODO: Clean\<close>

datatype bin = Bin (items: "item list")

datatype bins = Bins (bins: "bin list")

definition set_bin :: "bin \<Rightarrow> items" where
  "set_bin b = set (items b)"

definition set_bins :: "bins \<Rightarrow> items" where
  "set_bins bs = \<Union> { set_bin b | b. b \<in> set (bins bs) }"

definition app_bin :: "bin \<Rightarrow> item list \<Rightarrow> bin" where
  "app_bin b is = Bin (items b @ (filter (\<lambda>i. i \<notin> set (items b)) is))"

definition app_bins :: "bins \<Rightarrow> nat \<Rightarrow> item list \<Rightarrow> bins" where
  "app_bins bs k is = Bins ((bins bs)[k := app_bin ((bins bs)!k) is])"

lemma length_bins_app_bins:
  "length (bins (app_bins bs k is)) = length (bins bs)"
  unfolding app_bins_def by simp

lemma set_bin_app_bin:
  "set_bin (app_bin b is) = set_bin b \<union> set is"
  unfolding set_bin_def app_bin_def by auto

lemma set_bins_app_bins:
  assumes "k < length (bins bs)"
  shows "set_bins (app_bins bs k is) = set_bins bs \<union> set is"
proof standard
  show "set_bins (app_bins bs k is) \<subseteq> set_bins bs \<union> set is"
  proof standard
    fix x
    assume "x \<in> set_bins (app_bins bs k is)"
    then obtain b where "x \<in> set_bin b" "b \<in> set ((bins bs)[k := app_bin (bins bs ! k) is])"
      using set_bins_def app_bins_def by auto
    hence "b \<in> set (bins bs) \<or> b = app_bin (bins bs ! k) is"
      by (meson in_mono insertE set_update_subset_insert)
    moreover have "b \<in> set (bins bs) \<Longrightarrow> x \<in> set_bins bs \<union> set is"
      using \<open>x \<in> set_bin b\<close> set_bins_def by auto
    moreover have "b = app_bin (bins bs ! k) is \<Longrightarrow> x \<in> set_bins bs \<union> set is"
      by (smt (verit, ccfv_threshold) UnE UnI1 UnI2 Union_iff \<open>b \<in> set ((bins bs)[k := app_bin (bins bs ! k) is])\<close> \<open>x \<in> set_bin b\<close> list_update_beyond mem_Collect_eq not_le_imp_less nth_mem set_bin_app_bin set_bins_def)
    ultimately show "x \<in> set_bins bs \<union> set is"
      by blast
  qed
next
  show "set_bins bs \<union> set is \<subseteq> set_bins (app_bins bs k is)"
  proof standard
    fix x
    assume *: "x \<in> set_bins bs \<union> set is"
    show "x \<in> set_bins (app_bins bs k is)"
    proof (cases "x \<in> set_bins bs")
      case True
      then obtain b where "x \<in> set_bin b" "b \<in> set (bins bs)"
        using set_bins_def by auto
      then show ?thesis
        by (smt (z3) Earley_List.bins.case Un_iff Union_iff app_bins_def bins_def in_set_conv_nth length_list_update mem_Collect_eq nth_list_update_eq nth_list_update_neq set_bin_app_bin set_bins_def)
    next
      case False
      hence "x \<in> set is"
        using * by blast
      hence "x \<in> set_bin (app_bin (bins bs ! k) is)"
        by (simp add: set_bin_app_bin)
      have "app_bin (bins bs ! k) is \<in> set ((bins bs)[k := app_bin (bins bs ! k) is])"
        by (meson assms set_update_memI)
      then show ?thesis
        unfolding set_bins_def app_bins_def using \<open>x \<in> set_bin (app_bin (bins bs ! k) is)\<close> by auto
    qed
  qed
qed

locale Earley_List = Earley_Set +
  fixes rules :: "rule list"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
  assumes nonempty_deriv: "N \<in> \<NN> \<Longrightarrow> \<not> derives [N] []"
begin

subsection \<open>Earley algorithm\<close>

definition Init_it :: "bins" where
  "Init_it = (
    let rs = filter (\<lambda>r. rule_head r = \<SS>) rules in
    let b0 = Bin (map (\<lambda>r. init_item r 0) rs) in
    let bs = replicate (length inp + 1) (Bin []) in
    Bins (bs[0 := b0]))"

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

definition wf_bin :: "nat \<Rightarrow> bin \<Rightarrow> bool" where
  "wf_bin k b \<longleftrightarrow> (distinct (items b) \<and> (\<forall>x \<in> set (items b). wf_item x \<and> item_end x = k))"

definition wf_bins :: "bins \<Rightarrow> bool" where
  "wf_bins bs \<longleftrightarrow> (\<forall>k < length (bins bs). wf_bin k (bins bs ! k))"

lemma length_bins_Init_it:
  "length (bins Init_it) = length inp + 1"
  unfolding Init_it_def by simp

lemma length_bins_\<pi>_it':
  "length (bins (\<pi>_it' k bs i)) = length (bins bs)"
  by (induction k bs i rule: \<pi>_it'.induct) (auto simp: length_bins_app_bins Let_def split: if_splits option.splits)

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
  have "\<forall>xs. inj_on (\<lambda>r. init_item r 0) (set xs)"
    by (simp add: init_item_def inj_on_def)
  hence "distinct (items ?b0)"
    using valid_rules using distinct_map by force
  hence "wf_bin 0 ?b0"
    unfolding wf_bin_def wf_item_def using valid_rules by (auto simp: init_item_def)
  moreover have "wf_bins (Bins ?bs)"
    unfolding wf_bins_def wf_bin_def
    by (metis bin.sel bins.sel List.distinct.simps(1) List.list.set(1) empty_iff length_replicate nth_replicate)
  ultimately show ?thesis
    by (metis bins.sel Init_it_def length_list_update nth_list_update_eq nth_list_update_neq wf_bins_def)
qed

lemma wf_bins_Scan_it_aux:
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> x \<in> set_bin (bins bs ! k) \<Longrightarrow> k < length inp \<Longrightarrow> 
    next_symbol x \<noteq> None \<Longrightarrow> wf_item (inc_item x (k+1)) \<and> item_end (inc_item x (k+1)) = (k+1)"
  apply (auto simp: wf_bins_def wf_bin_def set_bin_def wf_item_def inc_item_def is_complete_def next_symbol_def item_rule_body_def split: if_splits)
  by fastforce

lemma wf_bins_Scan_it:
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> x \<in> set_bin (bins bs ! k) \<Longrightarrow> k \<le> length inp \<Longrightarrow> 
    next_symbol x \<noteq> None \<Longrightarrow> \<forall>y \<in> set (Scan_it k a x bs). wf_item y \<and> item_end y = (k+1)" 
  by (metis Groups.ab_semigroup_add_class.add.commute List.list.size(3) List.list.size(4) One_nat_def Scan_it_def gr_implies_not0 in_set_conv_nth not_less_less_Suc_eq nth_Cons_0 plus_1_eq_Suc wf_bins_Scan_it_aux)

lemma wf_bins_Predict_it:
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> k \<le> length inp \<Longrightarrow> \<forall>y \<in> set (Predict_it k X bs). wf_item y \<and> item_end y = k"
  by (auto simp: Predict_it_def wf_item_def wf_bins_def wf_bin_def init_item_def valid_rules)

lemma wf_bins_Complete_it:
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> y \<in> set_bin (bins bs ! k) \<Longrightarrow> \<forall>x \<in> set (Complete_it k y bs). wf_item x \<and> item_end x = k"
  unfolding wf_bins_def wf_bin_def wf_item_def Complete_it_def inc_item_def
  apply (auto simp: set_bin_def)
  apply (metis Orderings.order_class.dual_order.strict_trans2)
  apply (metis item.sel(1) Option.option.discI is_complete_def item_rule_body_def next_symbol_def not_less_eq_eq)
  apply (metis Orderings.order_class.dual_order.strict_trans2 not_le)
  done

lemma wf_bins_\<pi>_it':
  "wf_bins bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> k \<le> length inp \<Longrightarrow> wf_bins (\<pi>_it' k bs i)"
proof (induction k bs i rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof (cases "\<not> length (items (bins bs ! k)) \<le> i")
    case True

    let ?x = "items (bins bs ! k) ! i"
    have 0: "?x \<in> set_bin (bins bs ! k)"
      by (simp add: True not_le_imp_less set_bin_def)

    have "next_symbol ?x \<noteq> None \<Longrightarrow> \<forall>a. distinct (Scan_it k a ?x bs) \<and> (\<forall>y \<in> set (Scan_it k a ?x bs). wf_item y \<and> item_end y = (k+1))"
      using "1.prems" wf_bins_Scan_it 0 sorry
    hence 1: "next_symbol ?x \<noteq> None \<Longrightarrow> \<forall>a. wf_bins (app_bins bs (k+1) (Scan_it k a ?x bs))"
      using set_bins_app_bins[OF "1.prems"(2)] sorry
    have "\<forall>X. distinct (Predict_it k X bs) \<and> (\<forall>y \<in> set (Predict_it k X bs). wf_item y \<and> item_end y = k)"
      using "1.prems" wf_bins_Predict_it 0 sorry
    hence 2: "\<forall>X. wf_bins (app_bins bs k (Predict_it k X bs))"
      using set_bins_app_bins[OF "1.prems"(2)] sorry
    have "distinct (Complete_it k ?x bs) \<and> (\<forall>x \<in> set (Complete_it k ?x bs). wf_item x \<and> item_end x = k)"
      using "1.prems" wf_bins_Complete_it 0 sorry
    hence 3: "wf_bins (app_bins bs k (Complete_it k ?x bs))"
      using set_bins_app_bins[OF "1.prems"(2)] sorry

    let ?xa = "
(case next_symbol ?x of None \<Rightarrow> app_bins bs k (Complete_it k ?x bs)
 | Some a \<Rightarrow> if is_terminal a then 
if k < length inp then app_bins bs (k + 1) (Scan_it k a ?x bs) else bs else app_bins bs k (Predict_it k a bs))"

    have 4: "wf_bins ?xa"
      using 1 2 3 "1.prems"(1) by (auto split: option.split)
    moreover have 5: "k < length (bins ?xa)"
      apply (auto split: option.split)
        apply (auto simp add: "local.1.prems"(2) length_bins_app_bins)
      done
    ultimately have "wf_bins (\<pi>_it' k ?xa (i + 1))"
      using "1.IH"[OF True _ _ 4 5] "local.1.prems"(3) by blast
    then show ?thesis
      using True by (auto simp: Let_def)
  next
    case False
    then show ?thesis
      using "local.1.prems"(1) by auto
  qed
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
  unfolding set_bins_def set_bin_def Init_it_def Init_def rule_head_def
  by (auto simp: valid_rules; blast)

lemma Scan_it_sub_Scan:
  assumes "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "wf_bins bs" "k < length (bins bs)" "next_symbol x = Some a"
  shows "set (Scan_it k a x bs) \<subseteq> Scan k I"
proof standard
  fix y
  assume *: "y \<in> set (Scan_it k a x bs)"

  have "x \<in> set_bins bs"
    using assms(2) assms(4) nth_mem set_bins_def by auto
  moreover have "item_end x = k"
    using assms(2) assms(3,4) set_bin_def wf_bin_def wf_bins_def by blast
  ultimately have 0: "x \<in> bin I k"
    unfolding bin_def using assms(1) by blast

  {
    assume #: "k < length inp" "inp!k = a"
    hence "y = inc_item x (k+1)"
      using * unfolding Scan_it_def by simp
    hence "y \<in> Scan k I"
      using 0 # assms(5) unfolding Scan_def by blast
  }
  then show "y \<in> Scan k I"
    using * unfolding Scan_it_def by fastforce
qed

lemma Predict_it_sub_Predict:
  assumes "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)" "wf_bins bs" "next_symbol x = Some X"
  shows "set (Predict_it k X bs) \<subseteq> Predict k I"
proof standard
  fix y
  assume *: "y \<in> set (Predict_it k X bs)"

  have "x \<in> set_bins bs"
    using assms(2) assms(3) nth_mem set_bins_def by auto
  moreover have "item_end x = k"
    using assms(2) assms(3,4) set_bin_def wf_bin_def wf_bins_def by blast
  ultimately have 0: "x \<in> bin I k"
    unfolding bin_def using assms(1) by blast

  let ?rs = "filter (\<lambda>r. rule_head r = X) rules"
  let ?xs = "map (\<lambda>r. init_item r k) ?rs"

  have "y \<in> set ?xs"
    using * unfolding Predict_it_def by simp
  then obtain r where "y = init_item r k" "rule_head r = X" "r \<in> \<RR>" "next_symbol x = Some (rule_head r)"
    using valid_rules assms(5) by auto
  hence "y \<in> Predict k I"
    using 0 unfolding Predict_def by blast
  then show "y \<in> Predict k I"
    by simp
qed

lemma Complete_it_sub_Complete:
  assumes "set_bins bs \<subseteq> I" "y \<in> set_bin (bins bs ! k)" "next_symbol y = None" "wf_bins bs" "k < length (bins bs)"
  shows "set (Complete_it k y bs) \<subseteq> Complete k I"
proof standard
  fix x
  assume *: "x \<in> set (Complete_it k y bs)"

  have "y \<in> set_bins bs"
    using assms(2) assms(5) nth_mem set_bins_def by auto
  moreover have "item_end y = k"
    using assms(2) assms(4,5) set_bin_def wf_bin_def wf_bins_def by blast
  ultimately have 0: "y \<in> bin I k"
    unfolding bin_def using assms(1) by blast

  let ?orig = "bins bs ! item_origin y"
  let ?xs = "filter (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"

  have "item_origin y < length (bins bs)"
    by (metis wf_bins_def Orderings.order_class.dual_order.trans assms(2,4,5) less_Suc_eq_le not_less_eq set_bin_def wf_bin_def wf_item_def)

  hence "\<forall>z \<in> set_bin ?orig. z \<in> bin I (item_origin y)"
    by (smt (verit, best) Union_iff assms(1,4) bin_def mem_Collect_eq nth_mem set_bin_def set_bins_def subset_eq wf_bin_def wf_bins_def)

  hence 2:  "\<forall>z \<in> set ?xs. z \<in> bin I (item_origin y)"
    by (simp add: set_bin_def)

  then obtain z where 1: "x = inc_item z k" "z \<in> set ?xs"
    using "*" Complete_it_def by auto
  hence 3: "next_symbol z = Some (item_rule_head y)"
    by simp
  have 4: "z \<in> bin I (item_origin y)"
    using 1 2 by simp
  have 5: "is_complete y"
    using assms(3) next_symbol_def by (metis not_None_eq)

  show "x \<in> Complete k I"
    using 0 1(1) 3 4 5 unfolding Complete_def by blast
qed

lemma \<pi>_it'_sub_\<pi>:
  "set_bins bs \<subseteq> I \<Longrightarrow> k < length (bins bs) \<Longrightarrow> wf_bins bs \<Longrightarrow> length (bins bs) = length inp + 1 \<Longrightarrow> set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k I"
proof (induction k bs i arbitrary: I rule: \<pi>_it'.induct)
  case (1 k bs i)
  show ?case
  proof (cases "i \<ge> length (items (bins bs ! k)) ")
    case True
    then show ?thesis
      using "1.prems" \<pi>_mono by auto
  next
    case False
    let ?x = "items (bins bs ! k) ! i"
    have 0: "?x \<in> set_bin (bins bs ! k)"
      using False set_bin_def by auto
    have "?x \<in> set_bins bs"
      by (smt (verit, del_insts) "1.prems"(2) False Union_iff mem_Collect_eq not_le_imp_less nth_mem set_bin_def set_bins_def)
    hence "?x \<in> I"
      using "1.prems" by (smt (verit, ccfv_SIG) Union_iff in_mono mem_Collect_eq nth_mem set_bins_def)
    show ?thesis
    proof cases
      assume 1: "next_symbol ?x = None"
      have "set_bins (app_bins bs k (Complete_it k ?x bs)) = set_bins bs \<union> set (Complete_it k ?x bs)"
        using "1.prems" by (simp add: set_bins_app_bins)
      also have "... \<subseteq> I \<union> set (Complete_it k ?x bs)"
        using "1.prems" by blast
      also have "... \<subseteq> I \<union> Complete k I"
        using Complete_it_sub_Complete[OF "1.prems"(1) 0 1] "1.prems"(2,3) by blast
      finally have 0: "set_bins (app_bins bs k (Complete_it k ?x bs)) \<subseteq> I \<union> Complete k I" .

      have 1: "k < length (bins (app_bins bs k (Complete_it k ?x bs)))"
        by (simp add: "1.prems"(2) app_bins_def)
      have 2: "wf_bins (app_bins bs k (Complete_it k (items (bins bs ! k) ! i) bs))"
        using 0
        by (smt (verit, del_insts) "1.prems"(3) wf_bins_Complete_it wf_bin_def bins.sel False UnE app_bins_def length_list_update not_le_imp_less nth_list_update_eq nth_list_update_neq nth_mem set_bin_app_bin set_bin_def wf_bins_def)

      have "set_bins (\<pi>_it' k bs i) = set_bins (\<pi>_it' k (app_bins bs k (Complete_it k ?x bs)) (i + 1))"
        using False \<open>next_symbol ?x = None\<close> \<pi>_it'_simps(2) by presburger
      also have "... \<subseteq> \<pi> k (I \<union> Complete k I)"
        using "1.IH"[OF False _ _ 0 1 2] "1.prems" by (simp add: \<open>next_symbol ?x = None\<close> length_bins_app_bins)
      also have "... \<subseteq> \<pi> k (\<pi> k I)"
        using Complete_\<pi>_mono by (simp add: \<pi>_mono \<pi>_sub_mono)
      finally show ?thesis
        using \<pi>_idem by blast
    next
      assume "\<not> next_symbol ?x = None"
      then obtain a where 1: "next_symbol ?x = Some a"
        by blast
      show ?thesis
      proof cases
        assume 2: "is_terminal a"
        {
          assume "k < length inp"
          hence "set_bins (app_bins bs (k+1) (Scan_it k a ?x bs)) = set_bins bs \<union> set (Scan_it k a ?x bs)"
            using "1.prems" set_bins_app_bins by simp
          also have "... \<subseteq> I \<union> set (Scan_it k a ?x bs)"
            using "1.prems" by blast
          also have "... \<subseteq> I \<union> Scan k I"
            using Scan_it_sub_Scan[OF "1.prems"(1) 0 _ _ 1] "1.prems"(2,3) by blast
          finally have 0: "set_bins (app_bins bs (k+1) (Scan_it k a ?x bs)) \<subseteq> I \<union> Scan k I" .

          have 1: "k < length (bins (app_bins bs (k+1) (Scan_it k a ?x bs)))"
            by (simp add: "1.prems"(2) app_bins_def)
          have 2: "wf_bins (app_bins bs (k+1) (Scan_it k a ?x bs))"
            using 0 using wf_bins_Scan_it
            by (smt (z3) "1.prems"(3,4) wf_bin_def wf_bins_def bins.sel False Suc_eq_plus1 UnE \<open>k < length inp\<close> \<open>next_symbol ?x \<noteq> None\<close> app_bins_def le_imp_less_Suc length_bins_app_bins less_or_eq_imp_le not_le_imp_less nth_list_update_eq nth_list_update_neq nth_mem set_bin_app_bin set_bin_def)

          have "set_bins (\<pi>_it' k bs i) = set_bins (\<pi>_it' k (app_bins bs (k+1) (Scan_it k a ?x bs)) (i + 1))"
            using \<open>next_symbol ?x = Some a\<close> \<open>is_terminal a\<close> False \<pi>_it'_simps(3) \<open>k < length inp\<close> by presburger
          also have "... \<subseteq> \<pi> k (I \<union> Scan k I)"
            using "1.IH"[OF False _ _ 0 1 2] "1.prems"(4) length_bins_app_bins by (simp add: \<open>k < length inp\<close> \<open>next_symbol ?x = Some a\<close> \<open>is_terminal a\<close>)
          also have "... \<subseteq> \<pi> k (\<pi> k I)"
            using Scan_\<pi>_mono by (simp add: \<pi>_mono \<pi>_sub_mono)
          finally have ?thesis
            using \<pi>_idem by auto
        }
        hence "k < length inp \<Longrightarrow> ?thesis" .
        {
          assume "\<not> k < length inp"
          hence "Scan k I = {}"
            unfolding Scan_def by auto
          have "set_bins (\<pi>_it' k bs i) = set_bins (\<pi>_it' k bs (i + 1))"
            using \<open>next_symbol ?x = Some a\<close> \<open>is_terminal a\<close> False \<pi>_it'_simps(4) \<open>\<not> k < length inp\<close> by presburger
          also have "... \<subseteq> \<pi> k (I \<union> Scan k I)"
            using "1.IH"[OF False _ _ "1.prems"] \<open>Scan k I = {}\<close> by (simp add: \<open>\<not> k < length inp\<close> \<open>next_symbol ?x = Some a\<close> \<open>is_terminal a\<close>)
          also have "... \<subseteq> \<pi> k (\<pi> k I)"
            using Scan_\<pi>_mono by (simp add: \<pi>_mono \<pi>_sub_mono)
          finally have ?thesis
            using \<pi>_idem by auto
        }
        then show ?thesis
          using \<open>k < length inp \<Longrightarrow> ?thesis\<close> by blast
      next
        assume "\<not> is_terminal a"

        have "set_bins (app_bins bs k (Predict_it k a bs)) = set_bins bs \<union> set (Predict_it k a bs)"
          using "1.prems" by (simp add: set_bins_app_bins)
        also have "... \<subseteq> I \<union> set (Predict_it k a bs)"
          using "1.prems" by blast
        also have "... \<subseteq> I \<union> Predict k I"
          using Predict_it_sub_Predict[OF "1.prems"(1)] 0 1 "1.prems"(2,3) by blast
        finally have 0: "set_bins (app_bins bs k (Predict_it k a bs)) \<subseteq> I \<union> Predict k I" .

        have 1: "k < length (bins (app_bins bs k (Predict_it k a bs)))"
          by (simp add: "1.prems"(2) app_bins_def)
        have 2: "wf_bins (app_bins bs k (Predict_it k a bs))"
          using 0 wf_bins_Predict_it
          by (smt (z3) "1.prems"(3,4) bins.sel Suc_eq_plus1 Un_iff app_bins_def le_Suc_eq length_bins_app_bins less_or_eq_imp_le nat_neq_iff nth_list_update_eq nth_list_update_neq set_bin_app_bin set_bin_def wf_bin_def wf_bins_def)

        have "set_bins (\<pi>_it' k bs i) = set_bins (\<pi>_it' k (app_bins bs k (Predict_it k a bs)) (i + 1))"
          using False \<open>next_symbol ?x = Some a\<close> \<open>\<not> is_terminal a\<close> \<pi>_it'_simps(5) by presburger
        also have "... \<subseteq> \<pi> k (I \<union> Predict k I)"
          using "1.IH"[OF False _ _ 0 1 2] "1.prems"(4) length_bins_app_bins by (simp add: \<open>next_symbol ?x = Some a\<close> \<open>\<not> is_terminal a\<close>)
        also have "... \<subseteq> \<pi> k (\<pi> k I)"
          using Predict_\<pi>_mono by (simp add: \<pi>_mono \<pi>_sub_mono)
        finally show ?thesis
          using \<pi>_idem by blast
      qed
    qed
  qed
qed

lemma \<pi>_it_sub_\<pi>:
  "set_bins bs \<subseteq> I \<Longrightarrow> k < length (bins bs) \<Longrightarrow> length (bins bs) = length inp + 1 \<Longrightarrow> wf_bins bs \<Longrightarrow> set_bins (\<pi>_it k bs) \<subseteq> \<pi> k I"
  using \<pi>_it'_sub_\<pi> \<pi>_it_def by metis

lemma \<I>_it_sub_\<I>:
  "k < length (bins Init_it) \<Longrightarrow> length (bins bs) = length inp + 1 \<Longrightarrow> set_bins (\<I>_it k) \<subseteq> \<I> k"
proof (induction k)
  case 0
  then show ?case
    by (simp add: Init_it_eq_Init \<pi>_it_sub_\<pi> length_bins_Init_it wf_bins_Init_it)
next
  case (Suc k)
  hence 0: "set_bins (\<I>_it k) \<subseteq> \<I> k"
    by (simp add: Suc_lessD)
  have 1: "Suc k < length (bins (\<I>_it k))"
    using length_bins_\<I>_it Suc.prems by force
  have "set_bins (\<pi>_it (Suc k) (\<I>_it k)) \<subseteq> \<pi> (Suc k) (\<I> k)"
    using \<pi>_it_sub_\<pi>[OF 0 1] length_bins_Init_it length_bins_\<I>_it Suc.prems(1) wf_bins_\<I>_it by simp
  then show ?case
    by simp
qed

lemma \<II>_it_sub_\<II>:
  "set_bins \<II>_it \<subseteq> \<II>"
  using \<I>_it_sub_\<I> \<II>_def \<II>_it_def length_bins_Init_it by auto

end

end
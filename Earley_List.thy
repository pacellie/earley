theory Earley_List
  imports 
    Earley_Set
    "HOL-Library.While_Combinator" \<comment>\<open>TODO: Use?\<close>
begin

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

lemma set_bin_app_bin:
  "set_bin (app_bin b is) = set_bin b \<union> set is"
  unfolding set_bin_def app_bin_def by auto

lemma set_bins_app_bins: \<comment>\<open>TODO\<close>
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
            if is_terminal a then app_bins bs (k+1) (Scan_it k a x bs)
            else app_bins bs k (Predict_it k a bs)
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

subsection \<open>Wellformed Bins\<close>

definition wf_bin :: "nat \<Rightarrow> bin \<Rightarrow> bool" where
  "wf_bin k b \<longleftrightarrow> (\<forall>x \<in> set (items b). item_end x = k \<and> wf_item x)"

definition wf_bins :: "bins \<Rightarrow> bool" where
  "wf_bins bs \<longleftrightarrow> (\<forall>k. wf_bin k (bins bs ! k))"

subsection \<open>Equality of generated bins\<close>
\<comment>\<open>TODO: distinctness for termination proof\<close>

lemma Init_it_eq_Init:
  "set_bins Init_it = Init"
  unfolding set_bins_def set_bin_def Init_it_def Init_def rule_head_def
  by (auto simp: valid_rules; blast)

lemma A:
  assumes "set_bins bs \<subseteq> I" "y \<in> set_bin (bins bs ! k)" "next_symbol y = None" "wf_bins bs" "k < length (bins bs)"
  shows "set (Complete_it k y bs) \<subseteq> Complete k I"
proof standard
  fix x
  assume *: "x \<in> set (Complete_it k y bs)"

  have "y \<in> set_bins bs"
    using assms(2) assms(5) nth_mem set_bins_def by auto
  moreover have "item_end y = k"
    using assms(2) assms(4) set_bin_def wf_bin_def wf_bins_def by blast
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

  thm Complete_it_def Complete_def

  show "x \<in> Complete k I"
    using 0 1(1) 3 4 5 unfolding Complete_def by blast
qed

lemma B1:
  "wf_bins bs \<Longrightarrow> \<forall>x \<in> set (Complete_it k y bs). item_end x = k"
  unfolding wf_bins_def wf_bin_def Complete_it_def inc_item_def by simp

lemma B2:
  "wf_bins bs \<Longrightarrow> k \<le> length inp \<Longrightarrow> y \<in> set_bin (bins bs ! k) \<Longrightarrow> \<forall>x \<in> set (Complete_it k y bs). wf_item x"
  unfolding wf_bins_def wf_bin_def wf_item_def Complete_it_def inc_item_def
  apply (auto)
   apply (metis Earley_Set.item.sel(1) Option.option.discI is_complete_def item_rule_body_def next_symbol_def not_less_eq_eq)
  by (metis le_trans set_bin_def)

lemma \<pi>_it'_sub_\<pi>:
  "set_bins bs \<subseteq> I \<Longrightarrow> k < length (bins bs) \<Longrightarrow> wf_bins bs \<Longrightarrow> set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k I"
proof (induction k bs i arbitrary: I rule: \<pi>_it'.induct)
  case (1 k bs i)

  thm "1.prems"
  thm "1.IH"

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
      by (smt (verit, del_insts) "local.1.prems"(2) False Union_iff mem_Collect_eq not_le_imp_less nth_mem set_bin_def set_bins_def)
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
        using A[OF "1.prems"(1) 0 1] "1.prems"(2,3) by blast
      also have "... = Complete k I"
        using Complete_mono by blast
      finally have 0: "set_bins (app_bins bs k (Complete_it k ?x bs)) \<subseteq> Complete k I" .

      have 1: "k < length (bins (app_bins bs k (Complete_it k ?x bs)))"
        by (simp add: "1.prems"(2) app_bins_def)
      have 2: "wf_bins (app_bins bs k (Complete_it k (items (bins bs ! k) ! i) bs))"
        using 0 sledgehammer
        by (smt (z3) "local.1.prems"(2) "local.1.prems"(3) B2 Earley_List.Earley_List.B1 Earley_List.bins.sel Earley_List_axioms False UnE app_bins_def not_le_imp_less nth_list_update_eq nth_list_update_neq nth_mem set_bin_app_bin set_bin_def wf_bin_def wf_bins_def wf_item_def)

      have "set_bins (\<pi>_it' k bs i) = set_bins (\<pi>_it' k (app_bins bs k (Complete_it k ?x bs)) (i + 1))"
        by (metis (no_types, lifting) False Option.option.simps(4) \<open>next_symbol (items (bins bs ! k) ! i) = None\<close> local.\<pi>_it'.simps)
      also have "... \<subseteq> \<pi> k (Complete k I)"
        using "1.IH"[OF False _ _ 0 1 2] by (simp add: \<open>next_symbol (items (bins bs ! k) ! i) = None\<close>)
      also have "... \<subseteq> \<pi> k (\<pi> k I)"
        using Complete_\<pi>_mono by (simp add: \<pi>_sub_mono)
      finally show ?thesis
        using \<pi>_idem by blast
    next
      assume "\<not> next_symbol ?x = None"
      show ?thesis
        sorry
    qed
  qed
qed

lemma \<pi>_it_sub_\<pi>:
  "set_bins bs \<subseteq> I \<Longrightarrow> k < length (bins bs) \<Longrightarrow> wf_bins bs \<Longrightarrow> set_bins (\<pi>_it k bs) \<subseteq> \<pi> k I"
  using \<pi>_it'_sub_\<pi> \<pi>_it_def by metis

lemma Q:
  "wf_bins Init_it"
  sorry

lemma Q':
  "wf_bins bs \<Longrightarrow> wf_bins (\<pi>_it k bs)"
  sorry

lemma Q'':
  "length (bins (\<pi>_it k bs)) = length (bins bs)"
  sorry

lemma \<I>_it_length:
  "length (bins (\<I>_it k)) = length (bins Init_it)"
  by (induction k) (auto simp: Q'')

lemma \<I>_it_wf_bins:
  "wf_bins (\<I>_it k)"
  by (induction k) (auto simp: Q Q')

lemma \<I>_it_sub_\<I>:
  "k < length (bins Init_it) \<Longrightarrow> set_bins (\<I>_it k) \<subseteq> \<I> k"
proof (induction k)
  case 0
  then show ?case
    by (auto simp: \<pi>_it_sub_\<pi> Q Init_it_eq_Init)
next
  case (Suc k)
  hence 0: "set_bins (\<I>_it k) \<subseteq> \<I> k"
    by (simp add: Suc_lessD)
  have 1: "Suc k < length (bins (\<I>_it k))"
    using \<I>_it_length local.Suc.prems by force
  have "set_bins (\<pi>_it (Suc k) (\<I>_it k)) \<subseteq> \<pi> (Suc k) (\<I> k)"
    using \<pi>_it_sub_\<pi>[OF 0 1] \<I>_it_wf_bins by presburger
  then show ?case
    by simp
qed

lemma Q''':
  "length (bins Init_it) = length inp + 1"
  unfolding Init_it_def by simp

lemma \<II>_it_sub_\<II>:
  "set_bins \<II>_it \<subseteq> \<II>"
  using \<I>_it_sub_\<I> \<II>_def \<II>_it_def by (simp add: Q''')

end

end
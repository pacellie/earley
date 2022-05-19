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

subsection \<open>Equality of generated bins\<close>
\<comment>\<open>TODO: distinctness for termination proof\<close>

lemma Init_it_eq_Init:
  "set_bins Init_it = Init"
  unfolding set_bins_def set_bin_def Init_it_def Init_def rule_head_def
  by (auto simp: valid_rules; blast)

lemma A:
  "set_bins bs \<subseteq> I \<Longrightarrow> y \<in> set_bins bs \<Longrightarrow> next_symbol y = None \<Longrightarrow> set (Complete_it k y bs) \<subseteq> Complete k I"
  sorry

lemma \<pi>_it'_sub_\<pi>:
  "set_bins bs \<subseteq> I \<Longrightarrow> set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k I"
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
    have "?x \<in> set_bin (bins bs ! k)"
      using False set_bin_def by auto
    hence "?x \<in> I"
      using "1.prems" by (metis Earley_List.bins.collapse Un_iff app_bins_def le_refl list_update_beyond set_bin_def set_bins_app_bins subset_iff)
    show ?thesis
    proof cases
      assume "next_symbol ?x = None"
      have "set_bins (app_bins bs k (Complete_it k ?x bs)) = set_bins bs \<union> set (Complete_it k ?x bs)"
        by (simp add: set_bins_app_bins)
      also have "... \<subseteq> I \<union> set (Complete_it k ?x bs)"
        using "1.prems" by blast
      also have "... \<subseteq> I \<union> Complete k I"
        using A
        by (metis "local.1.prems" Earley_List.bins.exhaust_sel False app_bins_def le_cases le_iff_sup list_update_beyond nat_less_le set_bins_app_bins set_update_memI subset_eq sup_commute)
      also have "... = Complete k I"
        using Complete_mono by blast
      also have "... \<subseteq> \<pi> k I"
        by (simp add: Complete_\<pi>_mono)
      finally have "set_bins (app_bins bs k (Complete_it k ?x bs)) \<subseteq> \<pi> k I" .
      show ?thesis
        by (metis "1"(2) Earley_List.bins.exhaust_sel False Un_iff \<pi>_mono app_bins_def le_iff_sup linorder_le_cases list_update_beyond nat_less_le set_bins_app_bins set_update_memI subsetI)
    next
      assume "\<not> next_symbol ?x = None"
      show ?thesis
        sorry
    qed
  qed
qed

lemma \<pi>_it_sub_\<pi>:
  "set_bins bs \<subseteq> I \<Longrightarrow> set_bins (\<pi>_it k bs) \<subseteq> \<pi> k I"
  using \<pi>_it'_sub_\<pi> \<pi>_it_def by metis

lemma \<I>_it_sub_\<I>:
  "set_bins (\<I>_it k) \<subseteq> \<I> k"
  by (induction k) (auto simp: \<pi>_it_sub_\<pi> Init_it_eq_Init)

lemma \<II>_it_sub_\<II>:
  "set_bins \<II>_it \<subseteq> \<II>"
  using \<I>_it_sub_\<I> \<II>_def \<II>_it_def by simp

end

end
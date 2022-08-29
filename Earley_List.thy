theory Earley_List
  imports 
    Earley_Set
begin

subsection \<open>Bins\<close>

datatype 'a bin = Bin (items: "'a item list")

datatype 'a bins = Bins (bins: "'a bin list")

definition set_bin_upto :: "'a bin \<Rightarrow> nat \<Rightarrow> 'a items" where
  "set_bin_upto b i = { items b ! j | j. j < i \<and> j < length (items b) }"

definition set_bin :: "'a bin \<Rightarrow> 'a items" where
  "set_bin b = set (items b)"

definition wf_bin :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a bin \<Rightarrow> bool" where
  "wf_bin cfg inp k b \<longleftrightarrow> distinct (items b) \<and> (\<forall>x \<in> set (items b). wf_item cfg inp x \<and> item_end x = k)"

definition wf_bins :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "wf_bins cfg inp bs \<longleftrightarrow> (\<forall>k < length (bins bs). wf_bin cfg inp k (bins bs ! k))"

declare set_bin_def[simp]

definition set_bins_upto :: "'a bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a items" where
  "set_bins_upto bs k i = \<Union> { set_bin (bins bs ! l) | l. l < k } \<union> set_bin_upto (bins bs ! k) i"

definition set_bins :: "'a bins \<Rightarrow> 'a items" where
  "set_bins bs = \<Union> { set_bin (bins bs ! k) | k. k < length (bins bs) }"

definition app_bin :: "'a bin \<Rightarrow> 'a item list \<Rightarrow> 'a bin" where
  "app_bin b is = Bin (items b @ (filter (\<lambda>i. i \<notin> set (items b)) is))"

definition app_bins :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a item list \<Rightarrow> 'a bins" where
  "app_bins bs k is = Bins ((bins bs)[k := app_bin ((bins bs)!k) is])"

lemma length_bins_app_bins[simp]:
  "length (bins (app_bins bs k is)) = length (bins bs)"
  unfolding app_bins_def by simp

lemma length_nth_bin_app_bins:
  "length (items (bins (app_bins bs k is) ! l)) \<ge> length (items (bins bs ! l))"
  by (cases "k < length (bins bs)") (auto simp: nth_list_update app_bins_def app_bin_def)

lemma length_nth_bin_app_bins_eq:
  "k \<noteq> l \<Longrightarrow> length (items (bins (app_bins bs k is) ! l)) = length (items (bins bs ! l))"
  by (cases "k < length (bins bs)") (auto simp: app_bins_def app_bin_def)

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

lemma set_bin_upto_eq_set_bin:
  "i \<ge> length (items b) \<Longrightarrow> set_bin_upto b i = set_bin b"
  unfolding set_bin_upto_def set_bin_def by (auto, metis in_set_conv_nth less_le_trans)

lemma set_bins_upto_empty:
  "set_bins_upto bs 0 0 = {}"
  unfolding set_bins_upto_def set_bin_upto_def by simp

lemma set_bin_app_bin[simp]:
  "set_bin (app_bin b is) = set_bin b \<union> set is"
  unfolding app_bin_def by auto

lemma set_bins_app_bins:
  "k < length (bins bs) \<Longrightarrow> set_bins (app_bins bs k is) = set_bins bs \<union> set is"
  unfolding set_bins_def app_bins_def using set_bin_app_bin
  by (auto; smt Un_iff nth_list_update_eq nth_list_update_neq set_bin_app_bin set_bin_def)+

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

lemma distinct_app_bins:
  "distinct (items (bins bs ! k)) \<Longrightarrow> distinct is \<Longrightarrow> distinct (items (bins (app_bins bs k is) ! k))"
  unfolding app_bins_def by (auto, metis distinct_app_bin list_update_beyond not_le_imp_less nth_list_update_eq)

lemma wf_bins_kth_bin:
  "wf_bins cfg inp bs \<Longrightarrow> k < length (bins bs) \<Longrightarrow> x \<in> set_bin (bins bs ! k) \<Longrightarrow> wf_item cfg inp x \<and> item_end x = k"
  using set_bin_def wf_bin_def wf_bins_def by blast

lemma wf_bins_app_bins:
  "wf_bins cfg inp bs \<Longrightarrow> distinct xs \<Longrightarrow> \<forall>x \<in> set xs. wf_item cfg inp x \<and> item_end x = k \<Longrightarrow> wf_bins cfg inp (app_bins bs k xs)"
  unfolding wf_bins_def wf_bin_def app_bins_def using set_bin_app_bin distinct_app_bin
  by (cases "k < length (bins bs)") (auto simp: nth_list_update, blast+)

lemma wf_bins_impl_wf_items:
  "wf_bins cfg inp bs \<Longrightarrow> wf_items cfg inp (set_bins bs)"
  unfolding wf_bins_def wf_bin_def wf_items_def set_bins_def by auto


subsection \<open>Earley algorithm\<close>

definition nonempty_derives :: "'a cfg \<Rightarrow> bool" where
  "nonempty_derives cfg = (\<forall>N. N \<in> set (\<NN> cfg) \<longrightarrow> \<not> derives cfg [N] [])"

definition Init_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "Init_it cfg inp = (
    let rs = filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg) in
    let b0 = map (\<lambda>r. init_item r 0) rs in
    let bs = replicate (length inp + 1) (Bin []) in
    app_bins (Bins bs) 0 b0)"

definition Scan_it :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a  \<Rightarrow> 'a item \<Rightarrow> 'a item list" where
  "Scan_it k inp a x = (
    if k < length inp \<and> inp!k = a then
      let x' = inc_item x (k+1) in
      [x']
    else [])"

definition Predict_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a \<Rightarrow> 'a item list" where
  "Predict_it k cfg X = (
    let rs = filter (\<lambda>r. rule_head r = X) (\<RR> cfg) in
    map (\<lambda>r. init_item r k) rs)"

definition Complete_it :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a bins \<Rightarrow> 'a item list" where
  "Complete_it k y bs = (
    let orig = (bins bs)!(item_origin y) in
    let is = filter (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items orig) in
    map (\<lambda>x. inc_item x k) is)"

partial_function (tailrec) \<pi>_it' :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a bins" where
  "\<pi>_it' k cfg inp bs i = (
    if i \<ge> length (items (bins bs ! k)) then bs
    else
      let x = items (bins bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow>
            if is_terminal cfg a then
              if k < length inp then app_bins bs (k+1) (Scan_it k inp a x)
              else bs
            else app_bins bs k (Predict_it k cfg a)
        | None \<Rightarrow> app_bins bs k (Complete_it k x bs)
      in \<pi>_it' k cfg inp bs' (i+1))"

declare \<pi>_it'.simps[code]

definition \<pi>_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a bins" where
  "\<pi>_it k cfg inp bs = \<pi>_it' k cfg inp bs 0"

fun \<I>_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "\<I>_it 0 cfg inp = \<pi>_it 0 cfg inp (Init_it cfg inp)"
| "\<I>_it (Suc n) cfg inp = \<pi>_it (Suc n) cfg inp (\<I>_it n cfg inp)"

definition \<II>_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "\<II>_it cfg inp = \<I>_it (length inp) cfg inp"

lemma distinct_Scan_it:
  "distinct (Scan_it k inp a x)"
  unfolding Scan_it_def by simp

lemma distinct_Predict_it:
  "wf_cfg cfg \<Longrightarrow> distinct (Predict_it k cfg X)"
  unfolding Predict_it_def wf_cfg_defs by (auto simp: init_item_def rule_head_def distinct_map inj_on_def)

lemma distinct_Complete_it:
  "wf_bins cfg inp bs \<Longrightarrow> item_origin y < length (bins bs) \<Longrightarrow> distinct (Complete_it k y bs)"
  unfolding Complete_it_def wf_bins_def wf_bin_def by (auto simp: distinct_map inj_on_def inc_item_def item.expand)

lemma wf_bins_Scan_it':
  assumes "wf_bins cfg inp bs" "k < length (bins bs)" "x \<in> set_bin (bins bs ! k)"
  assumes "k < length inp" "next_symbol x \<noteq> None" "y = inc_item x (k+1)"
  shows "wf_item cfg inp y \<and> item_end y = k+1"
  using assms wf_bins_kth_bin[OF assms(1-3)]
  unfolding wf_item_def inc_item_def next_symbol_def is_complete_def item_rule_body_def
  by (auto split: if_splits)

lemma wf_bins_Scan_it:
  assumes "wf_bins cfg inp bs" "k < length (bins bs)" "x \<in> set_bin (bins bs ! k)"
  assumes "k \<le> length inp" "next_symbol x \<noteq> None"
  shows "\<forall>y \<in> set (Scan_it k inp a x). wf_item cfg inp y \<and> item_end y = (k+1)" 
  using wf_bins_Scan_it'[OF assms(1-3) _ assms(5)] 
  by (metis List.list.set(1,2) Scan_it_def empty_iff insert_iff)

lemma wf_bins_Predict_it:
  assumes "wf_bins cfg inp bs" "k < length (bins bs)" "k \<le> length inp" "wf_cfg cfg"
  shows "\<forall>y \<in> set (Predict_it k cfg X). wf_item cfg inp y \<and> item_end y = k"
  using assms by (auto simp: Predict_it_def wf_item_def wf_bins_def wf_bin_def init_item_def wf_cfg_defs)

lemma wf_bins_Complete_it:
  assumes "wf_bins cfg inp bs" "k < length (bins bs)" "y \<in> set_bin (bins bs ! k)"
  shows "\<forall>x \<in> set (Complete_it k y bs). wf_item cfg inp x \<and> item_end x = k"
  using assms wf_bins_kth_bin[OF assms]
  unfolding Complete_it_def wf_bins_def wf_bin_def wf_item_def inc_item_def next_symbol_def
            is_complete_def item_rule_body_def
  by (auto, metis le_less_trans, metis le_less_trans le_trans)

lemma Ex_wf_bins:
  "\<exists>n bs inp cfg. n \<le> length inp \<and> length (bins bs) = Suc (length inp) \<and> wf_cfg cfg \<and> wf_bins cfg inp bs"
  apply (rule exI[where x="0"])
  apply (rule exI[where x="Bins [Bin []]"])
  apply (rule exI[where x="[]"])
  apply (auto simp: wf_bins_def wf_bin_def wf_cfg_defs split: prod.splits)
  by (metis cfg.sel distinct.simps(1) empty_iff empty_set inf_bot_right list.set_intros(1))

definition wellformed_bins :: "(nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins) set" where
  "wellformed_bins = { 
    (k, cfg, inp, bs) | k cfg inp bs.
      k \<le> length inp \<and>
      length (bins bs) = length inp + 1 \<and>
      wf_cfg cfg \<and>
      wf_bins cfg inp bs
  }"

typedef 'a wf_bins = "wellformed_bins::(nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins) set"
  morphisms from_wf_bins to_wf_bins
  using Ex_wf_bins by (auto simp: wellformed_bins_def)

lemma wellformed_bins_elim:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "k \<le> length inp \<and> length (bins bs) = length inp + 1 \<and> wf_cfg cfg \<and> wf_bins cfg inp bs"
  using assms(1) from_wf_bins wellformed_bins_def by (smt (verit) mem_Collect_eq old.prod.inject)

lemma wellformed_bins_intro:
  assumes "k \<le> length inp" "length (bins bs) = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
  shows "(k, cfg, inp, bs) \<in> wellformed_bins"
  by (simp add: assms wellformed_bins_def)

fun earley_measure :: "nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins \<Rightarrow> nat \<Rightarrow> nat" where
  "earley_measure (k, cfg, inp, bs) i = card { x | x. wf_item cfg inp x \<and> item_end x = k } - i"

lemma \<pi>_it'_simps[simp]:
  "i \<ge> length (items (bins bs ! k)) \<Longrightarrow> \<pi>_it' k cfg inp bs i = bs"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = None \<Longrightarrow>
    \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (app_bins bs k (Complete_it k x bs)) (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    is_terminal cfg a \<Longrightarrow> k < length inp \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (app_bins bs (k+1) (Scan_it k inp a x)) (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    is_terminal cfg a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp bs (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    \<not> is_terminal cfg a \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (app_bins bs k (Predict_it k cfg a)) (i+1)"
  by (subst \<pi>_it'.simps, simp)+

lemma \<pi>_it'_induct[case_names Base Complete Scan Pass Predict]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes base: "\<And>k cfg inp bs i. i \<ge> length (items (bins bs ! k)) \<Longrightarrow> P k cfg inp bs i"
  assumes complete: "\<And>k cfg inp bs i x. \<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = None \<Longrightarrow> P k cfg inp (app_bins bs k (Complete_it k x bs)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes scan: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal cfg a \<Longrightarrow> k < length inp \<Longrightarrow> 
            P k cfg inp (app_bins bs (k+1) (Scan_it k inp a x)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes pass: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal cfg a \<Longrightarrow> \<not> k < length inp \<Longrightarrow>
            P k cfg inp bs (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes predict: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> \<not> is_terminal cfg a \<Longrightarrow> 
            P k cfg inp (app_bins bs k (Predict_it k cfg a)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  shows "P k cfg inp bs i"
  using assms(1)
proof (induction n\<equiv>"earley_measure (k, cfg, inp, bs) i" arbitrary: bs i rule: nat_less_induct)
  case 1
  have wf: "k \<le> length inp" "length (bins bs) = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using "1.prems" wellformed_bins_elim by metis+
  hence k: "k < length (bins bs)"
    by simp
  have fin: "finite { x | x. wf_item cfg inp x \<and> item_end x = k }"
    using finiteness_UNIV_wf_item by fastforce
  show ?case
  proof cases
    assume "i \<ge> length (items (bins bs ! k))"
    then show ?thesis
      by (simp add: base)
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
    let ?x = "items (bins bs ! k) ! i"
    have x: "?x \<in> set_bin (bins bs ! k)"
      using a1 by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "app_bins bs k (Complete_it k ?x bs)"
      have "item_origin ?x < length (bins bs)"
        using wf(4) k wf_bins_kth_bin wf_item_def x by (metis order_le_less_trans)
      hence wf_bins': "wf_bins cfg inp ?bs'"
        using wf_bins_Complete_it distinct_Complete_it wf(4) wf_bins_app_bins k x by fastforce
      hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
        using wf(1,2,3) wellformed_bins_intro by fastforce
      have sub: "set (items (bins ?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
        using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def using order_le_less_trans by auto
      have "i < length (items (bins ?bs' ! k))"
        using a1 by (meson leI length_nth_bin_app_bins order.trans)
      also have "... = card (set (items (bins ?bs' ! k)))"
        using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
        by (metis Suc_eq_plus1 le_imp_less_Suc length_bins_app_bins)
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
          let ?bs' = "app_bins bs (k+1) (Scan_it k inp a ?x)"
          have wf_bins': "wf_bins cfg inp ?bs'"
            using wf_bins_Scan_it distinct_Scan_it wf(1,4) wf_bins_app_bins a2 k x by metis
          hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
            using wf(1,2,3) wellformed_bins_intro by fastforce
          have sub: "set (items (bins ?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
            using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def using order_le_less_trans by auto
          have "i < length (items (bins ?bs' ! k))"
            using a1 by (meson leI length_nth_bin_app_bins order.trans)
          also have "... = card (set (items (bins ?bs' ! k)))"
            using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
            by (metis Suc_eq_plus1 le_imp_less_Suc length_bins_app_bins)
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
          have sub: "set (items (bins bs ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
            using wf(1,2,4) unfolding wf_bin_def wf_bins_def using order_le_less_trans by auto
          have "i < length (items (bins bs ! k))"
            using a1 by simp
          also have "... = card (set (items (bins bs ! k)))"
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
        let ?bs' = "app_bins bs k (Predict_it k cfg a)"
        have wf_bins': "wf_bins cfg inp ?bs'"
          using wf_bins_Predict_it distinct_Predict_it wf(1,3,4) wf_bins_app_bins k x by metis
        hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
          using wf(1,2,3) wellformed_bins_intro by fastforce
        have sub: "set (items (bins ?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
          using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def using order_le_less_trans by auto
        have "i < length (items (bins ?bs' ! k))"
          using a1 by (meson leI length_nth_bin_app_bins order.trans)
        also have "... = card (set (items (bins ?bs' ! k)))"
          using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
          by (metis Suc_eq_plus1 le_imp_less_Suc length_bins_app_bins)
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


subsection \<open>Auxiliary lemmas\<close>

lemma length_bins_Init_it[simp]:
  "length (bins (Init_it cfg inp)) = length inp + 1"
  unfolding Init_it_def using length_bins_app_bins by force

lemma length_bins_\<pi>_it'[simp]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (bins (\<pi>_it' k cfg inp bs i)) = length (bins bs)"
  by (induction i rule: \<pi>_it'_induct[OF assms]) auto

lemma length_bins_\<pi>_it[simp]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (bins (\<pi>_it k cfg inp bs)) = length (bins bs)"
  using assms unfolding \<pi>_it_def by simp

lemma length_nth_bin_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (items (bins (\<pi>_it' k cfg inp bs i) ! l)) \<ge> length (items (bins bs ! l))"
  using length_nth_bin_app_bins order_trans
  by (induction i rule: \<pi>_it'_induct[OF assms]) (auto, blast+)

lemma wf_bins_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "wf_bins cfg inp (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have wf: "k \<le> length inp" "length (bins bs) = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using Complete.prems wellformed_bins_elim by metis+
  have "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by force
  hence "wf_bins cfg inp ?bs'"
    using wf_bins_app_bins Complete.hyps(2) wf_bins_Complete_it 
      distinct_Complete_it wf_bins_kth_bin wf_item_def wf(1,2,4)
    by (smt (verit, ccfv_SIG) Suc_eq_plus1 le_imp_less_Suc le_trans)
  thus ?case
    using Complete.IH Complete.hyps wf(1,2,3) wellformed_bins_intro by fastforce
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k inp a x)"
  have wf: "k \<le> length inp" "length (bins bs) = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using Scan.prems wellformed_bins_elim by metis+
  have "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by force
  hence "wf_bins cfg inp ?bs'"
    using wf_bins_Scan_it wf_bins_app_bins Scan.hyps(3,5) distinct_Scan_it wf(1,2,4)
    by (metis option.simps(3) trans_less_add1)
  thus ?case
    using Scan.IH Scan.hyps wf(1,2,3) wellformed_bins_intro by (metis \<pi>_it'_simps(3) length_bins_app_bins)
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k cfg a)"
  have wf: "k \<le> length inp" "length (bins bs) = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using Predict.prems wellformed_bins_elim by metis+
  have "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by force
  hence "wf_bins cfg inp ?bs'"
    using Suc_eq_plus1 Suc_le_eq Suc_le_mono wf_bins_Predict_it wf
      wf_bins_app_bins distinct_Predict_it by metis
  thus ?case
    using Predict.IH Predict.hyps wf(1,2,3) wellformed_bins_intro
    by (metis \<pi>_it'_simps(5) length_bins_app_bins)
qed (auto simp: wellformed_bins_elim)

lemma wf_bins_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "wf_bins cfg inp (\<pi>_it k cfg inp bs)"
  using assms \<pi>_it_def wf_bins_\<pi>_it' by metis

lemma kth_\<pi>_it'_bins:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  assumes "j < length (items (bins bs ! l))"
  shows "items (bins (\<pi>_it' k cfg inp bs i) ! l) ! j = items (bins bs ! l) ! j"
  using assms(2)
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have "items (bins (\<pi>_it' k cfg inp ?bs' (i + 1)) ! l) ! j = items (bins ?bs' ! l) ! j"
    using Complete.IH Complete.prems length_nth_bin_app_bins order.strict_trans2 by blast
  also have "... = items (bins bs ! l) ! j"
    using kth_app_bins nth_app_bins Complete.prems by metis
  finally show ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k inp a x)"
  have "items (bins (\<pi>_it' k cfg inp ?bs' (i + 1)) ! l) ! j = items (bins ?bs' ! l) ! j"
    using Scan.IH Scan.prems length_nth_bin_app_bins order.strict_trans2 by blast
  also have "... = items (bins bs ! l) ! j"
    using kth_app_bins nth_app_bins Scan.prems by metis
  finally show ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k cfg a)"
  have "items (bins (\<pi>_it' k cfg inp ?bs' (i + 1)) ! l) ! j = items (bins ?bs' ! l) ! j"
    using Predict.IH Predict.prems length_nth_bin_app_bins order.strict_trans2 by blast
  also have "... = items (bins bs ! l) ! j"
    using kth_app_bins nth_app_bins Predict.prems by metis
  finally show ?case
    using Predict.hyps by simp
qed simp_all

lemma nth_bin_sub_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "set_bin (bins bs ! l) \<subseteq> set_bin (bins (\<pi>_it' k cfg inp bs i) ! l)"
proof standard
  fix x
  assume "x \<in> set_bin (bins bs ! l)"
  then obtain j where *: "j < length (items (bins bs ! l))" "items (bins bs ! l) ! j = x"
    using set_bin_def in_set_conv_nth by metis
  have "x = items (bins (\<pi>_it' k cfg inp bs i) ! l) ! j"
    using kth_\<pi>_it'_bins assms * by metis
  moreover have "j < length (items (bins (\<pi>_it' k cfg inp bs i) ! l))"
    using assms *(1) length_nth_bin_\<pi>_it' less_le_trans by blast
  ultimately show "x \<in> set_bin (bins (\<pi>_it' k cfg inp bs i) ! l)"
    by simp
qed

lemma set_bin_\<pi>_it'_eq:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "l < k \<Longrightarrow> set_bin (bins (\<pi>_it' k cfg inp bs i) ! l) = set_bin (bins bs ! l)"
  by (induction i rule: \<pi>_it'_induct[OF assms]) (auto simp: app_bins_def nth_app_bins)

lemma set_bins_upto_k0_\<pi>_it'_eq:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "set_bins_upto (\<pi>_it k cfg inp bs) k 0 = set_bins_upto bs k 0"
  unfolding set_bins_upto_def set_bin_upto_def \<pi>_it_def using set_bin_\<pi>_it'_eq assms by fast

lemma wf_bins_Init_it:
  assumes "wf_cfg cfg"
  shows "wf_bins cfg inp (Init_it cfg inp)"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg)"
  let ?b0 = "Bin (map (\<lambda>r. init_item r 0) ?rs)"
  let ?bs = "replicate (length inp + 1) (Bin [])"
  have "wf_bin cfg inp 0 ?b0"
    using assms unfolding wf_bin_def wf_item_def wf_cfg_def distinct_rules_def
    by (auto simp: init_item_def distinct_map inj_on_def)
  moreover have "wf_bins cfg inp (Bins ?bs)"
    unfolding wf_bins_def wf_bin_def using less_Suc_eq_0_disj by force
  ultimately show ?thesis
    using wf_bins_app_bins unfolding wf_bin_def Init_it_def by (metis bin.sel)
qed

lemma length_wf_bins_\<I>_it[simp]:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "length (bins (\<I>_it k cfg inp)) = length (bins (Init_it cfg inp)) \<and> wf_bins cfg inp (\<I>_it k cfg inp)"
  using assms
proof (induction k)
  case 0
  have "(k, cfg, inp, Init_it cfg inp) \<in> wellformed_bins"
    using wellformed_bins_intro "0.prems" wf_bins_Init_it length_bins_Init_it assms(1) by blast
  thus ?case
    using 0 by (auto simp: assms(2) wellformed_bins_elim wellformed_bins_intro wf_bins_Init_it wf_bins_\<pi>_it)
next
  case (Suc k)
  have "(Suc k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
    by (simp add: Suc.IH Suc.prems(1) Suc_leD assms(2) wellformed_bins_intro)
  thus ?case
    using Suc.IH Suc.prems length_bins_\<pi>_it wf_bins_\<pi>_it by auto
qed

lemma wf_bins_\<II>_it:
  "wf_cfg cfg \<Longrightarrow> wf_bins cfg inp (\<II>_it cfg inp)"
  unfolding \<II>_it_def using length_wf_bins_\<I>_it by auto


subsection \<open>List to Set\<close>

lemma Init_it_eq_Init:
  "set_bins (Init_it cfg inp) = Init cfg"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg)"
  let ?b0 = "map (\<lambda>r. init_item r 0) ?rs"
  let ?bs = "Bins (replicate (length inp + 1) (Bin []))"
  have "set_bins ?bs = {}"
    unfolding set_bins_def set_bins_upto_def set_bin_def set_bin_upto_def
    by (auto simp del: replicate_Suc)
  hence "set_bins (Init_it cfg inp) = set ?b0"
    by (auto simp: Init_it_def set_bins_app_bins)
  thus ?thesis
    unfolding Init_def rule_head_def by auto
qed

lemma Scan_it_sub_Scan:
  assumes "wf_bins cfg inp bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some a"
  shows "set (Scan_it k inp a x) \<subseteq> Scan k inp I"
proof standard
  fix y
  assume *: "y \<in> set (Scan_it k inp a x)"
  have "x \<in> bin I k"
    using kth_bin_in_bins assms(1-4) set_bin_def wf_bin_def wf_bins_def bin_def by blast
  {
    assume #: "k < length inp" "inp!k = a"
    hence "y = inc_item x (k+1)"
      using * unfolding Scan_it_def by simp
    hence "y \<in> Scan k inp I"
      using \<open>x \<in> bin I k\<close> # assms(5) unfolding Scan_def by blast
  }
  thus "y \<in> Scan k inp I"
    using * unfolding Scan_it_def by fastforce
qed

lemma Predict_it_sub_Predict:
  assumes "wf_bins cfg inp bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some X"
  shows "set (Predict_it k cfg X) \<subseteq> Predict k cfg I"
proof standard
  fix y
  assume *: "y \<in> set (Predict_it k cfg X)"
  have "x \<in> bin I k"
    using kth_bin_in_bins assms(1-4) set_bin_def wf_bin_def wf_bins_def bin_def by blast
  let ?rs = "filter (\<lambda>r. rule_head r = X) (\<RR> cfg)"
  let ?xs = "map (\<lambda>r. init_item r k) ?rs"
  have "y \<in> set ?xs"
    using * unfolding Predict_it_def by simp
  then obtain r where "y = init_item r k" "rule_head r = X" "r \<in> set (\<RR> cfg)" "next_symbol x = Some (rule_head r)"
    using assms(5) by auto
  thus "y \<in> Predict k cfg I"
    unfolding Predict_def using \<open>x \<in> bin I k\<close> by blast
qed

lemma Complete_it_sub_Complete:
  assumes "wf_bins cfg inp bs" "set_bins bs \<subseteq> I" "y \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
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
    using set_bin_def wf_bins_def wf_bin_def wf_item_def assms(1,3,4)
    by (metis Orderings.preorder_class.dual_order.strict_trans1 leD not_le_imp_less)
  hence "\<forall>z \<in> set ?xs. z \<in> bin I (item_origin y)"
     using wf_bin_def wf_bins_def bin_def assms kth_bin_in_bins set_bin_def
     by (metis (mono_tags, lifting) filter_is_subset in_mono mem_Collect_eq)
  then obtain z where "x = inc_item z k" "next_symbol z = Some (item_rule_head y)" "z \<in> bin I (item_origin y)"
    using * Complete_it_def by (smt (verit, best) filter_set imageE list.set_map member_filter)
  thus "x \<in> Complete k I"
    using \<open>y \<in> bin I k\<close> assms(5) unfolding Complete_def next_symbol_def by (auto split: if_splits)
qed

lemma \<pi>_it'_sub_\<pi>:
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "set_bins bs \<subseteq> I" "length (bins bs) = length inp + 1"
  assumes "k < length (bins bs)"
  shows "set_bins (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp I"
  using assms
proof (induction k cfg inp bs i arbitrary: I rule: \<pi>_it'_induct)
  case (Base k cfg inp bs i)
  thus ?case
    using \<pi>_mono by fastforce
next
  case (Complete k cfg inp bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by force
  have "set_bins ?bs' \<subseteq> I \<union> Complete k I"
    using 0 Complete_it_sub_Complete Complete.hyps(3) Complete.prems(2,3,5) set_bins_app_bins Un_mono by metis
  moreover have "wf_bins cfg inp ?bs'"
    using 0 wf_bins_app_bins Complete.hyps(2) Complete.prems(2,5) wf_bins_Complete_it 
      distinct_Complete_it wf_bins_kth_bin wf_item_def by (smt (verit) le_trans linorder_not_less)
  ultimately have "set_bins (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp (I \<union> Complete k I)"
    using Complete.IH Complete.hyps Complete.prems(1,4,5) by simp
  thus ?case
    using Complete_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k inp a x)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by force
  have "set_bins ?bs' \<subseteq> I \<union> Scan k inp I"
    using 0 Scan_it_sub_Scan[OF Scan.prems(2,3) 0 Scan.prems(5) Scan.hyps(3)]
          Scan.hyps(5) Scan.prems(3,4) by (auto simp: set_bins_app_bins)
  moreover have "wf_bins cfg inp ?bs'"
    using 0 wf_bins_Scan_it wf_bins_app_bins Scan.hyps(3,5) Scan.prems(2,5) distinct_Scan_it
    by (metis less_imp_le_nat option.simps(3))
  ultimately have "set_bins (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp (I \<union> Scan k inp I)"
    using Scan.IH Scan.hyps Scan.prems(1,4,5) by simp
  thus ?case
    using Scan_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
next
  case (Pass k cfg inp bs i x a)
  thus ?case
    using \<pi>_it'_simps(4) by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k cfg a)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by force
  have "set_bins ?bs' \<subseteq> I \<union> Predict k cfg I"
    using 0 Predict_it_sub_Predict Predict.hyps(3) Predict.prems(2,3,5) set_bins_app_bins Un_mono by metis
  moreover have "wf_bins cfg inp ?bs'"
    using Suc_eq_plus1 Suc_le_eq Suc_le_mono Predict.prems(1,2,4,5) wf_bins_Predict_it
      wf_bins_app_bins distinct_Predict_it by metis
  ultimately have "set_bins (\<pi>_it' k cfg inp bs i)  \<subseteq> \<pi> k cfg inp (I \<union> Predict k cfg I)"
    using Predict.IH Predict.hyps Predict.prems(1,4,5) by simp
  thus ?case
    using Predict_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
qed

lemma \<pi>_it_sub_\<pi>:
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "set_bins bs \<subseteq> I" "length (bins bs) = length inp + 1" "k < length (bins bs)"
  shows "set_bins (\<pi>_it k cfg inp bs) \<subseteq> \<pi> k cfg inp I"
  using assms \<pi>_it'_sub_\<pi> \<pi>_it_def by metis

lemma \<I>_it_sub_\<I>:
  "wf_cfg cfg \<Longrightarrow> k < length (bins (Init_it cfg inp)) \<Longrightarrow> set_bins (\<I>_it k cfg inp) \<subseteq> \<I> k cfg inp"
  by (induction k) (auto simp: Init_it_eq_Init \<pi>_it_sub_\<pi> wf_bins_Init_it wf_bins_\<I>_it)

lemma \<II>_it_sub_\<II>:
  "wf_cfg cfg \<Longrightarrow> set_bins (\<II>_it cfg inp) \<subseteq> \<II> cfg inp"
  using \<I>_it_sub_\<I> \<II>_def \<II>_it_def by (metis length_bins_Init_it less_add_one)

subsection \<open>Soundness\<close>

lemma sound_Scan_it:
  assumes "wf_bins cfg inp bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some a" "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (Scan_it k inp a x))"
  using sound_Scan Scan_it_sub_Scan assms by (smt (verit, best) sound_items_def subsetD)

lemma sound_Predict_it:
  assumes "wf_bins cfg inp bs" "set_bins bs \<subseteq> I" "x \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol x = Some X" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (Predict_it k cfg X))"
  using sound_Predict Predict_it_sub_Predict sound_items_def assms by (smt (verit, ccfv_SIG) in_mono)

lemma sound_Complete_it:
  assumes "wf_bins cfg inp bs" "set_bins bs \<subseteq> I" "y \<in> set_bin (bins bs ! k)" "k < length (bins bs)"
  assumes "next_symbol y = None" "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (Complete_it k y bs))"
  using sound_Complete Complete_it_sub_Complete sound_items_def assms by (metis (no_types, lifting) subsetD)

lemma sound_\<pi>_it':
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "sound_items cfg inp (set_bins bs)"
  shows "sound_items cfg inp (set_bins (\<pi>_it' k cfg inp bs i))"
  using assms
proof (induction k cfg inp bs i rule: \<pi>_it'_induct)
  case (Complete k cfg inp bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by force
  have "wf_bins cfg inp ?bs'"
    using 0 Complete.prems(2,3) wf_bins_Complete_it wf_bins_app_bins distinct_Complete_it
      wf_bins_kth_bin wf_item_def by (smt (verit, ccfv_SIG) le_trans nat_less_le nle_le)
  moreover have "sound_items cfg inp (set (Complete_it k x bs))"
    using 0 sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems(2,3,5) set_bins_bin_exists 
            sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def by metis
  ultimately have "sound_items cfg inp (set_bins (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Complete.IH Complete.prems(1,2-5) sound_items_def by (auto simp: set_bins_app_bins; blast)
  thus ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k inp a x)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by force
  have "wf_bins cfg inp ?bs'"
    using 0 Scan.prems(2,3) wf_bins_Scan_it wf_bins_app_bins Scan.hyps(3,5) distinct_Scan_it
    by (metis nat_less_le option.distinct(1))
  moreover have "sound_items cfg inp (set (Scan_it k inp a x))"
    using 0 sound_Scan_it \<pi>_mono Scan.hyps(3) Scan.prems(2,3,5) set_bins_bin_exists 
            sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def by metis
  ultimately have "sound_items cfg inp (set_bins (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Scan.IH Scan.prems(1,3-5) sound_items_def Scan.hyps(5) by (auto simp: set_bins_app_bins; blast)
  thus ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k cfg a)"
  have 0: "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by force
  have "wf_bins cfg inp ?bs'"
    using 0 Predict.prems(1-5) wf_bins_Predict_it wf_bins_app_bins distinct_Predict_it wf_bins_kth_bin by fastforce
  moreover have "sound_items cfg inp (set (Predict_it k cfg a))"
    using 0 sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems(1-3,5) set_bins_bin_exists 
            sound_\<pi> wf_bins_kth_bin wf_items_def by metis
  ultimately have "sound_items cfg inp (set_bins (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Predict.IH Predict.prems(1,3-5) sound_items_def by (auto simp: set_bins_app_bins; blast)
  thus ?case
    using Predict.hyps by simp
qed simp_all

lemma sound_\<pi>_it:
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "sound_items cfg inp (set_bins bs)"
  shows "sound_items cfg inp (set_bins (\<pi>_it k cfg inp bs))"
  using sound_\<pi>_it' assms \<pi>_it_def by metis

subsection \<open>Set to List\<close>

lemma bin_set_bins_upto_set_bins_eq:
  assumes "wf_bins cfg inp bs" "k < length (bins bs)" "i \<ge> length (items (bins bs ! k))" "l \<le> k"
  shows "bin (set_bins_upto bs k i) l = bin (set_bins bs) l"
  unfolding set_bins_upto_def set_bins_def bin_def using assms nat_less_le
  by (auto simp: nth_list_update set_bin_upto_eq_set_bin wf_bins_kth_bin, metis less_trans, blast)

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
  "wf_bins cfg inp bs \<Longrightarrow> x \<in> set_bins bs \<Longrightarrow> item_end x = k \<Longrightarrow> x \<in> set_bin (bins bs ! k)"
  using set_bins_bin_exists wf_bins_kth_bin wf_bins_def by blast

lemma Complete_set_bins_upto_eq_set_bins:
  assumes "wf_bins cfg inp bs" "k < length (bins bs)" "i \<ge> length (items (bins bs ! k))"
  shows "Complete k (set_bins_upto bs k i) = Complete k (set_bins bs)"
proof -
  have "\<And>l. l \<le> k \<Longrightarrow> bin (set_bins_upto bs k i) l = bin (set_bins bs) l"
    using bin_set_bins_upto_set_bins_eq[OF assms] by blast
  moreover have "wf_items cfg inp (set_bins bs)"
    using assms(1) wf_bins_impl_wf_items by metis
  ultimately show ?thesis
    unfolding Complete_def bin_def wf_items_def wf_item_def by auto
qed

lemma Complete_sub_set_bins_Un_Complete_it:
  assumes "Complete k I \<subseteq> set_bins bs" "I \<subseteq> set_bins bs" "is_complete z" "wf_bins cfg inp bs" "wf_item cfg inp z"
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
      using *(5) assms(3) by (auto simp: next_symbol_def)
  next
    case B
    let ?orig = "bins bs ! item_origin z"
    let ?is = "filter (\<lambda>x. next_symbol x = Some (item_rule_head z)) (items ?orig)"
    have "x \<in> bin I (item_origin y)"
      using B *(2) *(5) assms(3) by (auto simp: next_symbol_def bin_def)
    moreover have "bin I (item_origin z) \<subseteq> set_bin (bins bs ! item_origin z)"
      using wf_item_in_kth_bin assms(2,4) bin_def by blast
    ultimately have "x \<in> set ?is"
      using *(5) B set_bin_def by (simp add: in_mono)
    thus ?thesis
      unfolding Complete_it_def *(1) by simp
  next
    case 3
    thus ?thesis
      using * assms(1) Complete_def by (auto simp: bin_def; blast)
  qed
qed

lemma Complete_it_eq_item_origin:
  assumes "set_bin (bins bs ! item_origin x) = set_bin (bins bs' ! item_origin x)"
  shows "set (Complete_it k x bs) = set (Complete_it k x bs')"
  using assms unfolding Complete_it_def by simp

lemma kth_bin_set_bins_upto_empty:
  assumes "wf_bins cfg inp bs" "k < length (bins bs)"
  shows "bin (set_bins_upto bs k 0) k = {}"
proof -
  {
    fix x
    assume "x \<in> set_bins_upto bs k 0"
    then obtain l where "x \<in> set_bin (bins bs ! l)" "l < k"
      unfolding set_bins_upto_def set_bin_upto_def by blast
    hence "item_end x = l"
      using wf_bins_kth_bin assms by fastforce
    hence "item_end x < k"
      using \<open>l < k\<close> by blast
  }
  thus ?thesis
    by (auto simp: bin_def)
qed

lemma \<pi>_it'_mono:
  assumes "k < length (bins bs)" "length (bins bs) = length inp + 1"
  shows "set_bins bs \<subseteq> set_bins (\<pi>_it' k cfg inp bs i)"
  using assms by (induction k cfg inp bs i rule: \<pi>_it'_induct) (auto simp: set_bins_app_bins)

lemma \<pi>_step_sub_\<pi>_it':
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k cfg inp (set_bins_upto bs k i) \<subseteq> set_bins bs"
  assumes "sound_items cfg inp (set_bins bs)" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi>_step k cfg inp (set_bins bs) \<subseteq> set_bins (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction k cfg inp bs i rule: \<pi>_it'_induct)
  case (Base k cfg inp bs i)
  have "bin (set_bins bs) k = bin (set_bins_upto bs k i) k"
    using Base.hyps Base.prems(2,3) bin_set_bins_upto_set_bins_eq by blast
  thus ?case
    using Scan_bin_absorb Predict_bin_absorb Complete_set_bins_upto_eq_set_bins 
      Base.hyps Base.prems(1,2,3,5) \<pi>_step_def
    by (smt (verit, del_insts) \<pi>_it'_simps(1) dual_order.order_iff_strict sup.bounded_iff)
next
  case (Complete k cfg inp bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by auto
  have wf: "wf_bins cfg inp ?bs'"
    using Complete.hyps Complete.prems(2,3) wf_bins_Complete_it wf_bins_app_bins set_bin_def
      distinct_Complete_it wf_bins_kth_bin wf_item_def x by (smt (verit, best) le_trans nat_less_le nle_le)
  have sound: "sound_items cfg inp (set_bins ?bs')"
    using sound_Complete_it[OF _ _ _ Complete.prems(3) Complete.hyps(3)] wf_bins_impl_wf_items 
          Complete.hyps(1,2) sound_items_def Complete.prems(1,2,3,6) by (auto simp: set_bins_app_bins; fastforce)
  have "Scan k inp (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Scan k inp (set_bins_upto ?bs' k (i + 1)) = Scan k inp (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using Complete.hyps(1) set_bins_upto_Suc_Un length_nth_bin_app_bins by (metis less_le_trans not_le_imp_less)
    also have "... = Scan k inp (set_bins_upto bs k i \<union> {x})"
      using Complete.hyps(1,2) Complete.prems(3) kth_app_bins set_bins_upto_kth_nth_id by (metis leI less_not_refl)
    also have "... \<subseteq> set_bins bs \<union> Scan k inp {x}"
      using Complete.prems(4,5) Scan_Un Scan_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Complete.hyps(3) Complete.prems(1,2) kth_bin_in_bins wf_bins_kth_bin by (auto simp: Scan_def bin_def)
    finally show ?thesis
      using Complete.prems(3) by (auto simp: set_bins_app_bins)
  qed
  moreover have "Predict k cfg (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Predict k cfg (set_bins_upto ?bs' k (i + 1)) = Predict k cfg (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using Complete.hyps(1) set_bins_upto_Suc_Un length_nth_bin_app_bins by (metis less_le_trans not_le_imp_less)
    also have "... = Predict k cfg (set_bins_upto bs k i \<union> {x})"
      using Complete.hyps(1,2) Complete.prems(3) kth_app_bins set_bins_upto_kth_nth_id by (metis linorder_not_less nle_le)
    also have "... \<subseteq> set_bins bs \<union> Predict k cfg {x}"
      using Complete.prems(4,5) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Complete.hyps(3) Complete.prems(1,2) kth_bin_in_bins wf_bins_kth_bin by (auto simp: Predict_def bin_def)
    finally show ?thesis
      using Complete.prems(3) by (auto simp: set_bins_app_bins)
  qed
  moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un length_nth_bin_app_bins Complete.hyps(1) by (metis less_le_trans not_le_imp_less)
    also have "... = Complete k (set_bins_upto bs k i \<union> {x})"
      using kth_app_bins Complete.hyps(1,2) set_bins_upto_kth_nth_id Complete.prems(3) by (metis leI le_refl)
    also have "... \<subseteq> set_bins bs \<union> set (Complete_it k x bs)"
      using Complete_sub_set_bins_Un_Complete_it Complete.hyps(3) Complete.prems(2,3,5) next_symbol_def
        set_bins_upto_sub_set_bins wf_bins_kth_bin x by (metis Complete_\<pi>_step_mono Option.option.simps(3) subset_trans)
    finally show ?thesis
      using Complete.prems(3) set_bins_app_bins by blast
  qed
  ultimately have "\<pi>_step k cfg inp (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Complete.IH Complete.prems(1,3,4,7,8) sound wf \<pi>_step_def set_bins_upto_sub_set_bins
    by (metis (no_types, lifting) Un_assoc length_bins_app_bins subset_Un_eq)
  thus ?case
    using \<pi>_it'_simps(2) \<pi>_step_sub_mono Complete.hyps Complete.prems(3) set_bins_app_bins
    by (smt (verit, del_insts) Orderings.preorder_class.dual_order.trans Un_upper1)
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k inp a x)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by auto
  have wf: "wf_bins cfg inp ?bs'"
    using Scan.prems(2,3) Scan.hyps wf_bins_app_bins wf_bins_Scan_it x distinct_Scan_it by (metis Option.option.discI nat_less_le)
  have sound: "sound_items cfg inp (set_bins ?bs')"
    using sound_Scan_it[OF Scan.prems(2) _ x Scan.prems(3)] Scan.hyps(3,5) Scan.prems(2,4,6) 
          sound_items_def wf_bins_impl_wf_items by (auto simp: set_bins_app_bins; fastforce)
  have "Scan k inp (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Scan k inp (set_bins_upto ?bs' k (i + 1)) = Scan k inp (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un Scan.hyps(1) nth_app_bins
      by (metis Groups.monoid_add_class.add.right_neutral One_nat_def add_Suc_right lessI less_not_refl not_le_imp_less)
    also have "... = Scan k inp (set_bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(4) nth_app_bins set_bins_upto_kth_nth_id
      by (metis (no_types, lifting) Suc_eq_plus1 Suc_less_eq lessI linorder_not_less nat_less_le)
    also have "... \<subseteq> set_bins bs \<union> Scan k inp {x}"
      using Scan.prems(4,5) Scan_Un Scan_\<pi>_step_mono by fastforce
    finally have *: "Scan k inp (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs \<union> Scan k inp {x}" .
    show ?thesis
    proof cases
      assume a1: "inp!k = a"
      hence "Scan k inp {x} = {inc_item x (k+1)}"
        using Scan.hyps(1-3,5) Scan.prems(2,3) apply (auto simp: Scan_def bin_def)
        using wf_bins_kth_bin x by blast
      hence "Scan k inp (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs \<union> {inc_item x (k+1)}"
        using * by blast
      also have "... = set_bins bs \<union> set (Scan_it k inp a x)"
        using Scan_it_def a1 Scan.hyps(5) by (metis empty_set list.simps(15))
      also have "... = set_bins ?bs'"
        using Scan.hyps(5) Scan.prems(4) by (auto simp: set_bins_app_bins)
      finally show ?thesis .
    next
      assume a1: "\<not> inp!k = a"
      hence "Scan k inp {x} = {}"
        using Scan.hyps(3) by (auto simp: Scan_def bin_def)
      hence "Scan k inp (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins bs"
        using * by blast
      also have "... \<subseteq> set_bins ?bs'"
        using Scan.hyps(5) Scan.prems(4) by (auto simp: set_bins_app_bins)
      finally show ?thesis .
    qed
  qed
  moreover have "Predict k cfg (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Predict k cfg (set_bins_upto ?bs' k (i + 1)) = Predict k cfg (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un Scan.hyps(1) nth_app_bins by (metis Suc_eq_plus1 lessI less_not_refl not_le_imp_less)
    also have "... = Predict k cfg (set_bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(4) nth_app_bins set_bins_upto_kth_nth_id
      by (metis Suc_eq_plus1 add_less_cancel_left le_add1 lessI less_not_refl not_le_imp_less plus_1_eq_Suc)
    also have "... \<subseteq> set_bins bs \<union> Predict k cfg {x}"
      using Scan.prems(4,5) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Scan.hyps(3,4) Scan.prems(1) is_terminal_nonterminal by (auto simp: Predict_def bin_def rule_head_def; fastforce) 
    finally show ?thesis
      using Scan.hyps(5) Scan.prems(4) by (auto simp: set_bins_app_bins)
  qed
  moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un Scan.hyps(1) nth_app_bins by (metis Suc_eq_plus1 lessI less_not_refl not_le_imp_less)
    also have "... = Complete k (set_bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(4) nth_app_bins set_bins_upto_kth_nth_id
      by (metis Suc_eq_plus1 add_less_cancel_left le_add1 lessI less_not_refl not_le_imp_less plus_1_eq_Suc)
    also have "... = Complete k (set_bins_upto bs k i)"
      using Complete_Un_eq_terminal Scan.hyps(3,4) Scan.prems(1,2,3) set_bins_upto_sub_set_bins subset_iff
            wf_bins_impl_wf_items wf_bins_kth_bin wf_items_def x by metis
    finally show ?thesis
      using Scan.hyps(5) Scan.prems(4,5) Complete_\<pi>_step_mono by (auto simp: set_bins_app_bins, blast)
  qed
  ultimately have "\<pi>_step k cfg inp (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Scan.IH Scan.prems(1,3,4,7,8) sound wf \<pi>_step_def set_bins_upto_sub_set_bins by (metis Un_subset_iff length_bins_app_bins)
  thus ?case
    using \<pi>_step_sub_mono \<pi>_it'_simps(3) Scan.hyps Scan.prems(3,4) by (auto simp: set_bins_app_bins, blast)
next
  case (Pass k cfg inp bs i x a)
  have x: "x \<in> set_bin (bins bs ! k)"
    using Pass.hyps(1,2) by auto
  have "Scan k inp (set_bins_upto bs k (i + 1)) \<subseteq> set_bins bs"
    using Scan_def Pass.hyps(5) by auto
  moreover have "Predict k cfg (set_bins_upto bs k (i + 1)) \<subseteq> set_bins bs"
  proof -
    have "Predict k cfg (set_bins_upto bs k (i + 1)) = Predict k cfg (set_bins_upto bs k i \<union> {items (bins bs ! k) ! i})"
      using set_bins_upto_Suc_Un Pass.hyps(1) by (metis leI)
    also have "... = Predict k cfg (set_bins_upto bs k i \<union> {x})"
      using Pass.hyps(1,2,5) nth_app_bins set_bins_upto_kth_nth_id by simp
    also have "... \<subseteq> set_bins bs \<union> Predict k cfg {x}"
      using Pass.prems(4,5) Predict_Un Predict_\<pi>_step_mono by blast
    also have "... = set_bins bs"
      using Pass.hyps(3,4) Pass.prems(1) is_terminal_nonterminal by (auto simp: Predict_def bin_def rule_head_def, force)
    finally show ?thesis
      using set_bins_app_bins Pass.hyps(5) Pass.prems(3) by auto
  qed
  moreover have "Complete k (set_bins_upto bs k (i + 1)) \<subseteq> set_bins bs"
  proof -
    have "Complete k (set_bins_upto bs k (i + 1)) = Complete k (set_bins_upto bs k i \<union> {x})"
      using set_bins_upto_Suc_Un Pass.hyps(1,2) by (metis linorder_not_less)
    also have "... = Complete k (set_bins_upto bs k i)"
      using Complete_Un_eq_terminal Pass.hyps Pass.prems(1,2,3) set_bins_upto_sub_set_bins subset_iff 
            wf_bins_impl_wf_items wf_items_def wf_bins_kth_bin x by metis
    finally show ?thesis
      using Pass.prems(5) Complete_\<pi>_step_mono by blast
  qed
  ultimately have "\<pi>_step k cfg inp (set_bins bs) \<subseteq> set_bins (\<pi>_it' k cfg inp bs (i+1))"
    using Pass.IH Pass.prems \<pi>_step_def set_bins_upto_sub_set_bins by (metis Un_subset_iff)
  thus ?case
    using set_bins_app_bins Pass.hyps Pass.prems by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "app_bins bs k (Predict_it k cfg a)"
  have "k \<ge> length inp \<or> \<not> inp!k = a"
    using Predict.hyps(4) Predict.prems(7) by (metis is_word_is_terminal leI)
  have x: "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by auto
  have len: "i < length (items (bins ?bs' ! k))"
    using length_nth_bin_app_bins Predict.hyps(1) by (metis leI order_less_le_trans)
  have wf: "wf_bins cfg inp ?bs'"
    using Predict.prems(1-4) wf_bins_Predict_it wf_bins_app_bins distinct_Predict_it wf_bins_kth_bin x by fastforce
  have sound: "sound_items cfg inp (set_bins ?bs')" 
    using sound_Predict_it[OF _ _ x] Predict.hyps(3) Predict.prems(1,2,3,6) sound_items_def
    apply (auto simp: set_bins_app_bins)
    by (metis Un_iff dual_order.refl sound_items_def)
  have "item_rule x \<in> set (\<RR> cfg)"
    using Predict.prems(2,3) wf_bins_kth_bin x wf_item_def by blast
  hence "\<forall>s \<in> set (item_rule_body x). s \<in> set (\<NN> cfg) \<union> set (\<TT> cfg)"
    using Predict.prems(1) by (auto simp: wf_cfg_defs item_rule_body_def rule_body_def; fastforce)
  hence "is_terminal cfg a \<or> is_nonterminal cfg a"
    using Predict.hyps(3) by (auto simp: next_symbol_def is_complete_def is_nonterminal_def is_terminal_def split: if_splits)
  hence nonterm: "is_nonterminal cfg a"
    using Predict.hyps(4) by blast
  have "Scan k inp (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Scan k inp (set_bins_upto ?bs' k (i + 1)) = Scan k inp (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using Predict.hyps(1) set_bins_upto_Suc_Un length_nth_bin_app_bins by (metis less_le_trans not_le_imp_less)
    also have "... = Scan k inp (set_bins_upto bs k i \<union> {x})"
      using Predict.hyps(1,2) Predict.prems(3) kth_app_bins set_bins_upto_kth_nth_id by (metis less_not_refl not_le_imp_less)
    also have "... \<subseteq> set_bins bs \<union> Scan k inp {x}"
      using Predict.prems(4,5) Scan_Un Scan_\<pi>_step_mono by fastforce
    also have "... = set_bins bs"
      using Predict.hyps(3) \<open>length inp \<le> k \<or> inp ! k \<noteq> a\<close> by (auto simp: Scan_def bin_def)
    finally show ?thesis
      using Predict.prems(3) by (auto simp: set_bins_app_bins)
  qed
  moreover have "Predict k cfg (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Predict k cfg (set_bins_upto ?bs' k (i + 1)) = Predict k cfg (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using Predict.hyps(1) set_bins_upto_Suc_Un length_nth_bin_app_bins by (metis less_le_trans not_le_imp_less)
    also have "... = Predict k cfg (set_bins_upto bs k i \<union> {x})"
      using Predict.hyps(1,2) Predict.prems(3) kth_app_bins set_bins_upto_kth_nth_id by (metis leI less_or_eq_imp_le)
    also have "... \<subseteq> set_bins bs \<union> Predict k cfg {x}"
      using Predict.prems(4,5) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = set_bins bs \<union> set (Predict_it k cfg a)"
      using Predict.hyps Predict.prems(1-3) apply (auto simp: Predict_def Predict_it_def bin_def)
      using wf_bins_kth_bin x by blast
    finally show ?thesis
      using Predict.prems(3) by (auto simp: set_bins_app_bins)
  qed
  moreover have "Complete k (set_bins_upto ?bs' k (i + 1)) \<subseteq> set_bins ?bs'"
  proof -
    have "Complete k (set_bins_upto ?bs' k (i + 1)) = Complete k (set_bins_upto ?bs' k i \<union> {items (bins ?bs' ! k) ! i})"
      using set_bins_upto_Suc_Un len by force
    also have "... = Complete k (set_bins_upto bs k i \<union> {x})"
      using kth_app_bins Predict.hyps(1,2) Predict.prems(3) set_bins_upto_kth_nth_id by (metis leI nle_le)
    also have "... = Complete k (set_bins_upto bs k i)"
      using Complete_Un_eq_nonterminal[OF Predict.hyps(3) nonterm] Predict.prems(1,2,3,6,8) set_bins_upto_sub_set_bins 
            sound_items_def subset_eq wf_bins_kth_bin x wf_bins_impl_wf_items wf_items_def by metis
    finally show ?thesis
      using set_bins_app_bins Predict.prems(3,5) Complete_\<pi>_step_mono by fastforce
  qed
  ultimately have "\<pi>_step k cfg inp (set_bins ?bs') \<subseteq> set_bins (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Predict.IH Predict.prems(1,3,4,7,8) sound wf \<pi>_step_def set_bins_upto_sub_set_bins 
    by (metis Un_subset_iff length_bins_app_bins)
  thus ?case
    using \<pi>_step_sub_mono \<pi>_it'_simps(5) Predict.hyps Predict.prems(2,3) by (auto simp: set_bins_app_bins, blast)
qed

lemma \<pi>_step_sub_\<pi>_it:
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k cfg inp (set_bins_upto bs k 0) \<subseteq> set_bins bs"
  assumes "sound_items cfg inp (set_bins bs)" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi>_step k cfg inp (set_bins bs) \<subseteq> set_bins (\<pi>_it k cfg inp bs)"
  using assms \<pi>_step_sub_\<pi>_it' \<pi>_it_def by metis

lemma \<pi>_it'_idem:
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "k < length (bins bs)" "length (bins bs) = length inp + 1" "i \<le> j"
  assumes "sound_items cfg inp (set_bins bs)" "nonempty_derives cfg"
  shows "\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j = \<pi>_it' k cfg inp bs i"
  using assms
proof (induction k cfg inp bs i arbitrary: j rule: \<pi>_it'_induct)
  case (Complete k cfg inp bs i x)
  let ?bs' = "app_bins bs k (Complete_it k x bs)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Complete.hyps(1,2) by auto
  have wf: "wf_bins cfg inp ?bs'"
    using Complete.hyps Complete.prems(2,3) wf_bins_Complete_it wf_bins_app_bins
      distinct_Complete_it wf_bins_kth_bin wf_item_def x
    by (smt (verit) linorder_not_less order_trans)
  have sound: "sound_items cfg inp (set_bins ?bs')"
    using sound_Complete_it[OF _ _ _ Complete.prems(3) Complete.hyps(3)] wf_bins_impl_wf_items 
          Complete.hyps(1,2) sound_items_def Complete.prems(1,2,3,6) by (auto simp: set_bins_app_bins; fastforce)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using wf sound Complete by (metis \<pi>_it'_simps(2) length_bins_app_bins)
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Complete.prems(5) by simp
    have "\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j"
      using \<pi>_it'_simps(2) Complete.hyps(1-3) by simp
    also have "... = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_app_bins order_trans by blast
      hence 0: "\<not> length (items (bins ?bs'' ! k)) \<le> j"
        using \<open>i = j\<close> Complete.hyps(1) by linarith
      have "x = items (bins ?bs' ! k) ! j"
        using \<open>i = j\<close> kth_app_bins Complete.hyps(1,2) by (metis not_le_imp_less)
      hence 1: "x = items (bins ?bs'' ! k) ! j"
        using \<open>i = j\<close> kth_\<pi>_it'_bins length_nth_bin_app_bins Complete.hyps(1) by (metis leI order_trans)
      have "\<pi>_it' k cfg inp ?bs'' j = \<pi>_it' k cfg inp (app_bins ?bs'' k (Complete_it k x ?bs'')) (j+1)"
        using \<pi>_it'_simps(2) 0 1 Complete.hyps(1,3) Complete.prems(2) by blast
      moreover have "app_bins ?bs'' k (Complete_it k x ?bs'') = ?bs''"
      proof -
        have "set (Complete_it k x ?bs'') = set (Complete_it k x bs)"
        proof (cases "item_origin x = k")
          case True
          thus ?thesis
            using impossible_complete_item True kth_bin_in_bins Complete.hyps(3) Complete.prems(1,2,3,6,7) 
                  wf_bins_kth_bin x sound_items_def next_symbol_def by (metis option.distinct(1) subsetD)
        next
          case False
          hence "item_origin x < k"
            using x Complete.prems(2,3) wf_bins_kth_bin wf_item_def nat_less_le by blast
          hence "set_bin (bins bs ! item_origin x) = set_bin (bins ?bs'' ! item_origin x)"
            by (smt (verit, best) set_bin_def False nth_app_bins set_bin_\<pi>_it'_eq)
          thus ?thesis
            using Complete_it_eq_item_origin by blast
        qed
        also have "... \<subseteq> set_bin (bins ?bs' ! k)"
          using Complete.prems(3) app_bins_def set_bin_app_bin by (metis bins.sel Un_iff nth_list_update_eq subsetI)
        also have "... \<subseteq> set_bin (bins ?bs'' ! k)"
          using Complete.prems(3) nth_bin_sub_\<pi>_it' by (metis length_bins_app_bins)
        finally have "set (Complete_it k x ?bs'') \<subseteq> set_bin (bins ?bs'' ! k)" .
        thus ?thesis
          using app_bins_eq Complete.prems(2) length_bins_\<pi>_it' length_bins_app_bins by blast
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k cfg inp ?bs' (i + 1)"
      using Complete.IH Complete.prems(1-4,7) \<open>i = j\<close> Complete.hyps length_bins_app_bins 
            wf_bins_Complete_it wf_bins_app_bins x wf sound by simp
    finally show ?thesis
      using Complete.hyps by simp
  qed
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "app_bins bs (k+1) (Scan_it k inp a x)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Scan.hyps(1,2) by auto
  have wf: "wf_bins cfg inp ?bs'"
    using Scan.prems(2,3) Scan.hyps wf_bins_app_bins wf_bins_Scan_it x distinct_Scan_it by (metis Option.option.discI nat_less_le)
  have sound: "sound_items cfg inp (set_bins ?bs')"
    using sound_Scan_it[OF Scan.prems(2) _ x Scan.prems(3)] Scan.hyps(3,5) Scan.prems(2,4,6) 
          set_bins_app_bins sound_items_def wf_bins_impl_wf_items
    by (metis Groups.ab_semigroup_add_class.add.commute Orderings.preorder_class.dual_order.refl UnE add_less_cancel_left)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using wf sound Scan by (metis length_bins_app_bins \<pi>_it'_simps(3))
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Scan.prems(5) by auto
    have "\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j"
      using Scan.hyps by simp
    also have "... = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_app_bins order_trans by blast
      hence "\<pi>_it' k cfg inp ?bs'' j = \<pi>_it' k cfg inp (app_bins ?bs'' (k+1) (Scan_it k inp a x)) (j+1)"
        using \<open>i = j\<close> kth_\<pi>_it'_bins nth_app_bin \<pi>_it'_simps(3) Scan.hyps
        by (smt (verit, ccfv_SIG) length_bins_\<pi>_it' less_or_eq_imp_le not_le_imp_less order_trans wf_bins_\<pi>_it')
      moreover have "app_bins ?bs'' (k+1) (Scan_it k inp a x) = ?bs''"
      proof -
        have "set (Scan_it k inp a x) = set (Scan_it k inp a x)"
          unfolding Scan_it_def by blast
        also have "... \<subseteq> set_bin (bins ?bs' ! (k+1))"
          using Scan.hyps(5) Scan.prems(4) app_bins_def set_bin_app_bin
          by (metis bins.sel Groups.ab_semigroup_add_class.add.commute Suc_less_eq Un_iff nth_list_update_eq plus_1_eq_Suc subsetI)
        also have "... \<subseteq> set_bin (bins ?bs'' ! (k+1))"
          using Scan.hyps(5) Scan.prems(3,4) nth_bin_sub_\<pi>_it' by (metis add.commute add_less_cancel_left length_bins_app_bins)
        ultimately have "set (Scan_it k inp a x) \<subseteq> set_bin (bins ?bs'' ! (k+1))"
          using \<open>set (Scan_it k inp a x) \<subseteq> set_bin (bins (app_bins bs (k + 1) (Scan_it k inp a x)) ! (k + 1))\<close> by blast
        thus ?thesis
          using app_bins_eq Scan.hyps(5) Scan.prems(3) length_bins_\<pi>_it' by simp
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k cfg inp ?bs' (i + 1)"
      using \<open>i = j\<close> Scan.IH Scan.prems(1,3,4,7) sound wf by (metis dual_order.refl length_bins_app_bins)
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
  let ?bs' = "app_bins bs k (Predict_it k cfg a)"
  have x: "x \<in> set_bin (bins bs ! k)"
    using Predict.hyps(1,2) by auto
  have len: "i < length (items (bins ?bs' ! k))"
    using length_nth_bin_app_bins Predict.hyps(1) Orderings.preorder_class.dual_order.strict_trans1 linorder_not_less by blast
  have wf: "wf_bins cfg inp ?bs'"
    using Predict.prems(1-4) wf_bins_Predict_it wf_bins_app_bins distinct_Predict_it wf_bins_kth_bin x by fastforce
  have sound: "sound_items cfg inp (set_bins ?bs')" 
    using sound_Predict_it[OF _ _ x] Predict.hyps(3) Predict.prems(2,3,6) sound_items_def
    apply (auto simp: set_bins_app_bins)
    by (meson UnE dual_order.refl sound_items_def)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using sound wf Predict by (metis length_bins_app_bins \<pi>_it'_simps(5))
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Predict.prems(5) by auto
    have "\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j"
      using Predict.hyps by simp
    also have "... = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (bins ?bs'' ! k)) \<ge> length (items (bins bs ! k))"
        using length_nth_bin_\<pi>_it' length_nth_bin_app_bins order_trans by blast
      hence "\<pi>_it' k cfg inp ?bs'' j = \<pi>_it' k cfg inp (app_bins ?bs'' k (Predict_it k cfg a)) (j+1)"
        using \<open>i = j\<close> kth_\<pi>_it'_bins nth_app_bin \<pi>_it'_simps(5) Predict.hyps Predict.prems(3) length_bins_\<pi>_it'
          wf_bins_\<pi>_it' by (smt (verit, best) Orderings.preorder_class.dual_order.trans leI wf_bins_kth_bin wf_item_def x)
      moreover have "app_bins ?bs'' k (Predict_it k cfg a) = ?bs''"
      proof -
        have "set (Predict_it k cfg a) = set (Predict_it k cfg a)"
          unfolding Predict_it_def by blast
        also have "... \<subseteq> set_bin (bins ?bs' ! k)"
          using Predict.prems(3) app_bins_def set_bin_app_bin by (metis bins.sel Un_upper2 nth_list_update_eq)
        also have "... \<subseteq> set_bin (bins ?bs'' ! k)"
          using Predict.prems(3) nth_bin_sub_\<pi>_it' by (metis length_bins_app_bins)
        ultimately have "set (Predict_it k cfg a) \<subseteq> set_bin (bins ?bs'' ! k)"
          using \<open>set (Predict_it k cfg a) \<subseteq> set_bin (bins (app_bins bs k (Predict_it k cfg a)) ! k)\<close> by blast
        thus ?thesis
          using app_bins_eq Predict.prems(2) length_bins_\<pi>_it' by simp
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k cfg inp ?bs' (i + 1)"
      using \<open>i = j\<close> Predict.IH Predict.prems(1,3,4,7) sound wf by (metis length_bins_app_bins order_refl)
    finally show ?thesis
      using Predict.hyps by simp
  qed
qed simp

lemma \<pi>_it_idem:
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "sound_items cfg inp (set_bins bs)" "nonempty_derives cfg"
  shows "\<pi>_it k cfg inp (\<pi>_it k cfg inp bs) = \<pi>_it k cfg inp bs"
  using assms \<pi>_it'_idem \<pi>_it_def le0 by metis

lemma funpower_\<pi>_step_sub_\<pi>_it:
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k cfg inp (set_bins_upto bs k 0) \<subseteq> set_bins bs" "sound_items cfg inp (set_bins bs)"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "funpower (\<pi>_step k cfg inp) n (set_bins bs) \<subseteq> set_bins (\<pi>_it k cfg inp bs)"
  using assms
proof (induction n)
  case 0
  thus ?case
    by (simp add: \<pi>_it'_mono \<pi>_it_def)
next
  case (Suc n)
  have 0: "\<pi>_step k cfg inp (set_bins_upto (\<pi>_it k cfg inp bs) k 0) \<subseteq> set_bins (\<pi>_it k cfg inp bs)"
    using \<pi>_it'_mono set_bins_upto_k0_\<pi>_it'_eq \<pi>_it_def Suc.prems(3-5) order_trans by (metis (no_types, lifting))
  have "funpower (\<pi>_step k cfg inp) (Suc n) (set_bins bs) \<subseteq> (\<pi>_step k cfg inp) (set_bins (\<pi>_it k cfg inp bs))"
    using \<pi>_step_sub_mono Suc by (metis funpower.simps(2))
  also have "... \<subseteq> set_bins (\<pi>_it k cfg inp (\<pi>_it k cfg inp bs))"
    using \<pi>_step_sub_\<pi>_it Suc.prems(1-4,6-8) wf_bins_\<pi>_it sound_\<pi>_it 0
    by (metis add.commute length_bins_\<pi>_it less_Suc_eq_le plus_1_eq_Suc)
  also have "... \<subseteq> set_bins (\<pi>_it k cfg inp bs)"
    using \<pi>_it_idem Suc.prems by fastforce
  finally show ?case .
qed

lemma \<pi>_sub_\<pi>_it:
  assumes "wf_cfg cfg" "wf_bins cfg inp bs" "k < length (bins bs)" "length (bins bs) = length inp + 1"
  assumes "\<pi>_step k cfg inp (set_bins_upto bs k 0) \<subseteq> set_bins bs" "sound_items cfg inp (set_bins bs)"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi> k cfg inp (set_bins bs) \<subseteq> set_bins (\<pi>_it k cfg inp bs)"
  using assms funpower_\<pi>_step_sub_\<pi>_it \<pi>_def elem_limit_simp by fastforce

lemma \<I>_sub_\<I>_it:
  assumes "wf_cfg cfg" "k < length (bins (Init_it cfg inp))"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "\<I> k cfg inp \<subseteq> set_bins (\<I>_it k cfg inp)"
  using assms
proof (induction k)
  case 0
  hence "\<pi> 0 cfg inp (Init cfg) \<subseteq> set_bins (\<pi>_it 0 cfg inp (Init_it cfg inp))"
    using wf_bins_Init_it \<pi>_sub_\<pi>_it Init_it_eq_Init length_bins_Init_it Init_it_eq_Init 
          sound_Init set_bins_upto_empty \<pi>_step_empty set_bins_upto_sub_set_bins by metis
  thus ?case
    by simp
next
  case (Suc k)
  have wf: "wf_bins cfg inp (\<I>_it k cfg inp)"
    using length_bins_Init_it Suc.prems wf_bins_\<I>_it by force
  have sub: "\<pi>_step (Suc k) cfg inp (set_bins_upto (\<I>_it k cfg inp) (Suc k) 0) \<subseteq> set_bins (\<I>_it k cfg inp)"
  proof -
    have "bin (set_bins_upto (\<I>_it k cfg inp) (Suc k) 0) (Suc k) = {}"
      using kth_bin_set_bins_upto_empty wf Suc.prems by fastforce
    hence "\<pi>_step (Suc k) cfg inp (set_bins_upto (\<I>_it k cfg inp) (Suc k) 0) = set_bins_upto (\<I>_it k cfg inp) (Suc k) 0"
      unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast
    also have "... \<subseteq> set_bins (\<I>_it k cfg inp)"
      using wf Suc.prems set_bins_upto_sub_set_bins by (metis length_bins_\<I>_it)
    finally show ?thesis .
  qed
  have sound: "sound_items cfg inp (set_bins (\<I>_it k cfg inp))"
    using Suc sound_\<I> \<I>_it_sub_\<I> by (metis Suc_lessD subset_antisym)
  have "\<I> (Suc k) cfg inp \<subseteq> \<pi> (Suc k) cfg inp (set_bins (\<I>_it k cfg inp))"
    using Suc \<pi>_sub_mono by simp
  also have "... \<subseteq> set_bins (\<pi>_it (Suc k) cfg inp (\<I>_it k cfg inp))"
    using \<pi>_sub_\<pi>_it wf sub sound Suc.prems by fastforce
  finally show ?case
    by simp
qed

lemma \<II>_sub_\<II>_it:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<II> cfg inp \<subseteq> set_bins (\<II>_it cfg inp)"
  using assms \<I>_sub_\<I>_it \<II>_def \<II>_it_def by (metis length_bins_Init_it less_add_one)

subsection \<open>Correctness\<close>

definition earley_recognized_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "earley_recognized_it cfg inp = (\<exists>x \<in> set (items (bins (\<II>_it cfg inp) ! length inp)). is_finished cfg inp x)"

theorem earley_recognized_it_iff_earley_recognized:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "earley_recognized_it cfg inp \<longleftrightarrow> earley_recognized cfg inp"
proof -
  have "earley_recognized_it cfg inp = (\<exists>x \<in> set (items (bins (\<II>_it cfg inp) ! length inp)). is_finished cfg inp x)"
    unfolding earley_recognized_it_def by blast
  also have "... = (\<exists>x \<in> set_bins (\<II>_it cfg inp). is_finished cfg inp x)"
    using is_finished_def kth_bin_in_bins \<II>_it_def length_bins_Init_it length_bins_\<I>_it wf_bins_\<II>_it
      wf_item_in_kth_bin set_bin_def by (metis (mono_tags, lifting) assms(1) less_add_one subsetD)
  also have "... = (\<exists>x \<in> \<II> cfg inp. is_finished cfg inp x)"
    using assms \<II>_it_sub_\<II> \<II>_sub_\<II>_it by blast
  also have "... = earley_recognized cfg inp"
    unfolding earley_recognized_def by blast
  finally show ?thesis .
qed

corollary correctness_list:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "earley_recognized_it cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
  using assms correctness_set earley_recognized_it_iff_earley_recognized by blast

end

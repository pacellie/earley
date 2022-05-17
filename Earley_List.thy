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

definition Scan_it :: "nat \<Rightarrow> symbol \<Rightarrow> item \<Rightarrow> bins \<Rightarrow> bins" where
  "Scan_it k a x bs = (
    if k < length inp \<and> inp!k = a then
      let x' = inc_item x (k+1) in
      app_bins bs (k+1) [x']
    else bs)"

definition Predict_it :: "nat \<Rightarrow> symbol \<Rightarrow> bins \<Rightarrow> bins" where
  "Predict_it k X bs = (
    let rs = filter (\<lambda>r. rule_head r = X) rules in
    let is = map (\<lambda>r. init_item r k) rs in
    app_bins bs k is)"

definition Complete_it :: "nat \<Rightarrow> item \<Rightarrow> bins \<Rightarrow> bins" where
  "Complete_it k y bs = (
    let orig = (bins bs)!(item_origin y) in
    let is = filter (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items orig) in
    app_bins bs k (map (\<lambda>x. inc_item x k) is))"

function \<pi>_it' :: "nat \<Rightarrow> bins \<Rightarrow> nat \<Rightarrow> bins" where
  "\<pi>_it' k bs i = (
    if i \<ge> length (bins bs) then bs
    else
      let x = items (bins bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow>
            if is_terminal a then Scan_it k a x bs
            else Predict_it k a bs
        | None \<Rightarrow> Complete_it k x bs
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

lemma \<pi>_it'_sub_\<pi>:
  "set_bins bs \<subseteq> I \<Longrightarrow> set_bins (\<pi>_it' k bs i) \<subseteq> \<pi> k I"
proof standard
  fix x
  assume "set_bins bs \<subseteq> I" "x \<in> set_bins (\<pi>_it' k bs i)"
  thus "x \<in> \<pi> k I"
  proof (induction k bs i arbitrary: I rule: \<pi>_it'.induct)
    case (1 k bs i)

    thm "1.prems"
    thm "1.IH"

    show ?case
    proof (cases "i \<ge> length (bins bs)")
      case True
      then show ?thesis
        using "1.prems" \<pi>_mono by auto
    next
      case False
      let ?x = "items (bins bs ! k) ! i"
      show ?thesis
      proof cases
        assume "next_symbol x = None"
        show ?thesis
          sorry
      next
        assume "\<not> next_symbol x = None"
        show ?thesis
          sorry
      qed
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
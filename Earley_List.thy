theory Earley_List
  imports 
    Earley_Set
    "HOL-Library.While_Combinator" \<comment>\<open>TODO: Use?\<close>
begin

type_synonym bin = "item list"
type_synonym bins = "bin list"

definition set_bins :: "bins \<Rightarrow> items" where
  "set_bins bs = \<Union> { set b | b. b \<in> set bs }"

locale Earley_List = Earley_Set +
  fixes rules :: "rule list"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
  assumes nonempty_deriv: "N \<in> \<NN> \<Longrightarrow> \<not> derives [N] []"
begin

subsection \<open>Earley algorithm\<close>

definition Init_it :: "bins" where
  "Init_it = (
    let rs = filter (\<lambda>r. rule_head r = \<SS>) rules in
    let is = map (\<lambda>r. init_item r 0) rs in
    let bs = replicate (length inp + 1) [] in
    bs[0 := is])"

definition Scan_it :: "nat \<Rightarrow> nat \<Rightarrow> bins \<Rightarrow> bins" where
  "Scan_it k i bs = (
    let x = (bs!k)!i in
    case next_symbol x of
      Some a \<Rightarrow>
        if inp!k = a \<and> k < length inp then
          let x' = inc_item x (k+1) in
          bs[k+1 := bs!(k+1) @ [x']]
        else bs
      | None \<Rightarrow> bs)"

definition Predict_it :: "nat \<Rightarrow> nat \<Rightarrow> bins \<Rightarrow> bins" where
  "Predict_it k i bs = (
    case next_symbol ((bs!k)!i) of
      Some X \<Rightarrow>
        if is_nonterminal X then
          let rs = filter (\<lambda>r. rule_head r = X) rules in
          let is = map (\<lambda>r. init_item r k) rs in
          bs[k := bs!k @ is]
        else
          bs
      | None \<Rightarrow> bs)"

definition Complete_it :: "nat \<Rightarrow> nat \<Rightarrow> bins \<Rightarrow> bins" where
  "Complete_it k i bs = (
    let x = (bs!k)!i in
    if next_symbol x = None then
      let f = \<lambda>y. next_symbol y = Some (item_rule_head x) in
      let is = filter f (bs!(item_origin x)) in
      bs[k := bs!k @ map (\<lambda>y. inc_item y k) is]
    else
      bs)"

function \<pi>_it' :: "nat \<Rightarrow> bins \<Rightarrow> nat \<Rightarrow> bins" where
  "\<pi>_it' k bs i = (
    if i \<ge> length (bs!k) then bs
    else
      let f = Scan_it k i \<circ> Complete_it k i \<circ> Predict_it k i in
      \<pi>_it' k (f bs) (i+1)
  )"
  by pat_completeness simp
termination
  sorry \<comment>\<open>TODO\<close>
(* while_option :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option"
   while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" *)

definition \<pi>_it :: "nat \<Rightarrow> bins \<Rightarrow> bins" where
  "\<pi>_it k bs = \<pi>_it' k bs 0"

fun \<I>_it :: "nat \<Rightarrow> bins" where
  "\<I>_it 0 = \<pi>_it 0 Init_it"
| "\<I>_it (Suc n) = \<pi>_it (Suc n) (\<I>_it n)"

definition \<II>_it :: "bins" where
  "\<II>_it = \<I>_it (length inp)"

subsection \<open>Equality of set and list implementations\<close>
\<comment>\<open>TODO: distinctness for termination proof\<close>

lemma Init_eq_Init_it:
  "set_bins Init_it = Init"
  unfolding Init_it_def Init_def set_bins_def by (auto simp: rule_head_def valid_rules; blast)

lemma Scan_sup_Scan_it:
  "set_bins bs \<subseteq> I \<Longrightarrow> k < length bs \<Longrightarrow> i < length (bs!k) \<Longrightarrow>  set_bins (Scan_it k i bs) \<subseteq> Scan k I"
proof standard
  fix y
  assume *: "set_bins bs \<subseteq> I" "k < length bs" "i < length (bs!k)" "y \<in> set_bins (Scan_it k i bs)"
  let ?x = "(bs!k)!i"
  have #: "?x \<in> bin I k"
    sorry
  show "y \<in> Scan k I"
  proof (cases "set_bins (Scan_it k i bs) = set_bins bs")
    case True
    then show ?thesis 
      using "*"(1) "*"(4) Scan_mono by blast
  next
    case False
    then show ?thesis
      sledgehammer
  qed
qed


end

end
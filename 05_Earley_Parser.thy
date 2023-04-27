(*<*)
theory "05_Earley_Parser"
  imports
    "04_Earley_Recognizer"
    "HOL-Library.Monad_Syntax"
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter\<open>Earley Parser Implementation\<close>

section \<open>Pointer lemmas\<close>

definition predicts :: "'a item \<Rightarrow> bool" where
  "predicts x \<longleftrightarrow> item_origin x = item_end x \<and> item_dot x = 0"

definition scans :: "'a sentence \<Rightarrow> nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "scans inp k x y \<longleftrightarrow> y = inc_item x k \<and> (\<exists>a. next_symbol x = Some a \<and> inp!(k-1) = a)"

definition completes :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "completes k x y z \<longleftrightarrow> y = inc_item x k \<and> is_complete z \<and> item_origin z = item_end x \<and>
    (\<exists>N. next_symbol x = Some N \<and> N = item_rule_head z)"

definition sound_null_ptr :: "'a entry \<Rightarrow> bool" where
  "sound_null_ptr e = (pointer e = Null \<longrightarrow> predicts (item e))"

definition sound_pre_ptr :: "'a sentence \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a entry \<Rightarrow> bool" where
  "sound_pre_ptr inp bs k e = (\<forall>pre. pointer e = Pre pre \<longrightarrow>
    k > 0 \<and> pre < length (bs!(k-1)) \<and> scans inp k (item (bs!(k-1)!pre)) (item e))"

definition sound_prered_ptr :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a entry \<Rightarrow> bool" where
  "sound_prered_ptr bs k e = (\<forall>p ps k' pre red. pointer e = PreRed p ps \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow>
    k' < k \<and> pre < length (bs!k') \<and> red < length (bs!k) \<and> completes k (item (bs!k'!pre)) (item e) (item (bs!k!red)))"

definition sound_ptrs :: "'a sentence \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "sound_ptrs inp bs = (\<forall>k < length bs. \<forall>e \<in> set (bs!k).
    sound_null_ptr e \<and>
    sound_pre_ptr inp bs k e \<and>
    sound_prered_ptr bs k e)"

definition mono_red_ptr :: "'a bins \<Rightarrow> bool" where
  "mono_red_ptr bs = (\<forall>k < length bs. \<forall>i < length (bs!k).
    \<forall>k' pre red ps. pointer (bs!k!i) = PreRed (k', pre, red) ps \<longrightarrow> red < i)"

lemma sound_ptrs_bin_upd:
  assumes "sound_ptrs inp bs" "k < length bs" "es = bs!k" "distinct (items es)"
  assumes "sound_null_ptr e" "sound_pre_ptr inp bs k e" "sound_prered_ptr bs k e"
  shows "sound_ptrs inp (bs[k := bin_upd e es])"
(*<*)
  sorry
(*>*)

lemma mono_red_ptr_bin_upd:
  assumes "mono_red_ptr bs" "k < length bs" "es = bs!k" "distinct (items es)"
  assumes "\<forall>k' pre red ps. pointer e = PreRed (k', pre, red) ps \<longrightarrow> red < length es"
  shows "mono_red_ptr (bs[k := bin_upd e es])"
(*<*)
  sorry
(*>*)

lemma sound_mono_ptrs_bin_upds:
  assumes "sound_ptrs inp bs" "mono_red_ptr bs" "k < length bs" "b = bs!k" "distinct (items b)" "distinct (items es)"
  assumes "\<forall>e \<in> set es. sound_null_ptr e \<and> sound_pre_ptr inp bs k e \<and> sound_prered_ptr bs k e"
  assumes "\<forall>e \<in> set es. \<forall>k' pre red ps. pointer e = PreRed (k', pre, red) ps \<longrightarrow> red < length b"
  shows "sound_ptrs inp (bs[k := bin_upds es b]) \<and> mono_red_ptr (bs[k := bin_upds es b])"
(*<*)
  sorry
(*>*)

lemma sound_mono_ptrs_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_ptrs inp bs" "sound_items cfg inp (bins_items bs)"
  assumes "mono_red_ptr bs"
  assumes "nonempty_derives cfg" "wf_cfg cfg"
  shows "sound_ptrs inp (\<pi>_it' k cfg inp bs i) \<and> mono_red_ptr (\<pi>_it' k cfg inp bs i)"
(*<*)
  sorry
(*>*)

lemma sound_mono_ptrs_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_ptrs inp bs" "sound_items cfg inp (bins_items bs)"
  assumes "mono_red_ptr bs"
  assumes "nonempty_derives cfg" "wf_cfg cfg"
  shows "sound_ptrs inp (\<pi>_it k cfg inp bs) \<and> mono_red_ptr (\<pi>_it k cfg inp bs)"
(*<*)
  sorry
(*>*)

lemma sound_ptrs_Init_it:
  "sound_ptrs inp (Init_it cfg inp)"
(*<*)
  sorry
(*>*)

lemma mono_red_ptr_Init_it:
  "mono_red_ptr (Init_it cfg inp)"
(*<*)
  sorry
(*>*)

lemma sound_mono_ptrs_\<I>_it:
  assumes "k \<le> length inp" "wf_cfg cfg" "nonempty_derives cfg" "wf_cfg cfg"
  shows "sound_ptrs inp (\<I>_it k cfg inp) \<and> mono_red_ptr (\<I>_it k cfg inp)"
(*<*)
  sorry
(*>*)

lemma sound_mono_ptrs_\<II>_it:
  assumes "wf_cfg cfg" "nonempty_derives cfg"
  shows "sound_ptrs inp (\<II>_it cfg inp) \<and> mono_red_ptr (\<II>_it cfg inp)"
(*<*)
  sorry
(*>*)

section \<open>Trees and Forests\<close>

datatype 'a tree =
  Leaf 'a
  | Branch 'a "'a tree list"

fun yield_tree :: "'a tree \<Rightarrow> 'a sentence" where
  "yield_tree (Leaf a) = [a]"
| "yield_tree (Branch _ ts) = concat (map yield_tree ts)"

fun root_tree :: "'a tree \<Rightarrow> 'a" where
  "root_tree (Leaf a) = a"
| "root_tree (Branch N _) = N"

fun wf_rule_tree :: "'a cfg \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_rule_tree _ (Leaf a) \<longleftrightarrow> True"
| "wf_rule_tree cfg (Branch N ts) \<longleftrightarrow> (
    (\<exists>r \<in> set (\<RR> cfg). N = rule_head r \<and> map root_tree ts = rule_body r) \<and>
    (\<forall>t \<in> set ts. wf_rule_tree cfg t))"

fun wf_item_tree :: "'a cfg \<Rightarrow> 'a item \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_item_tree cfg _ (Leaf a) \<longleftrightarrow> True"
| "wf_item_tree cfg x (Branch N ts) \<longleftrightarrow> (
    N = item_rule_head x \<and> map root_tree ts = take (item_dot x) (item_rule_body x) \<and>
    (\<forall>t \<in> set ts. wf_rule_tree cfg t))"

definition wf_yield_tree :: "'a sentence \<Rightarrow> 'a item \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_yield_tree inp x t \<longleftrightarrow> yield_tree t = slice (item_origin x) (item_end x) inp"

datatype 'a forest =
  FLeaf 'a
  | FBranch 'a "'a forest list list"

fun combinations :: "'a list list \<Rightarrow> 'a list list" where
  "combinations [] = [[]]"
| "combinations (xs#xss) = [ x#cs . x <- xs, cs <- combinations xss ]"

fun trees :: "'a forest \<Rightarrow> 'a tree list" where
  "trees (FLeaf a) = [Leaf a]"
| "trees (FBranch N fss) = (
    let tss = (map (\<lambda>fs. concat (map (\<lambda>f. trees f) fs)) fss) in
    map (\<lambda>ts. Branch N ts) (combinations tss)
  )"

section \<open>A single parse tree\<close>

partial_function (option) build_tree' :: "'a bins \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tree option" where
  "build_tree' bs inp k i = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some (Branch (item_rule_head (item e)) [])
    | Pre pre \<Rightarrow> (
        do {
          t \<leftarrow> build_tree' bs inp (k-1) pre;
          case t of
            Branch N ts \<Rightarrow> Some (Branch N (ts @ [Leaf (inp!(k-1))]))
          | _ \<Rightarrow> None
        })
    | PreRed (k', pre, red) _ \<Rightarrow> (
        do {
          t \<leftarrow> build_tree' bs inp k' pre;
          case t of
            Branch N ts \<Rightarrow>
              do {
                t \<leftarrow> build_tree' bs inp k red;
                Some (Branch N (ts @ [t]))
              }
          | _ \<Rightarrow> None
        })
  ))"

definition build_tree :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a tree option" where
  "build_tree cfg inp bs = (
    let k = length bs - 1 in (
    case filter_with_index (\<lambda>x. is_finished cfg inp x) (items (bs!k)) of
      [] \<Rightarrow> None
    | (_, i)#_ \<Rightarrow> build_tree' bs inp k i
  ))"


definition wellformed_tree_ptrs :: "('a bins \<times> 'a sentence \<times> nat \<times> nat) set" where
  "wellformed_tree_ptrs = {
    (bs, inp, k, i) | bs inp k i.
      sound_ptrs inp bs \<and>
      mono_red_ptr bs \<and>
      k < length bs \<and>
      i < length (bs!k)
  }"

fun build_tree'_measure :: "('a bins \<times> 'a sentence \<times> nat \<times> nat) \<Rightarrow> nat" where
  "build_tree'_measure (bs, inp, k, i) = foldl (+) 0 (map length (take k bs)) + i"

lemma wellformed_tree_ptrs_pre:
  assumes "(bs, inp, k, i) \<in> wellformed_tree_ptrs"
  assumes "e = bs!k!i" "pointer e = Pre pre"
  shows "(bs, inp, (k-1), pre) \<in> wellformed_tree_ptrs"
(*<*)
  sorry
(*>*)

lemma wellformed_tree_ptrs_prered_pre:
  assumes "(bs, inp, k, i) \<in> wellformed_tree_ptrs"
  assumes "e = bs!k!i" "pointer e = PreRed (k', pre, red) ps"
  shows "(bs, inp, k', pre) \<in> wellformed_tree_ptrs"
(*<*)
  sorry
(*>*)

lemma wellformed_tree_ptrs_prered_red:
  assumes "(bs, inp, k, i) \<in> wellformed_tree_ptrs"
  assumes "e = bs!k!i" "pointer e = PreRed (k', pre, red) ps"
  shows "(bs, inp, k, red) \<in> wellformed_tree_ptrs"
(*<*)
  sorry
(*>*)

lemma build_tree'_induct:
  assumes "(bs, inp, k, i) \<in> wellformed_tree_ptrs"
  assumes "\<And>bs inp k i.
    (\<And>e pre. e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> P bs inp (k-1) pre) \<Longrightarrow>
    (\<And>e k' pre red ps. e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) ps \<Longrightarrow> P bs inp k' pre) \<Longrightarrow>
    (\<And>e k' pre red ps. e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) ps \<Longrightarrow> P bs inp k red) \<Longrightarrow>
    P bs inp k i" 
  shows "P bs inp k i"
(*<*)
  sorry
(*>*)

lemma build_tree'_termination:
  assumes "(bs, inp, k, i) \<in> wellformed_tree_ptrs"
  shows "\<exists>N ts. build_tree' bs inp k i = Some (Branch N ts)"
(*<*)
  sorry
(*>*)

lemma wf_item_tree_build_tree':
  assumes "(bs, inp, k, i) \<in> wellformed_tree_ptrs"
  assumes "wf_bins cfg inp bs"
  assumes "k < length bs" "i < length (bs!k)"
  assumes "build_tree' bs inp k i = Some t"
  shows "wf_item_tree cfg (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

lemma wf_yield_tree_build_tree':
  assumes "(bs, inp, k, i) \<in> wellformed_tree_ptrs"
  assumes "wf_bins cfg inp bs"
  assumes "k < length bs" "i < length (bs!k)" "k \<le> length inp"
  assumes "build_tree' bs inp k i = Some t"
  shows "wf_yield_tree inp (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

theorem wf_rule_root_yield_tree_build_tree:
  assumes "wf_bins cfg inp bs" "sound_ptrs inp bs" "mono_red_ptr bs" "length bs = length inp + 1"
  assumes "build_tree cfg inp bs = Some t"
  shows "wf_rule_tree cfg t \<and> root_tree t = \<SS> cfg \<and> yield_tree t = inp"
(*<*)
  sorry
(*>*)

corollary wf_rule_root_yield_tree_build_tree_\<II>_it:
  assumes "wf_cfg cfg" "nonempty_derives cfg"
  assumes "build_tree cfg inp (\<II>_it cfg inp) = Some t"
  shows "wf_rule_tree cfg t \<and> root_tree t = \<SS> cfg \<and> yield_tree t = inp"
(*<*)
  sorry
(*>*)

theorem correctness_build_tree_\<II>_it:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "(\<exists>t. build_tree cfg inp (\<II>_it cfg inp) = Some t) \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
(*<*)
  sorry
(*>*)

section \<open>Parse trees\<close>

fun insert_group :: "('a \<Rightarrow> 'k) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a \<Rightarrow> ('k \<times> 'v list) list \<Rightarrow> ('k \<times> 'v list) list" where
  "insert_group K V a [] = [(K a, [V a])]"
| "insert_group K V a ((k, vs)#xs) = (
    if K a = k then (k, V a # vs) # xs
    else (k, vs) # insert_group K V a xs  
  )"

fun group_by :: "('a \<Rightarrow> 'k) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a list \<Rightarrow> ('k \<times> 'v list) list" where
  "group_by K V [] = []"
| "group_by K V (x#xs) = insert_group K V x (group_by K V xs)"

(*<*)
lemma [partial_function_mono]:
  "monotone option.le_fun option_ord
    (\<lambda>f. map_option concat (those (map (\<lambda>((k', pre), reds).
      f ((((r, s), k'), pre), {pre}) \<bind>
        (\<lambda>pres. those (map (\<lambda>red. f ((((r, s), t), red), b \<union> {red})) reds) \<bind>
          (\<lambda>rss. those (map (\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss])) | _ \<Rightarrow> None) pres))))
    xs)))"
  sorry
(*>*)

partial_function (option) build_trees' :: "'a bins \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> 'a forest list option" where
  "build_trees' bs inp k i I = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some ([FBranch (item_rule_head (item e)) []])
    | Pre pre \<Rightarrow> (
        do {
          pres \<leftarrow> build_trees' bs inp (k-1) pre {pre};
          those (map (\<lambda>f.
            case f of
              FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (inp!(k-1))]]))
            | _ \<Rightarrow> None
          ) pres)
        })
    | PreRed p ps \<Rightarrow> (
        let ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps) in
        let gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps' in
        map_option concat (those (map (\<lambda>((k', pre), reds).
          do {
            pres \<leftarrow> build_trees' bs inp k' pre {pre};
            rss \<leftarrow> those (map (\<lambda>red. build_trees' bs inp k red (I \<union> {red})) reds);
            those (map (\<lambda>f.
              case f of
                FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss]))
              | _ \<Rightarrow> None
            ) pres)
          }
        ) gs))
      )
  ))"

definition build_trees :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a forest list option" where
  "build_trees cfg inp bs = (
    let k = length bs - 1 in
    let finished = filter_with_index (\<lambda>x. is_finished cfg inp x) (items (bs!k)) in
    map_option concat (those (map (\<lambda>(_, i). build_trees' bs inp k i {i}) finished))
  )"

definition wellformed_forest_ptrs :: "('a bins \<times> 'a sentence \<times> nat \<times> nat \<times> nat set) set" where
  "wellformed_forest_ptrs = {
    (bs, inp, k, i, I) | bs inp k i I.
      sound_ptrs inp bs \<and>
      k < length bs \<and>
      i < length (bs!k) \<and>
      I \<subseteq> {0..<length (bs!k)} \<and>
      i \<in> I
  }"

fun build_forest'_measure :: "('a bins \<times> 'a sentence \<times> nat \<times> nat \<times> nat set) \<Rightarrow> nat" where
  "build_forest'_measure (bs, inp, k, i, I) = foldl (+) 0 (map length (take (k+1) bs)) - card I"

lemma wellformed_forest_ptrs_pre:
  assumes "(bs, inp, k, i, I) \<in> wellformed_forest_ptrs"
  assumes "e = bs!k!i" "pointer e = Pre pre"
  shows "(bs, inp, (k-1), pre, {pre}) \<in> wellformed_forest_ptrs"
(*<*)
  sorry
(*>*)

lemma wellformed_forest_ptrs_prered_pre:
  assumes "(bs, inp, k, i, I) \<in> wellformed_forest_ptrs"
  assumes "e = bs!k!i" "pointer e = PreRed p ps"
  assumes "ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps)"
  assumes "gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps'"
  assumes "((k', pre), reds) \<in> set gs"
  shows "(bs, inp, k', pre, {pre}) \<in> wellformed_forest_ptrs"
(*<*)
  sorry
(*>*)

lemma wellformed_forest_ptrs_prered_red:
  assumes "(bs, inp, k, i, I) \<in> wellformed_forest_ptrs"
  assumes "e = bs!k!i" "pointer e = PreRed p ps"
  assumes "ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps)"
  assumes "gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps'"
  assumes "((k', pre), reds) \<in> set gs" "red \<in> set reds"
  shows "(bs, inp, k, red, I \<union> {red}) \<in> wellformed_forest_ptrs"
(*<*)
  sorry
(*>*)

lemma build_trees'_induct:
  assumes "(bs, inp, k, i, I) \<in> wellformed_forest_ptrs"
  assumes "\<And>bs inp k i I.
    (\<And>e pre. e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> P bs inp (k-1) pre {pre}) \<Longrightarrow>
    (\<And>e p ps ps' gs k' pre reds. e = bs!k!i \<Longrightarrow> pointer e = PreRed p ps \<Longrightarrow>
      ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps) \<Longrightarrow>
      gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps' \<Longrightarrow>
      ((k', pre), reds) \<in> set gs \<Longrightarrow> P bs inp k' pre {pre}) \<Longrightarrow>
    (\<And>e p ps ps' gs k' pre red reds reds'. e = bs!k!i \<Longrightarrow> pointer e = PreRed p ps \<Longrightarrow>
      ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps) \<Longrightarrow>
      gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps' \<Longrightarrow>
      ((k', pre), reds) \<in> set gs \<Longrightarrow> red \<in> set reds \<Longrightarrow> P bs inp k red (I \<union> {red})) \<Longrightarrow>
    P bs inp k i I" 
  shows "P bs inp k i I"
(*<*)
  sorry
(*>*)

lemma build_trees'_termination:
  assumes "(bs, inp, k, i, I) \<in> wellformed_forest_ptrs"
  shows "\<exists>fs. build_trees' bs inp k i I = Some fs \<and> (\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss)"
(*<*)
  sorry
(*>*)

lemma wf_item_tree_build_trees':
  assumes "(bs, inp, k, i, I) \<in> wellformed_forest_ptrs"
  assumes "wf_bins cfg inp bs"
  assumes "k < length bs" "i < length (bs!k)"
  assumes "build_trees' bs inp k i I = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_item_tree cfg (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

lemma wf_yield_tree_build_trees':
  assumes "(bs, inp, k, i, I) \<in> wellformed_forest_ptrs"
  assumes "wf_bins cfg inp bs"
  assumes "k < length bs" "i < length (bs!k)" "k \<le> length inp"
  assumes "build_trees' bs inp k i I = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_yield_tree inp (item (bs!k!i)) t"
(*<*)
  sorry
(*>*)

theorem wf_rule_root_yield_tree_build_trees:
  assumes "wf_bins cfg inp bs" "sound_ptrs inp bs" "length bs = length inp + 1"
  assumes "build_trees cfg inp bs = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree cfg t \<and> root_tree t = \<SS> cfg \<and> yield_tree t = inp"
(*<*)
  sorry
(*>*)

corollary wf_rule_root_yield_tree_build_trees_\<II>_it:
  assumes "wf_cfg cfg" "nonempty_derives cfg"
  assumes "build_trees cfg inp (\<II>_it cfg inp) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree cfg t \<and> root_tree t = \<SS> cfg \<and> yield_tree t = inp"
(*<*)
  sorry
(*>*)

theorem soundness_build_trees_\<II>_it:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  assumes "build_trees cfg inp (\<II>_it cfg inp) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "derives cfg [\<SS> cfg] inp"
(*<*)
  sorry
(*>*)

theorem termination_build_tree_\<II>_it:
  assumes "wf_cfg cfg" "nonempty_derives cfg" "derives cfg [\<SS> cfg] inp"
  shows "\<exists>fs. build_trees cfg inp (\<II>_it cfg inp) = Some fs"
(*<*)
  sorry
(*>*)

section \<open>A word on completeness\<close>

(*<*)
end
(*>*)
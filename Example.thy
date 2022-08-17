theory Example
  imports Main
begin

section\<open>Minimal set of necessary definitions\<close>

subsection\<open>CFG\<close>

type_synonym 'a rule = "'a \<times> 'a list"

type_synonym 'a rules = "'a rule list"

type_synonym 'a sentence = "'a list"

datatype 'a cfg = 
  CFG 
    (\<NN> : "'a list") 
    (\<TT> : "'a list") 
    (\<RR> : "'a rules")
    (\<SS> : "'a")

definition is_terminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_terminal cfg s = (s \<in> set (\<TT> cfg))"

subsection \<open>Items\<close>

definition rule_head :: "'a rule \<Rightarrow> 'a" where
  "rule_head = fst"

definition rule_body :: "'a rule \<Rightarrow> 'a list" where
  "rule_body = snd"

datatype 'a item = 
  Item 
    (item_rule: "'a rule") 
    (item_dot : nat) 
    (item_origin : nat)
    (item_end : nat)

definition item_rule_head :: "'a item \<Rightarrow> 'a" where
  "item_rule_head x = rule_head (item_rule x)"

definition item_rule_body :: "'a item \<Rightarrow> 'a sentence" where
  "item_rule_body x = rule_body (item_rule x)"

definition init_item :: "'a rule \<Rightarrow> nat \<Rightarrow> 'a item" where
  "init_item r k = Item r 0 k k"

definition is_complete :: "'a item \<Rightarrow> bool" where
  "is_complete x = (item_dot x \<ge> length (item_rule_body x))"

definition next_symbol :: "'a item \<Rightarrow> 'a option" where
  "next_symbol x = (if is_complete x then None else Some ((item_rule_body x) ! (item_dot x)))"

definition inc_item :: "'a item \<Rightarrow> nat \<Rightarrow> 'a item" where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

subsection \<open>Bins\<close>

datatype 'a bin = Bin (items: "'a item list")

datatype 'a bins = Bins (bins: "'a bin list")

definition app_bin :: "'a bin \<Rightarrow> 'a item list \<Rightarrow> 'a bin" where
  "app_bin b is = Bin (items b @ (filter (\<lambda>i. i \<notin> set (items b)) is))"

definition app_bins :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a item list \<Rightarrow> 'a bins" where
  "app_bins bs k is = Bins ((bins bs)[k := app_bin ((bins bs)!k) is])"

subsection \<open>Algorithm\<close>

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

section \<open>Actual question\<close>

subsection\<open>Old Version\<close>

function \<pi>_it'_old :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a bins" where
  "\<pi>_it'_old k cfg inp bs i = (
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
      in \<pi>_it'_old k cfg inp bs' (i+1))"
  by pat_completeness auto
termination
  sorry

lemma \<pi>_it'_old_simps[simp]:
  "i \<ge> length (items (bins bs ! k)) \<Longrightarrow> \<pi>_it'_old k cfg inp bs i = bs"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = None \<Longrightarrow>
    \<pi>_it'_old k cfg inp bs i = \<pi>_it'_old k cfg inp (app_bins bs k (Complete_it k x bs)) (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    is_terminal cfg a \<Longrightarrow> k < length inp \<Longrightarrow> \<pi>_it'_old k cfg inp bs i = \<pi>_it'_old k cfg inp (app_bins bs (k+1) (Scan_it k inp a x)) (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    is_terminal cfg a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> \<pi>_it'_old k cfg inp bs i = \<pi>_it'_old k cfg inp bs (i+1)"
  "\<not> i \<ge> length (items (bins bs ! k)) \<Longrightarrow> x = items (bins bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    \<not> is_terminal cfg a \<Longrightarrow> \<pi>_it'_old k cfg inp bs i = \<pi>_it'_old k cfg inp (app_bins bs k (Predict_it k cfg a)) (i+1)"
  by (subst \<pi>_it'_old.simps, simp del: \<pi>_it'_old.simps)+

text\<open>This is the induction rule I was using basically all the time to avoid manual case splitting.\<close>
lemma \<pi>_it'_old_induct[case_names Base Complete Scan Pass Predict]:
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
proof (induction k cfg inp bs i rule: \<pi>_it'_old.induct)
  case (1 k cfg inp bs i)
  show ?case
  proof cases
    assume "i \<ge> length (items (bins bs ! k))"
    thus ?thesis
      using base by blast
  next
    assume a1: "\<not> i \<ge> length (items (bins bs ! k))"
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
        assume a3: "is_terminal cfg a"
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
        assume a3: "\<not> is_terminal cfg a"
        show ?thesis
          using 1 a1 a3 a_def predict by simp
      qed
    qed
  qed
qed

subsection\<open>Current Version\<close>

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
  shows "P k cfg inp bs i" \<comment>\<open>How do I proof this? I don't have \<pi>_it'.induct anymore.\<close>
  oops

text\<open>Do I use \<pi>_it'.fixp_induct or \<pi>_it'.raw_induct but they just produce errors ...\<close>

end
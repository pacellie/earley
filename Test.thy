theory Test
  imports Main "HOL-Library.Monad_Syntax"
begin

section \<open>Small example\<close>

text \<open>
  Nonsense example:

  We start working at some index i and keep following the 'pointers' aka nats representing indices
  until we hit index 0.

  f) only one pointer
  g) multiple pointer
\<close>

partial_function (option) f :: "nat list \<Rightarrow> nat \<Rightarrow> nat option" where
  "f xs i = (
    if i = 0 then
      Some 0
    else
      f xs (xs!i)
  )"


thm monotone_def
thm flat_ord_def
thm flat_lub_def
thm fun_ord_def

term monotone

term option.le_fun
term option_ord
term flat_ord

term "(\<lambda>f. those (map (\<lambda>j. f j) a))"

lemma [partial_function_mono]: "monotone (fun_ord (flat_ord None)) (flat_ord None) (\<lambda>f. those (map (\<lambda>j. f (a, j)) (a ! b)))"
  apply (induction a arbitrary: b)
   apply (auto simp add: monotone_def flat_ord_def fun_ord_def option.leq_refl)
  oops

partial_function (option) g :: "nat list list \<Rightarrow> nat \<Rightarrow> nat option" where
  "g xs i = (
    if i = 0 then
      Some 0
    else
      do {
        ns \<leftarrow> those (map (\<lambda>j. g xs j) (xs!i)); \<comment>\<open>fails here\<close>
        Some (foldr (+) ns 0)
      }
  )"

section \<open>Original Problem\<close>

type_synonym 'a rule = "'a \<times> 'a list"
type_synonym 'a sentence = "'a list"

definition rule_head :: "'a rule \<Rightarrow> 'a" where
  "rule_head = fst"

datatype 'a item = 
  Item 
    (item_rule: "'a rule") 
    (item_dot : nat) 
    (item_origin : nat)
    (item_end : nat)

definition item_rule_head :: "'a item \<Rightarrow> 'a" where
  "item_rule_head x = rule_head (item_rule x)"

datatype pointer =
  Null
  | Pre nat
  | PreRed "nat \<times> nat \<times> nat" "nat list"

datatype 'a entry =
  Entry
    (item : "'a item")
    (pointer : pointer)

type_synonym 'a bin = "'a entry list"
type_synonym 'a bins = "'a bin list"

datatype 'a forest =
  FLeaf 'a
  | FBranch 'a "'a forest list list"

text\<open>This works fine with only one reduction pointer\<close>

partial_function (option) build_forest' :: "'a bins \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> 'a forest option" where
  "build_forest' bs inp k i I = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some (FBranch (item_rule_head (item e)) []) \<comment>\<open>start building sub-forest\<close>
    | Pre pre \<Rightarrow> ( \<comment>\<open>add sub-forest starting from terminal\<close>
        do {
          f \<leftarrow> build_forest' bs inp (k-1) pre {pre};
          case f of
            FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (inp!(k-1))]]))
          | _ \<Rightarrow> undefined \<comment>\<open>impossible case\<close>
        })
    | PreRed (k', pre, red) _ \<Rightarrow> ( \<comment>\<open>add sub-forest starting from non-terminal\<close>
        do {
          f \<leftarrow> build_forest' bs inp k' pre {pre};
          case f of
            FBranch N fss \<Rightarrow>
              do {
                f \<leftarrow> build_forest' bs inp k red (I \<union> {i}); \<comment>\<open>only one reduction pointer\<close>
                Some (FBranch N (fss @ [[f]]))
              }
          | _ \<Rightarrow> undefined \<comment>\<open>impossible case\<close>
        })
  ))"

text\<open>This breaks :(\<close>

lemma [partial_function_mono]: "monotone option.le_fun option_ord (\<lambda>f. those (map (\<lambda>r. f ((((ac, bc), bb), r), b \<union> {ba})) xb))"
  sorry

partial_function (option) build_forest'' :: "'a bins \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> 'a forest option" where
  "build_forest'' bs inp k i I = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some (FBranch (item_rule_head (item e)) []) \<comment>\<open>start building sub-forest\<close>
    | Pre pre \<Rightarrow> ( \<comment>\<open>add sub-forest starting from terminal\<close>
        do {
          f \<leftarrow> build_forest'' bs inp (k-1) pre {pre};
          case f of
            FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (inp!(k-1))]]))
          | _ \<Rightarrow> undefined \<comment>\<open>impossible case\<close>
        })
    | PreRed (k', pre, red) reds \<Rightarrow> ( \<comment>\<open>add sub-forest starting from non-terminal\<close>
        do {
          f \<leftarrow> build_forest'' bs inp k' pre {pre};
          case f of
            FBranch N fss \<Rightarrow>
              let reds' = filter (\<lambda>r. r \<notin> I) (red#reds) in
              do {
                fs \<leftarrow> those (map (\<lambda>r. build_forest'' bs inp k r (I \<union> {i})) reds'); \<comment>\<open>all reduction pointers\<close>
                Some (FBranch N (fss @ [fs]))
              }
          | _ \<Rightarrow> undefined \<comment>\<open>impossible case\<close>
        })
  ))"

end
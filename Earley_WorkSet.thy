theory Earley_WorkSet
  imports 
    Earley_Set
begin

locale Earley_WorkSet = Earley_Set +
  assumes nonempty_deriv: "N \<in> \<NN> \<Longrightarrow> \<not> derives [N] []"
begin

definition Complete_W :: "nat \<Rightarrow> items \<Rightarrow> items \<Rightarrow> items" where
  "Complete_W k W I =
    { inc_item x k | x y.
        x \<in> bin I (item_origin y) \<and>
        y \<in> bin W k \<and>
        is_complete y \<and>
        next_symbol x = Some (item_rule_head y) }"

function \<pi>_W :: "nat \<Rightarrow> items \<Rightarrow> items \<times> items \<Rightarrow> items \<times> items" where
  "\<pi>_W k W (I,J) = (
    if W = {} then (I,J)
    else
      let J' = J \<union> Scan k W in
      let T = Predict k W \<union> Complete_W k W I in
      let W' = T - I in
      let I' = I \<union> T in
      \<pi>_W k W' (I',J'))"
  by pat_completeness simp
termination sorry

fun \<I>_W' :: "nat \<Rightarrow> items \<times> items" where
  "\<I>_W' 0 = \<pi>_W 0 Init (Init,{})"
| "\<I>_W' (Suc k) = (
    let (I,J) = \<I>_W' k in
    \<pi>_W (Suc k) J (I \<union> J, {}))"

definition \<I>_W :: "nat \<Rightarrow> items" where
  "\<I>_W k = (let (I,J) = \<I>_W' k in I \<union> J)"

definition \<II>_W :: "items" where
  "\<II>_W = \<I>_W (length inp)"

end
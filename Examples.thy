theory Examples
  imports Earley_List
begin

subsection \<open>Problem 1\<close>

(* CFG.thy
typedecl symbol <-- HERE

type_synonym rule = "symbol \<times> symbol list"

type_synonym sentence = "symbol list"

locale CFG =
  fixes \<NN> :: "symbol set" <-- use "'a set" instead everywhere?
  fixes \<TT> :: "symbol set"
  fixes \<RR> :: "rule set"
  fixes \<SS> :: "symbol"
  assumes disjunct_symbols: "\<NN> \<inter> \<TT> = {}"
  assumes startsymbol_dom: "\<SS> \<in> \<NN>"
  assumes validRules: "\<forall> (N, \<alpha>) \<in> \<RR>. N \<in> \<NN> \<and> (\<forall> s \<in> set \<alpha>. s \<in> \<NN> \<union> \<TT>)"
*)
datatype t = a | plus
datatype n = S
datatype s = Terminal t | Nonterminal n

definition grammar :: "s rule set" where
  "grammar = {
    (Nonterminal S, [Terminal a]),
    (Nonterminal S, [Nonterminal S, Terminal plus, Nonterminal S])
  }"

text\<open>
  Solution: remove `symbol` instead use "'a" everywhere? But then we can't depend on Steven's
  AFP entry except for very few things and have to copy/rewrite CFG, ... files.
\<close>

text\<open>
  Follow up question: How do we want to specify a grammar? Like above if with typedecl, or ...?
\<close>


subsection \<open>Problem 2\<close>

(*
locale Earley_Set = CFG +
  fixes inp :: "symbol list" <-- HERE
  assumes valid_inp: "set inp \<subseteq> \<TT>"
  assumes finite: "finite \<RR>"
*)
locale Test =
  fixes global :: nat
begin

fun f :: "'a \<Rightarrow> nat" where
  "f _ = global"

end

global_interpretation test: Test "5::nat"
  defines f_impl = test.f .

term f_impl
value "f_impl (0::nat)"

text\<open>
  Solution: remove `inp` from locale and pass it everywhere as an additional argument?
\<close>


subsection \<open>'Problem'/TODO 3\<close>

(*
locale Earley_List = Earley_Set +
  fixes rules :: "rule list"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
  assumes nonempty_deriv: "N \<in> \<NN> \<Longrightarrow> \<not> derives [N] []" <-- HERE
*)

text\<open>
  Write a function (naive/more involved) that given a grammar and a nonterminal
  checks if this terminal has an empty derivation then prove by `eval`.
\<close>

end
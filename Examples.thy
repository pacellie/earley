theory Examples
  imports Earley_List
begin

(*
typedecl symbol

type_synonym rule = "symbol \<times> symbol list"

type_synonym sentence = "symbol list"

locale CFG =
  fixes \<NN> :: "symbol set"
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

definition grammar :: "rule set" where
  "grammar = {
    (Nonterminal S, [Terminal a]),
    (Nonterminal S, [Nonterminal S, Terminal plus, Nonterminal S])
  }"

(*
locale Earley_Set = CFG +
  fixes inp :: "symbol list"
  assumes valid_inp: "set inp \<subseteq> \<TT>"
  assumes finite: "finite \<RR>"
*)
locale Test =
  fixes global :: nat
begin

fun f :: "'a \<Rightarrow> nat" where
  "f _ = global"

end

global_interpretation test: Test "5" .

term test.f

(*
locale Earley_List = Earley_Set +
  fixes rules :: "rule list"
  assumes valid_rules: "set rules = \<RR> \<and> distinct rules"
  assumes nonempty_deriv: "N \<in> \<NN> \<Longrightarrow> \<not> derives [N] []"
*)

end
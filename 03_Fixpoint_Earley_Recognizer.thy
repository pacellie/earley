(*<*)
theory "03_Fixpoint_Earley_Recognizer"
  imports
    "02_Earleys_Algorithm"
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter \<open>Earley's Algorithm Formalization \label{chapter:3}\<close>

text\<open>
In this chapter we shortly introduce the interactive theorem prover Isabelle/HOL \cite{Nipkow:2002} used as
the tool for verification in this thesis and recap some of the formalism of context-free grammars and its representation
in Isabelle. Finally we formalize the simplified Earley recognizer algorithm presented in Chapter
\ref{chapter:2}; presenting the implementation and the proofs for termination, soundness and completeness.
Note that most of the definitions of Sections \ref{sec:cfg} and \ref{sec:earley} are not our own work
but only slightly adapted from \cite{Obua:2017} \cite{LocalLexing-AFP}. All of the proofs in this chapter are
our own work. 
\<close>

section\<open>Context-free grammars and Isabelle/HOL \label{sec:cfg}\<close>

text\<open>
Isabelle/HOL \cite{Nipkow:2002} is an interactive theorem prover based on a fragment of higher-order logic. It supports the core
concepts known from common functional programming languages. The notation $t :: \tau$ means that term $t$ has type
$\tau$. Basic types include \textit{bool}, \textit{nat}; the operator @{term "(\<times>)"} represents pairs at the type level. Type variables are written $'a$, $'b$, etc;
most type constructors are written postfix, e.g. $'a \, \textit{set}$ and $'a \, \textit{list}$; the function
space arrow is $\Rightarrow$; function \textit{set} converts a list into a set. Type synonyms are introduced via \textit{type\_synonym}. Algebraic data types are defined with the keyword \textit{datatype}.
Non-recursive definitions are introduced with the \textit{definition} keyword.

It is standard to define a language as a set of strings over a finite set of symbols. We deviate slightly by introducing a type variable $'a$
for the type of symbols. Thus a string corresponds to a list of symbols and a language is formalized as
a set of lists of symbols. We represent a context-free grammar as the datatype \textit{CFG}. An instance \textit{cfg} consists of (1) a list of
nonterminals @{term "\<NN> cfg"}, (2) a list of terminals @{term "\<TT> cfg"}, (3) a list of production rules
@{term "\<RR> cfg"}, and a start symbol @{term "\<SS> cfg"}. Each rule consists in turn of a left-hand side, a single symbol,
and a right-hand side, a list of symbols.
The productions with a particular nonterminal $N$ on their left-hand sides are called the alternatives of $N$.
We make the usual assumptions about the wellformedness of a context-free grammar. The intersection of set of terminals and
the set of nonterminals is empty; the start symbol @{term \<SS>} is a nonterminal; the left-hand side of a production
is a nonterminal and its right-hand side consists of only symbols. Additionally, since we are working with
a list of productions, we make the assumption that this list is distinct.
\<close>

type_synonym 'a rule = "'a \<times> 'a list"
type_synonym 'a rules = "'a rule list"

datatype 'a cfg = 
  CFG 
    (\<NN> : "'a list") 
    (\<TT> : "'a list") 
    (\<RR> : "'a rules")
    (\<SS> : "'a")

definition disjunct_symbols :: "'a cfg \<Rightarrow> bool" where
  "disjunct_symbols cfg \<equiv> set (\<NN> cfg) \<inter> set (\<TT> cfg) = {}"

definition wf_startsymbol :: "'a cfg \<Rightarrow> bool" where
  "wf_startsymbol cfg \<equiv> \<SS> cfg \<in> set (\<NN> cfg)"

definition wf_rules :: "'a cfg \<Rightarrow> bool" where
  "wf_rules cfg \<equiv> \<forall>(N, \<alpha>) \<in> set (\<RR> cfg). N \<in> set (\<NN> cfg) \<and> (\<forall>s \<in> set \<alpha>. s \<in> set (\<NN> cfg) \<union> set (\<TT> cfg))"

definition distinct_rules :: "'a cfg \<Rightarrow> bool" where
  "distinct_rules cfg \<equiv> distinct (\<RR> cfg)"

definition wf_cfg :: "'a cfg \<Rightarrow> bool" where
  "wf_cfg cfg \<equiv> disjunct_symbols cfg \<and> wf_startsymbol cfg \<and> wf_rules cfg \<and> distinct_rules cfg"

text\<open>
Furthermore, in Isabelle, lists are constructed from the empty list @{term "[]"} via the infix cons-operator @{term "(#)"}; the operator @{term "(@)"} appends two lists. Pairs are written
@{term "(a, b)"}; triples and so forth are written @{term "(a, b, c)"} but are internally represented as
nested pairs; the nesting is on the first component of a pair. Functions \textit{fst} and \textit{snd} return
the first and second component of a pair. Sets follow the standard mathematical notation including
the commonly found set builder notation or set comprehensions @{term "{ x | x. P x}"}, and can also be defined
inductively using the keyword \textit{inductive\_set}.

Next we formalize the concept of a derivation. We use lowercase letters $a$, $b$, $c$ indicating terminal symbols; capital letters
$A$, $B$, $C$ denote nonterminals; lists of symbols are represented by greek letters: \alpha, \beta, \gamma, occasionally also by lowercase letters $u$, $v$, $w$.
The empty list in the context of a language is \epsilon. A sentential is a list $\alpha$ consisting of only symbols. A sentence
is a sentential if it only contains terminal symbols. We first define a predicate \textit{derives1} which expresses that
we can derive $v$ from $u$ in a single step or @{term "derives1 cfg u v"} holds if there exist $\alpha$, $\beta$, $N$ and $\gamma$ such that @{term "u = \<alpha> @ [N] @ \<beta>"},
@{term "v = \<alpha> @ \<gamma> @ \<beta>"} and @{term "(N, \<gamma>)"} is a production rule. We then can define the set of single-step derivations utilizing @{term derives1},
and subsequently the set of all derivations given a particular grammar is the reflexive-transitive closure of the set of
single-step derivations. Finally, we say $v$ can be derived from $u$ given a grammar \textit{cfg}, or @{term "derives cfg u v"} if
@{term "(u, v) \<in> derivations cfg"}.
\<close>

type_synonym 'a sentential = "'a list"

definition is_terminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_terminal cfg s \<equiv> s \<in> set (\<TT> cfg)"

definition is_nonterminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_nonterminal cfg s \<equiv> s \<in> set (\<NN> cfg)"

definition is_symbol :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_symbol cfg s \<longleftrightarrow> is_terminal cfg s \<or> is_nonterminal cfg s"

definition wf_sentential :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "wf_sentential cfg s \<equiv> \<forall>x \<in> set s. is_symbol cfg x"

definition is_sentence :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "is_sentence cfg s \<equiv> \<forall>x \<in> set s. is_terminal cfg x"

definition derives1 :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "derives1 cfg u v \<equiv>
     \<exists> \<alpha> \<beta> N \<gamma>. 
         u = \<alpha> @ [N] @ \<beta>
       \<and> v = \<alpha> @ \<gamma> @ \<beta>
       \<and> (N, \<gamma>) \<in> set (\<RR> cfg)"  

definition derivations1 :: "'a cfg \<Rightarrow> ('a sentential \<times> 'a sentential) set" where
  "derivations1 cfg = { (u,v) | u v. derives1 cfg u v }"

definition derivations :: "'a cfg \<Rightarrow> ('a sentential \<times> 'a sentential) set" where 
  "derivations cfg = (derivations1 cfg)^*"

definition derives :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "derives cfg u v \<equiv> (u, v) \<in> derivations cfg"

text\<open>
It goes without saying that we can also define functions in Isabelle. Potentially recursive but provably total functions that may make use of pattern matching are defined with
the \textit{fun} and \textit{function} keywords; partial functions are defined via \textit{partial\_function}
Take for example the function @{term slice} defined below. Term @{term "slice i j xs"} computes the slice of a list @{term xs}
between indices $i$ (inclusive) and $j$ (exclusive), e.g. @{term "slice (2::nat) (4::nat) [a, b, c, d, e]"} evaluates to @{term "[c, d]"}.
\<close>

fun slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slice _ _ [] = []"
| "slice _ 0 (x#xs) = []"
| "slice 0 (Suc b) (x#xs) = x # slice 0 b xs"
| "slice (Suc a) (Suc b) (x#xs) = slice a b xs"

text\<open>
Lemmas, theorems and corollaries are presented using the keywords \textit{lemma}, \textit{theorem}, \textit{corollary} respectively, followed
by their names. They consist of zero or more assumptions marked by \textit{assumes} keywords and one conclusion
indicated by \textit{shows}. E.g. we can proof a simple lemma about the interaction between the @{term slice} function
and the append operator @{term "(@)"}, stating the conditions under which we can split one slice into two.
\<close>

lemma slice_append:
  assumes "i \<le> j" "j \<le> k"
  shows "slice i j xs @ slice j k xs = slice i k xs"
(*<*)
  sorry
(*>*)

section \<open>Earley's Algorithm \label{sec:earley}\<close>

text\<open>
Now we are ready to formalize the algorithm presented in Chapter \ref{chapter:2}.
\<close>

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

type_synonym 'a items = "'a item set"

definition item_rule_head :: "'a item \<Rightarrow> 'a" where
  "item_rule_head x = rule_head (item_rule x)"

definition item_rule_body :: "'a item \<Rightarrow> 'a sentential" where
  "item_rule_body x = rule_body (item_rule x)"

definition item_\<alpha> :: "'a item \<Rightarrow> 'a sentential" where
  "item_\<alpha> x = take (item_dot x) (item_rule_body x)"

definition item_\<beta> :: "'a item \<Rightarrow> 'a sentential" where 
  "item_\<beta> x = drop (item_dot x) (item_rule_body x)"

definition is_complete :: "'a item \<Rightarrow> bool" where
  "is_complete x \<equiv> item_dot x \<ge> length (item_rule_body x)"

definition next_symbol :: "'a item \<Rightarrow> 'a option" where
  "next_symbol x \<equiv> if is_complete x then None else Some ((item_rule_body x) ! (item_dot x))"

definition init_item :: "'a rule \<Rightarrow> nat \<Rightarrow> 'a item" where
  "init_item r k = Item r 0 k k"

definition inc_item :: "'a item \<Rightarrow> nat \<Rightarrow> 'a item" where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

definition bin :: "'a items \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"

definition wf_item :: "'a cfg \<Rightarrow> 'a sentential => 'a item \<Rightarrow> bool" where 
  "wf_item cfg inp x \<equiv> 
    item_rule x \<in> set (\<RR> cfg) \<and> 
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length inp"

definition wf_items :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> bool" where
  "wf_items cfg inp I \<equiv> \<forall>x \<in> I. wf_item cfg inp x"

definition is_finished :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a item \<Rightarrow> bool" where
  "is_finished cfg inp x \<equiv> 
    item_rule_head x = \<SS> cfg \<and>
    item_origin x = 0 \<and>
    item_end x = length inp \<and> 
    is_complete x"

definition earley_recognized :: "'a items \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "earley_recognized I cfg inp \<equiv> \<exists>x \<in> I. is_finished cfg inp x"

definition Init :: "'a cfg \<Rightarrow> 'a items" where
  "Init cfg = { init_item r 0 | r. r \<in> set (\<RR> cfg) \<and> fst r = (\<SS> cfg) }"

definition Scan :: "nat \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Scan k inp I = 
    { inc_item x (k+1) | x a.
        x \<in> bin I k \<and>
        inp!k = a \<and>
        k < length inp \<and>
        next_symbol x = Some a }"

definition Predict :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Predict k cfg I =
    { init_item r k | r x.
        r \<in> set (\<RR> cfg) \<and>
        x \<in> bin I k \<and>
        next_symbol x = Some (rule_head r) }"

definition Complete :: "nat \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Complete k I =
    { inc_item x k | x y.
        x \<in> bin I (item_origin y) \<and>
        y \<in> bin I k \<and>
        is_complete y \<and>
        next_symbol x = Some (item_rule_head y) }"

fun funpower :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "funpower f 0 x = x"
| "funpower f (Suc n) x = f (funpower f n x)"

definition natUnion :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "natUnion f = \<Union> { f n | n. True }"

definition limit  :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit f x = natUnion (\<lambda> n. funpower f n x)"

definition E_step :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "E_step k cfg inp I = I \<union> Scan k inp I \<union> Complete k I \<union> Predict k cfg I"

definition E :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "E k cfg inp I = limit (E_step k cfg inp) I"

fun \<E> :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items" where
  "\<E> 0 cfg inp = E 0 cfg inp (Init cfg)"
| "\<E> (Suc n) cfg inp = E (Suc n) cfg inp (\<E> n cfg inp)"

definition earley :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items" where
  "earley cfg inp = \<E> (length inp) cfg inp"

(*
inductive_set Earley :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items"
  for cfg :: "'a cfg" and inp :: "'a sentential"
  where
  init: "r \<in> set (\<RR> cfg) \<Longrightarrow> fst r = \<SS> cfg \<Longrightarrow> init_item r 0 \<in> Earley cfg inp"
| scan: "x \<in> bin (Earley cfg inp) k \<Longrightarrow> k < length inp \<Longrightarrow> inp!k = a \<Longrightarrow> next_symbol x = Some a
    \<Longrightarrow> inc_item x (k+1) \<in> Earley cfg inp"
*)

section \<open>Wellformedness\<close>

lemma wf_Init:
  assumes "x \<in> Init cfg"
  shows "wf_item cfg inp x"
(*<*)
  sorry
(*>*)
text\<open>by definition\<close>

lemma wf_Scan_Predict_Complete:
  assumes "wf_items cfg inp I" 
  shows "wf_items cfg inp (Scan k inp I \<union> Predict k cfg I \<union> Complete k I)"
(*<*)
  sorry
(*>*)
text\<open>by definition\<close>

lemma wf_E_step:
  assumes "wf_items cfg inp I"
  shows "wf_items cfg inp (E_step k cfg inp I)"
(*<*)
  sorry
(*>*)
text\<open>@{thm[source] wf_Scan_Predict_Complete} by definition\<close>

lemma wf_funpower:
  assumes "wf_items cfg inp I"
  shows " wf_items cfg inp (funpower (E_step k cfg inp) n I)"
(*<*)
  sorry
(*>*)
text\<open>@{thm[source] wf_E_step}, by induction on n\<close>

lemma wf_E:
  assumes "wf_items cfg inp I"
  shows "wf_items cfg inp (E k cfg inp I)"
(*<*)
  sorry
(*>*)
text\<open>@{thm[source] wf_funpower} by definition\<close>

lemma wf_E0:
  shows "wf_items cfg inp (E 0 cfg inp (Init cfg))"
(*<*)
  sorry
(*>*)
text\<open>@{thm[source] wf_Init} @{term wf_E} by definition\<close>

lemma wf_\<E>:
  shows "wf_items cfg inp (\<E> n cfg inp)"
(*<*)
  sorry
(*>*)
text\<open>@{thm[source] wf_E0} @{thm[source] wf_E} by induction on n\<close>

lemma wf_earley:
  shows "wf_items cfg inp (earley cfg inp)"
(*<*)
  sorry
(*>*)
text\<open>@{thm[source] wf_\<E>} by definition\<close>

section \<open>Soundness\<close>

definition sound_item :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a item \<Rightarrow> bool" where
  "sound_item cfg inp x = derives cfg [item_rule_head x] (slice (item_origin x) (item_end x) inp @ item_\<beta> x)"

definition sound_items :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> bool" where
  "sound_items cfg inp I \<equiv> \<forall>x \<in> I. sound_item cfg inp x"

lemma sound_Init:
  shows "sound_items cfg inp (Init cfg)"
(*<*)
  sorry
(*>*)

lemma sound_item_inc_item:
  assumes "wf_item cfg inp x" "sound_item cfg inp x"
  assumes "next_symbol x = Some a" "k < length inp" "inp!k = a" "item_end x = k"
  shows "sound_item cfg inp (inc_item x (k+1))"
(*<*)
  sorry
(*>*)

lemma sound_Scan:
  assumes "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (Scan k inp I)"
(*<*)
  sorry
(*>*)

lemma sound_Predict:
  assumes "sound_items cfg inp I"
  shows "sound_items cfg inp (Predict k cfg I)"
(*<*)
  sorry
(*>*)

lemma sound_Complete:
  assumes "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (Complete k I)"
(*<*)
  sorry
(*>*)

lemma sound_E_step:
  assumes "wf_items cfg inp I" "sound_items cfg inp I" 
  shows "sound_items cfg inp (E_step k cfg inp I)"
(*<*)
  sorry
(*>*)

lemma sound_funpower:
  assumes "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (funpower (E_step k cfg inp) n I)"
(*<*)
  sorry
(*>*)

lemma sound_E:
  assumes "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (E k cfg inp I)"
(*<*)
  sorry
(*>*)

lemma sound_E0:
  shows "sound_items cfg inp (E 0 cfg inp (Init cfg))"
(*<*)
  sorry
(*>*)

lemma sound_\<E>:
  shows "sound_items cfg inp (\<E> k cfg inp)"
(*<*)
  sorry
(*>*)

lemma sound_earley:
  shows "sound_items cfg inp (earley cfg inp)"
(*<*)
  sorry
(*>*)

theorem soundness:
  assumes "earley_recognized (earley cfg inp) cfg inp"
  shows "derives cfg [\<SS> cfg] inp"
(*<*)
  sorry
(*>*)

section \<open>Completeness\<close>

lemma Scan_\<E>:
  assumes "i+1 \<le> k" "k \<le> length inp" "x \<in> bin (\<E> k cfg inp) i"
  assumes "next_symbol x = Some a" "inp!i = a"
  shows "inc_item x (i+1) \<in> \<E> k cfg inp"
(*<*)
  sorry
(*>*)

lemma Predict_\<E>:
  assumes "i \<le> k" "x \<in> bin (\<E> k cfg inp) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set (\<RR> cfg)"
  shows "init_item (N,\<alpha>) i \<in> \<E> k cfg inp"
(*<*)
  sorry
(*>*)

lemma Complete_\<E>:
  assumes "i \<le> j" "j \<le> k" "x \<in> bin (\<E> k cfg inp) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set (\<RR> cfg)"
  assumes "i = item_origin y" "y \<in> bin (\<E> k cfg inp) j" "item_rule y = (N,\<alpha>)" "is_complete y"
  shows "inc_item x j \<in> \<E> k cfg inp"
(*<*)
  sorry
(*>*)

type_synonym 'a derivation = "(nat \<times> 'a rule) list"

definition Derives1 :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "Derives1 cfg u i r v \<equiv> 
     \<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> (N, \<alpha>) \<in> set (\<RR> cfg)
        \<and> r = (N, \<alpha>) \<and> i = length x"

fun Derivation :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a derivation \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "Derivation _ a [] b = (a = b)"
| "Derivation cfg a (d#D) b = (\<exists> x. Derives1 cfg a (fst d) (snd d) x \<and> Derivation cfg x D b)"

definition partially_completed :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> ('a derivation \<Rightarrow> bool) \<Rightarrow> bool" where
  "partially_completed k cfg inp I P \<equiv>
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length inp \<and>
      x \<in> bin I i \<and> next_symbol x = Some a \<and>
      Derivation cfg [a] D (slice i j inp) \<and> P D \<longrightarrow>
      inc_item x j \<in> I"

lemma fully_completed:
  assumes "j \<le> k" "k \<le> length inp"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> I" "wf_items cfg inp I"
  assumes "Derivation cfg (item_\<beta> x) D (slice j k inp)"
  assumes "partially_completed k cfg inp I (\<lambda>D'. length D' \<le> length D)"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> I"
(*<*)
  sorry
(*>*)

lemma partially_completed_\<E>:
  assumes "wf_cfg cfg"
  shows "partially_completed k cfg inp (\<E> k cfg inp) (\<lambda>_. True)"
(*<*)
  sorry
(*>*)

lemma partially_completed_earley:
  assumes "wf_cfg cfg"
  shows "partially_completed (length inp) cfg inp (earley cfg inp) (\<lambda>_. True)"
(*<*)
  sorry
(*>*)

theorem completeness:
  assumes "derives cfg [\<SS> cfg] inp" "is_sentence cfg inp" "wf_cfg cfg"
  shows "earley_recognized (earley cfg inp) cfg inp"
(*<*)
  sorry
(*>*)

corollary
  assumes "wf_cfg cfg" "is_sentence cfg inp"
  shows "earley_recognized (earley cfg inp) cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
(*<*)
  sorry
(*>*)

section \<open>Finiteness\<close>

lemma finiteness_UNIV_wf_item:
  shows "finite { x | x. wf_item cfg inp x }"
(*<*)
  sorry
(*>*)

theorem finiteness:
  shows "finite (earley cfg inp)"
(*<*)
  sorry
(*>*)

(*<*)
end
(*>*)
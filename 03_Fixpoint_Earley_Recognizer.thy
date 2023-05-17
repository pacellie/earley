(*<*)
theory "03_Fixpoint_Earley_Recognizer"
  imports
    "02_Earleys_Algorithm"
begin
(*>*)

chapter \<open>Earley's Algorithm Formalization \label{chapter:3}\<close>

text\<open>
In this chapter we shortly introduce the interactive theorem prover Isabelle/HOL \cite{Nipkow:2002} used as
the tool for verification in this thesis and recap some of the formalism of context-free grammars and their representation
in Isabelle. Then we formalize the simplified Earley recognizer algorithm presented in Chapter
\ref{chapter:2}; discussing the implementation and the proofs for soundness, completeness, and finiteness.
Note that most of the basic definitions of Sections \ref{sec:cfg} and \ref{sec:earley} are not our own work
but only slightly adapted from Obua's work on \textit{Local Lexing} \cite{Obua:2017} \cite{LocalLexing-AFP}. All of the proofs in this chapter are
our own work. 
\<close>

section\<open>Context-free grammars and Isabelle/HOL \label{sec:cfg}\<close>

text\<open>
Isabelle/HOL \cite{Nipkow:2002} is an interactive theorem prover based on a fragment of higher-order logic. It supports the core
concepts commonly known from functional programming languages. The notation $t :: \tau$ means that term $t$ has type
$\tau$. Basic types include \textit{bool}, \textit{nat}; type variables are written $'a$, $'b$, etc. Pairs are written
@{term "(a, b)"}; triples are written @{term "(a, b, c)"} and so forth but are internally represented as
nested pairs; the nesting is on the first component of a pair. Functions @{term fst} and @{term snd} return
the first and second component of a pair; the operator @{term "(\<times>)"} represents pairs at the type level.
Most type constructors are written postfix, e.g. $'a \, \textit{set}$ and $'a \, \textit{list}$; the function
space arrow is $\Rightarrow$; function \textit{set} converts a list into a set. Type synonyms are introduced via the \textit{type\_synonym} command. Algebraic data types are defined with the keyword \textit{datatype}.
Non-recursive definitions are introduced with the \textit{definition} keyword.

It is standard to define a language as a set of strings over a finite set of symbols. We deviate slightly by introducing a type variable $'a$
for the type of symbols. Thus a string corresponds to a list of symbols and a language is formalized as
a set of lists of symbols, a symbol being either a terminal or a non-terminal. We represent a context-free grammar as the datatype @{term CFG}. An instance @{term \<G>} consists of (1) a list of
non-terminals (@{term "\<NN> \<G>"}), (2) a list of terminals (@{term "\<TT> \<G>"}), (3) a list of production rules
(@{term "\<RR> \<G>"}), and a start symbol (@{term "\<SS> \<G>"}) where @{term \<NN>}, @{term \<TT>}, @{term \<RR>} and @{term \<SS>} are
projections accessing the specific part of an instance @{term \<G>} of the datatype @{term CFG}. Each rule consists of a left-hand side or @{term rule_head}, a single symbol,
and a right-hand side or @{term rule_body}, a list of symbols.
The productions with a particular non-terminal $N$ on their left-hand sides are called the alternatives of $N$.
We make the usual assumptions about the well-formedness of a context-free grammar: the intersection of the set of terminals and
the set of non-terminals is empty; the start symbol is a non-terminal; the rule head of a production
is a non-terminal and its rule body consists of only symbols. Additionally, since we are working with
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

definition rule_head :: "'a rule \<Rightarrow> 'a" where
  "rule_head = fst"

definition rule_body :: "'a rule \<Rightarrow> 'a list" where
  "rule_body = snd"

definition disjunct_symbols :: "'a cfg \<Rightarrow> bool" where
  "disjunct_symbols \<G> \<equiv> set (\<NN> \<G>) \<inter> set (\<TT> \<G>) = {}"

definition wf_startsymbol :: "'a cfg \<Rightarrow> bool" where
  "wf_startsymbol \<G> \<equiv> \<SS> \<G> \<in> set (\<NN> \<G>)"

definition wf_rules :: "'a cfg \<Rightarrow> bool" where
  "wf_rules \<G> \<equiv> \<forall>(N, \<alpha>) \<in> set (\<RR> \<G>). N \<in> set (\<NN> \<G>) \<and> (\<forall>s \<in> set \<alpha>. s \<in> set (\<NN> \<G>) \<union> set (\<TT> \<G>))"

definition distinct_rules :: "'a cfg \<Rightarrow> bool" where
  "distinct_rules \<G> \<equiv> distinct (\<RR> \<G>)"

definition wf_\<G> :: "'a cfg \<Rightarrow> bool" where
  "wf_\<G> \<G> \<equiv> disjunct_symbols \<G> \<and> wf_startsymbol \<G> \<and> wf_rules \<G> \<and> distinct_rules \<G>"

(*<*)
syntax
  "derives1" :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow> _" [1000,0] 1000)

syntax
  "derives" :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<^sup>* _" [1000,0] 1000)

syntax
  "slice" :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" ("_[_.. _\<rangle>" [1000,0] 1000)
(*>*)

text\<open>
Furthermore, in Isabelle, lists are constructed from the empty list @{term "[]"} via the infix cons-operator @{term "(#)"};
the operator @{term "(@)"} appends two lists; @{term "|xs|"} denotes the length and @{term "xs!n"} returns the $n$-th item of the list @{term xs}.
Sets follow the standard mathematical notation including
the commonly found set builder notation or set comprehensions @{term "{ x | x. P x}"}. Sets can also be defined
inductively using the keyword \textit{inductive\_set}.

Next we formalize the concept of a derivation. We use lowercase letters $a$, $b$, $c$ indicating terminal symbols; capital letters
$A$, $B$, $C$ denote non-terminals; lists of symbols are represented by greek letters: \alpha, \beta, \gamma, occasionally also by lowercase letters $u$, $v$, $w$.
The empty list in the context of a language is \epsilon. A sentential is a list consisting of only symbols. A sentence
is a sentential if it only contains terminal symbols. We first define a predicate @{term "derives1 \<G> u v"} which expresses that
we can derive $v$ from $u$ in a single step or the predicate holds if there exist $\alpha$, $\beta$, $N$ and $\gamma$ such that @{term "u = \<alpha> @ [N] @ \<beta>"},
@{term "v = \<alpha> @ \<gamma> @ \<beta>"} and @{term "(N, \<gamma>)"} is a production rule. We also introduce some slightly more convenient notation: @{term "derives1 \<G> u v"} is written @{term \<G>} $\vdash u \Rightarrow v$ in the following. We then can define the set of single-step derivations using @{term derives1},
and subsequently the set of all derivations given a particular grammar is the reflexive-transitive closure of the set of
single-step derivations. Finally, we say $v$ can be derived from $u$ given a grammar @{term \<G>} or @{term "derives \<G> u v"} if
@{term "(u, v) \<in> derivations \<G>"}. A slightly more convenient notation is again: @{term "derives \<G> u v"} $=$ @{term \<G>} $\vdash u \Rightarrow^{\ast} v$
\<close>

type_synonym 'a sentential = "'a list"

definition is_terminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_terminal \<G> s \<equiv> s \<in> set (\<TT> \<G>)"

definition is_nonterminal :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_nonterminal \<G> s \<equiv> s \<in> set (\<NN> \<G>)"

definition is_symbol :: "'a cfg \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_symbol \<G> s \<equiv> is_terminal \<G> s \<or> is_nonterminal \<G> s"

definition wf_sentential :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "wf_sentential \<G> s \<equiv> \<forall>x \<in> set s. is_symbol \<G> x"

definition is_sentence :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "is_sentence \<G> s \<equiv> \<forall>x \<in> set s. is_terminal \<G> x"

definition derives1 :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "derives1 \<G> u v \<equiv>
     \<exists> \<alpha> \<beta> N \<gamma>. 
         u = \<alpha> @ [N] @ \<beta>
       \<and> v = \<alpha> @ \<gamma> @ \<beta>
       \<and> (N, \<gamma>) \<in> set (\<RR> \<G>)"

definition derivations1 :: "'a cfg \<Rightarrow> ('a sentential \<times> 'a sentential) set" where
  "derivations1 \<G> = { (u,v) | u v. \<G> \<turnstile> u \<Rightarrow> v }"

definition derivations :: "'a cfg \<Rightarrow> ('a sentential \<times> 'a sentential) set" where 
  "derivations \<G> = (derivations1 \<G>)^*"

definition derives :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "derives \<G> u v \<equiv> (u, v) \<in> derivations \<G>"

text\<open>
Potentially recursive but provably total functions that may make use of pattern matching are defined with
the \textit{fun} and \textit{function} keywords; partial functions are defined via \textit{partial\_function}.
Take for example the function @{term slice} defined below. Term @{term "slice xs i j"} computes the slice of a list @{term xs}
between indices $i$ (inclusive) and $j$ (exclusive), e.g. @{term "slice [a, b, c, d, e] (2::nat) (4::nat)"} evaluates to @{term "[c, d]"}.
We also introduce a shorthand notation: e.g. @{term "slice xs i j"} is written @{term "xs"}$[ i..j \rangle$ in the following.
\<close>

fun slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "slice [] _ _ = []"
| "slice (x#xs) _ 0  = []"
| "slice (x#xs) 0 (Suc b) = x # slice xs 0 b"
| "slice (x#xs) (Suc a) (Suc b) = slice xs a b"

(*<*)
notation (latex output)
  derives1 ("_ \<turnstile> _ \<Rightarrow> _" [1000,0] 1000)

notation (latex output)
  derives ("_ \<turnstile> _ \<^latex>\<open>\\ensuremath{\\Rightarrow^{\\ast}}\<close> _" [1000,0] 1000)

notation (latex output)
  slice ("_[_.._\<rangle>" [1000,0] 1000)
(*>*)

text\<open>
Lemmas, theorems and corollaries are presented using the keywords \textit{lemma}, \textit{theorem}, \textit{corollary} respectively, followed
by their names. They consist of zero or more assumptions marked by \textit{assumes} keywords and one conclusion
indicated by \textit{shows}. E.g. we can proof a simple lemma about the interaction between the @{term slice} function
and the append operator @{term "(@)"}, stating the conditions under which we can split one slice into two.
\<close>

lemma slice_append:
  assumes "i \<le> j"
  assumes "j \<le> k"
  shows "xs[i..j\<rangle> @ xs[j..k\<rangle> = xs[i..k\<rangle>"
(*<*)
  sorry
(*>*)

section \<open>The Formalized Algorithm \label{sec:earley}\<close>

text\<open>
Next we formalize the algorithm presented in Chapter \ref{chapter:2}. First we define the datatype @{term item}
representing Earley items. For example, the item $S \rightarrow \, S + \bullet S, 2, 4$ consists of four parts:
a production rule (@{term item_rule}), a natural number (@{term item_bullet}) indicating the position of the bullet in
the production rule, and two natural numbers (@{term item_origin} inclusive, @{term item_end} exclusive) representing the portion
of the input string @{term \<omega>} that has been parsed by the item. Additionally, we introduce a few useful abbreviations:
the functions @{term item_rule_head} and @{term item_rule_body} access the @{term rule_head} respectively @{term rule_body}
of an item. Functions @{term item_\<alpha>} and @{term item_\<beta>} split the production rule body at the bullet, e.g. $S \rightarrow \, \alpha \bullet \beta$.
We call an item @{term complete} if the bullet is at the end of the production rule body. The next symbol (@{term next_symbol}) of
an item is either @{term None} if it is complete, or @{term "Some s"} where $s$ is the symbol in the production
rule body following the bullet. An item is finished if the item rule head is the start symbol, the item is complete, and
the whole input has been parsed or @{term "item_origin item = (0::nat)"} and @{term "item_end item = |\<omega>|"}. Finally, we call a set of
items @{term recognizing} if it contains at least one finished item, indicating that this set of items recognizes the input $\omega$.
\<close>

datatype 'a item = 
  Item 
    (item_rule: "'a rule") 
    (item_bullet : nat) 
    (item_origin : nat)
    (item_end : nat)

type_synonym 'a items = "'a item set"

definition item_rule_head :: "'a item \<Rightarrow> 'a" where
  "item_rule_head x = rule_head (item_rule x)"

definition item_rule_body :: "'a item \<Rightarrow> 'a sentential" where
  "item_rule_body x = rule_body (item_rule x)"

definition item_\<alpha> :: "'a item \<Rightarrow> 'a sentential" where
  "item_\<alpha> x = take (item_bullet x) (item_rule_body x)"

definition item_\<beta> :: "'a item \<Rightarrow> 'a sentential" where 
  "item_\<beta> x = drop (item_bullet x) (item_rule_body x)"

definition is_complete :: "'a item \<Rightarrow> bool" where
  "is_complete x \<equiv> item_bullet x \<ge> |item_rule_body x|"

definition next_symbol :: "'a item \<Rightarrow> 'a option" where
  "next_symbol x \<equiv> if is_complete x then None else Some (item_rule_body x ! item_bullet x)"

definition is_finished :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a item \<Rightarrow> bool" where
  "is_finished \<G> \<omega> x \<equiv> 
    item_rule_head x = \<SS> \<G> \<and>
    item_origin x = 0 \<and>
    item_end x = |\<omega>| \<and> 
    is_complete x"

definition recognizing :: "'a items \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "recognizing I \<G> \<omega> \<equiv> \<exists>x \<in> I. is_finished \<G> \<omega> x"

text\<open>
Normally we don't construct items directly via the @{term Item} constructor but use two auxiliary constructors:
the function @{term init_item} is used by the @{term Init} and @{term Predict} operations. It sets the @{term item_bullet} to 0 or
the beginning of the production rule body, initializes the @{term item_rule}, and indicates that this is an initial item
by assigning @{term item_origin} and @{term item_end} to the current position in the input. The function @{term inc_item}
returns a new item, moving the bullet over the next symbol (assuming there is one), and setting the @{term item_end} to the
current position in the input, leaving the item rule and origin untouched. It is utilized by the @{term Scan} and
@{term Complete} operations.
\<close>

definition init_item :: "'a rule \<Rightarrow> nat \<Rightarrow> 'a item" where
  "init_item r k = Item r 0 k k"

definition inc_item :: "'a item \<Rightarrow> nat \<Rightarrow> 'a item" where
  "inc_item x k = Item (item_rule x) (item_bullet x + 1) (item_origin x) k"

text\<open>
There are different approaches of defining the set of Earley items in accordance with the rules of Figure \ref{fig:inference_rules}.
We can take an abstract approach and define the set inductively using Isabelle's inductive sets,
or a more operational point of view. We take the latter approach and discuss the reasoning for this
decision end the end of this section.

Note that, as mentioned previously, even though we are only constructing one set of Earley items, conceptually all items with the same item end
form one Earley bin. Our operational approach is then the following: we generate Earley items bin by bin in ascending order,
starting from the $0$-th bin that contains all initial items computed by the @{term Init} operation. The three operations @{term Scan}, @{term Predict}, and @{term Complete}
all take as arguments the index of the current bin and the current set of Earley items. For the $k$-th bin
the @{term Scan} operation initializes the $k+1$-st bin, whereas the @{term Predict} and @{term Complete} operations
only generate items belonging to the $k$-th bin. We then define a function @{term Earley_step} that
returns the union of the set itself and applying the three operations to a set of Earley items. We complete the $k$-th
bin and initialize the $k+1$-th bin by iterating @{term Earley_step} until the set of items converges, captured by the @{term Earley_bin}
definition. The function @{term Earley} then generates the bins up to the $n$-th bin by applying the @{term Earley_bin}
function first to the initial set of items @{term Init} and continuing in ascending order bin by bin. Finally, we compute
the set of Earley items by applying function @{term Earley} to the length of the input.
\<close>

definition bin :: "'a items \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"

definition Init :: "'a cfg \<Rightarrow> 'a items" where
  "Init \<G> = { init_item r 0 | r. r \<in> set (\<RR> \<G>) \<and> fst r = (\<SS> \<G>) }"

definition Scan :: "nat \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Scan k \<omega> I = 
    { inc_item x (k+1) | x a.
        x \<in> bin I k \<and>
        \<omega>!k = a \<and>
        k < |\<omega>| \<and>
        next_symbol x = Some a }"

definition Predict :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Predict k \<G> I =
    { init_item r k | r x.
        r \<in> set (\<RR> \<G>) \<and>
        x \<in> bin I k \<and>
        next_symbol x = Some (rule_head r) }"

definition Complete :: "nat \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Complete k I =
    { inc_item x k | x y.
        x \<in> bin I (item_origin y) \<and>
        y \<in> bin I k \<and>
        is_complete y \<and>
        next_symbol x = Some (item_rule_head y) }"

definition Earley_step :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Earley_step k \<G> \<omega> I = I \<union> Scan k \<omega> I \<union> Complete k I \<union> Predict k \<G> I"

fun funpower :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "funpower f 0 x = x"
| "funpower f (Suc n) x = f (funpower f n x)"

definition natUnion :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "natUnion f = \<Union> { f n | n. True }"

definition limit :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit f x = natUnion (\<lambda> n. funpower f n x)"

definition Earley_bin :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "Earley_bin k \<G> \<omega> I = limit (Earley_step k \<G> \<omega>) I"

fun Earley :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items" where
  "Earley 0 \<G> \<omega> = Earley_bin 0 \<G> \<omega> (Init \<G>)"
| "Earley (Suc n) \<G> \<omega> = Earley_bin (Suc n) \<G> \<omega> (Earley n \<G> \<omega>)"

definition \<E>arley :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items" where
  "\<E>arley \<G> \<omega> = Earley |\<omega>| \<G> \<omega>"

text\<open>
We follow the operational approach of defining the set of Earley items primarily for two reasons: first of all, we reuse and only slightly adapt
most of the basic definitions of this chapter from the work of Obua on \textit{Local Lexing} \cite{Obua:2017} \cite{LocalLexing-AFP},
who takes the more operational approach and already defines useful lemmas, for example on function iteration.
Secondly, the operational approach maps more easily to the list-based implementation of the next chapter that
necessarily takes an ordered approach to generating Earley items. Nonetheless, in hindsight, defining the set
of Earley items inductively seems to be not only the more elegant approach but also might simplify some of the proofs of
this chapter, and is consequently future work worth considering.
\<close>

\<comment>\<open>TODO: illustrate inductive definition here\<close>

section \<open>Well-formedness\<close>

text\<open>
Due to the operational view of generating the set of Earley items, the proofs of, not only, well-formedness, but
also soundness and completeness follow a similar structure: we first proof a property about the basic building
blocks, the @{term Init}, @{term Scan}, @{term Predict}, and @{term Complete} operations. Then we proof that
this property is maintained iterating the function @{term Earley_step}, and thus holds for the @{term Earley_bin} operation.
Finally, we show that the function @{term Earley} maintains this property for all bins and thus for the @{term \<E>arley} definition, or
the set of Earley items.

Before we start to proof soundness and completeness of the generated set of Earley items, especially the
completeness proof is more involved, we highlight the general proof structure once in detail, for a simpler
property: well-formedness of the items, allowing us to concentrate only on the core aspects for the soundness
and completeness proofs.

An Earley item is well-formed (@{term wf_item}) if the item rule is a rule of the grammar; the item
bullet is bounded by the length of the item rule body; the item origin does not exceed the item end, and
finally the item end is at most the length of the input.
\<close>

definition wf_item :: "'a cfg \<Rightarrow> 'a sentential => 'a item \<Rightarrow> bool" where 
  "wf_item \<G> \<omega> x \<equiv> 
    item_rule x \<in> set (\<RR> \<G>) \<and> 
    item_bullet x \<le> |item_rule_body x| \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> |\<omega>|"

definition wf_items :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> bool" where
  "wf_items \<G> \<omega> I \<equiv> \<forall>x \<in> I. wf_item \<G> \<omega> x"

lemma wf_Init:
  shows "wf_items \<G> \<omega> (Init \<G>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_Scan_Predict_Complete:
  assumes "wf_items \<G> \<omega> I" 
  shows "wf_items \<G> \<omega> (Scan k \<omega> I \<union> Predict k \<G> I \<union> Complete k I)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_Earley_step:
  assumes "wf_items \<G> \<omega> I"
  shows "wf_items \<G> \<omega> (Earley_step k \<G> \<omega> I)"
(*<*)
  sorry
(*>*)

text\<open>
Lemmas @{thm[source] wf_Init}, @{thm[source] wf_Scan_Predict_Complete}, and @{thm[source] wf_Earley_step}
follow trivially by definition of the respective operations.
\<close>

lemma wf_funpower:
  assumes "wf_items \<G> \<omega> I"
  shows "wf_items \<G> \<omega> (funpower (Earley_step k \<G> \<omega>) n I)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_Earley_bin:
  assumes "wf_items \<G> \<omega> I"
  shows "wf_items \<G> \<omega> (Earley_bin k \<G> \<omega> I)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_Earley_bin0:
  shows "wf_items \<G> \<omega> (Earley_bin 0 \<G> \<omega> (Init \<G>))"
(*<*)
  sorry
(*>*)

text\<open>
We proof the lemma @{thm[source] wf_funpower} by induction on $n$ using lemma @{thm[source] wf_Earley_step}, and
lemmas @{thm[source] wf_Earley_bin} and @{thm[source] wf_Earley_bin0} follow immediately using additionally the fact
that @{term "x \<in> limit f X \<equiv> \<exists>n. x \<in> funpower f n X"} and lemma @{thm[source] wf_Init}.
\<close>

lemma wf_Earley:
  shows "wf_items \<G> \<omega> (Earley n \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma wf_\<E>arley:
  shows "wf_items \<G> \<omega> (\<E>arley \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>
Finally, lemma @{thm[source] wf_Earley} is proved by induction on $n$ using lemmas @{thm[source] wf_Earley_bin} 
and @{thm[source] wf_Earley_bin0}; lemma @{thm[source] wf_\<E>arley} follows by definition of @{term \<E>arley}.
\<close>

section \<open>Soundness\<close>

text\<open>
Next we proof the soundness of the generated items, or: $A \rightarrow \, \alpha \bullet \beta, i, j \in B \,\,\, \textrm{implies} \,\,\, A \, \xRightarrow{\ast} \, @{term \<omega>}[i..j) \beta$
which is stated in terms of our formalization by the @{term sound_item} definition below. As mentioned previously, the general proof structure
follows the proof for well-formedness. Thus, we only highlight one slightly more involved lemma stating the
soundness of the @{term Complete} operation while stating the remaining lemmas without explicit proof.
Additionally, proving lemma @{term sound_Complete} provides some insight into working with and proving properties
about derivations.
\<close>

definition sound_item :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a item \<Rightarrow> bool" where
  "sound_item \<G> \<omega> x = \<G> \<turnstile> [item_rule_head x] \<Rightarrow>\<^sup>* \<omega>[item_origin x..item_end x\<rangle> @ item_\<beta> x"

definition sound_items :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> bool" where
  "sound_items \<G> \<omega> I \<equiv> \<forall>x \<in> I. sound_item \<G> \<omega> x"

text\<open>
Obua \cite{Obua:2017} \cite{LocalLexing-AFP} defines derivations at two different abstraction levels.
The first representation is as the reflexive-transitive closure of the set of one-step derivations as introduced earlier in this chapter.
The second representation is again more operational. He defines a predicate @{term "Derives1 \<G> u i r v"}
that is conceptually analogous to the predicate @{term "\<G> \<turnstile> u \<Rightarrow> v"} but also captures the rule $r$
used for a single rewriting step and the position $i$ in $u$ where the rewriting occurs.
\<close>
(*<*)
syntax
  "Derives1" :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentential \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>(_, _) _" [1000,0] 1000)
(*>*)

definition Derives1 :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "Derives1 \<G> u i r v \<equiv> 
     \<exists> \<alpha> \<beta> N \<gamma>. 
          u = \<alpha> @ [N] @ \<beta>
        \<and> v = \<alpha> @ \<gamma> @ \<beta>
        \<and> (N, \<gamma>) \<in> set (\<RR> \<G>)
        \<and> r = (N, \<gamma>) \<and> i = |\<alpha>|"

text\<open>
He then defines the type of a \textit{derivation} as a list of pairs representing precisely the positions and rules
used to apply each rewrite step. The predicate @{term Derivation} is defined recursively as follows: @{term "Derivation \<alpha> [] \<beta>"} holds only if @{term "\<alpha> = \<beta>"}. If the derivation consists of at least one rewrite pair $(i, r)$, or
@{term "Derivation \<G> \<alpha> ((i, r)#D) \<beta>"}, then there must exist a $\gamma$ such that @{term "Derives1 \<G> \<alpha> i r \<gamma>"} and
@{term "Derivation \<G> \<gamma> D \<beta>"}. Note that we introduce once again a more convenient notation: e.g. @{term "Derivation \<alpha> D \<beta>"} is written @{term \<G>} $\vdash \alpha \Rightarrow^{\mathit{D}} \beta$ in the following. Obua then proves that both notions of a derivation are equivalent (lemma @{term derives_equiv_Derivation})
\<close>

type_synonym 'a derivation = "(nat \<times> 'a rule) list"

(*<*)
syntax
  "Derivation" :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a derivation \<Rightarrow> 'a sentential \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<^sup>_ _" [1000,0] 1000)
(*>*)

fun Derivation :: "'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a derivation \<Rightarrow> 'a sentential \<Rightarrow> bool" where
  "Derivation _ \<alpha> [] \<beta> = (\<alpha> = \<beta>)"
| "Derivation \<G> \<alpha> (d#D) \<beta> = (\<exists>\<gamma>. Derives1 \<G> \<alpha> (fst d) (snd d) \<gamma> \<and> Derivation \<G> \<gamma> D \<beta>)"

(*<*)
notation (latex output)
  Derives1 ("_ \<turnstile> _ \<Rightarrow>(_, _) _" [1000,0] 1000)

notation (latex output)
  Derivation ("_ \<turnstile> _ \<Rightarrow>\<^sup>_ _" [1000,0] 1000)
(*>*)

lemma derives_equiv_Derivation:
  shows "\<G> \<turnstile> \<alpha> \<Rightarrow>\<^sup>* \<beta> \<equiv> \<exists>D. \<G> \<turnstile> \<alpha> \<Rightarrow>\<^sup>D \<beta>"
(*<*)
  sorry
(*>*)

text\<open>
Next we state a small but useful lemma about rewriting derivations using the more operational
definition of derivations defined above without explicit proof.
\<close>

lemma Derivation_append_rewrite:
  assumes "\<G> \<turnstile> \<alpha> \<Rightarrow>\<^sup>D \<beta> @ \<gamma> @ \<delta>"
  assumes "\<G> \<turnstile> \<gamma> \<Rightarrow>\<^sup>E \<gamma>'"
  shows "\<exists>F. \<G> \<turnstile> \<alpha> \<Rightarrow>\<^sup>F \<beta> @ \<gamma>' @ \<delta>"
(*<*)
  sorry
(*>*)

text\<open>
And finally, we proof soundness of the @{term Complete} operation:
\<close>

lemma sound_Complete:
  assumes wf: "wf_items \<G> \<omega> I"
  assumes sound: "sound_items \<G> \<omega> I"
  shows "sound_items \<G> \<omega> (Complete k I)"
(*<*)
  sorry
(*>*)

text\<open>
\begin{proof}

Let $z$ denote an arbitrary but fixed item of @{term "Complete k I"}. By the definition of the
@{term Complete} operation there exist items $x$ and $y$ such that: @{term "x \<in> bin I (item_origin y)"},
@{term "y \<in> bin I k"}, @{term "is_complete y"}, @{term "next_symbol x = Some (item_rule_head y)"}, and
@{term "z = inc_item x k"}.

Since $y$ is in bin $k$, it is complete and the set $I$ is sound (assumption \textit{sound}),
there exists a derivation $E$ such that 
  $$@{term "\<G> \<turnstile> [item_rule_head y] \<Rightarrow>\<^sup>E \<omega>[item_origin y..item_end y\<rangle>"}$$
by lemma @{thm[source] derives_equiv_Derivation}. Similarly, since $x$ is in bin @{term "item_origin y"} and due to assumption \textit{sound},
there exists a derivation $D$ such that
  $$ @{term "\<G> \<turnstile> [item_rule_head x] \<Rightarrow>\<^sup>D \<omega>[item_origin x..item_origin y\<rangle> @ item_\<beta> x"}$$
Note that @{term "item_\<beta> x = (item_rule_head y) # tl (item_\<beta> x)"} since the next symbol of $x$ is equal to
the item rule head of $y$. Thus, by lemma @{thm[source] Derivation_append_rewrite}, and the definition of $D$ and $E$,
there exists a derivation $F$ such that

\begin{equation*}
\begin{split}
  & @{term "\<G> \<turnstile> [item_rule_head x] \<Rightarrow>\<^sup>F \<omega>[item_origin x..item_origin y\<rangle>"} \, @ \\
  & \quad \quad @{term "\<omega>[item_origin y..item_end y\<rangle> @ tl (item_\<beta> x)"}
\end{split}
\end{equation*}

Additionally, we know that $x$ and $y$ are well-formed items due to the facts that $x$ is in bin @{term "item_origin y"},
$y$ is in bin $k$, and the assumption @{term "wf_items \<G> \<omega> I"}. Thus, we can discharge the assumptions of
lemma @{thm[source] slice_append} (@{term "item_origin x \<le> item_origin y"} and @{term "item_origin y \<le> item_end y"})
and have 
  $$@{term "\<G> \<turnstile> [item_rule_head x] \<Rightarrow>\<^sup>F \<omega>[item_origin x..item_end y\<rangle> @ tl (item_\<beta> x)"}$$

Moreover, since @{term "z = inc_item x k"} and the next symbol of x is the item rule head of y, it follows
that @{term "tl (item_\<beta> x) = item_\<beta> z"}, and ultimately @{term "sound_item \<G> \<omega> z"}, again by the definition
of $z$ and lemma @{thm[source] derives_equiv_Derivation}.

\end{proof}
\<close>

lemma sound_Init:
  shows "sound_items \<G> \<omega> (Init \<G>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_Scan:
  assumes "wf_items \<G> \<omega> I"
  assumes "sound_items \<G> \<omega> I"
  shows "sound_items \<G> \<omega> (Scan k \<omega> I)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_Predict:
  assumes "sound_items \<G> \<omega> I"
  shows "sound_items \<G> \<omega> (Predict k \<G> I)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_Earley_step:
  assumes "wf_items \<G> \<omega> I"
  assumes "sound_items \<G> \<omega> I" 
  shows "sound_items \<G> \<omega> (Earley_step k \<G> \<omega> I)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_funpower:
  assumes "wf_items \<G> \<omega> I"
  assumes "sound_items \<G> \<omega> I"
  shows "sound_items \<G> \<omega> (funpower (Earley_step k \<G> \<omega>) n I)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_Earley_bin:
  assumes "wf_items \<G> \<omega> I"
  assumes "sound_items \<G> \<omega> I"
  shows "sound_items \<G> \<omega> (Earley_bin k \<G> \<omega> I)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_Earley_bin0:
  shows "sound_items \<G> \<omega> (Earley_bin 0 \<G> \<omega> (Init \<G>))"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_Earley:
  shows "sound_items \<G> \<omega> (Earley k \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma sound_\<E>arley:
  shows "sound_items \<G> \<omega> (\<E>arley \<G> \<omega>)"
(*<*)
  sorry
(*>*)

text\<open>
Finally, using @{thm[source] sound_\<E>arley} and the definitions of @{term sound_item}, @{term recognizing},
@{term is_finished} and @{term is_complete} the final theorem follows: if the generated set of Earley
items is @{term recognizing}, or contains a \textit{finished} item, then there exists a derivation
of the input $\omega$ from the start symbol of the grammar.
\<close>

theorem soundness:
  assumes "recognizing (\<E>arley \<G> \<omega>) \<G> \<omega>"
  shows "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry
(*>*)

section \<open>Completeness\<close>

text\<open>
Next we prove completeness and consequently obtain a concluded correctness proof using theorem
@{thm[source] soundness}. The completeness proof is by far the most involved proof of this chapter. Thus
we present it in greater detail, and also slightly deviate from the proof structure of the well-formedness
and soundness proofs presented previously. We directly start to prove three properties of the @{term Earley}
function that correspond conceptually to the three different operations that can occur while generating
the bins.

We need three simple lemmas concerning the @{term Earley_bin} function, stated without explicit proof: (1) @{term "Earley_bin k \<G> \<omega> I"}
only (potentially) changes bins $k$ and $k+1$ (lemma @{term Earley_bin_bin_idem}); (2) the @{term Earley_step}
operation is subsumed by the @{term Earley_bin} operation, since it computes the limit of @{term Earley_step}
(lemma @{term Earley_step_sub_Earley_bin}); and (3) the function @{term Earley_bin} is idempotent (lemma @{term Earley_bin_idem}).
\<close>

lemma Earley_bin_bin_idem:
  assumes "i \<noteq> k"
  assumes "i \<noteq> k+1" 
  shows "bin (Earley_bin k \<G> \<omega> I) i = bin I i"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_step_sub_Earley_bin:
  shows "Earley_step k \<G> \<omega> I \<subseteq> Earley_bin k \<G> \<omega> I"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Earley_bin_idem:
  shows "Earley_bin k \<G> \<omega> (Earley_bin k \<G> \<omega> I) = Earley_bin k \<G> \<omega> I"
(*<*)
  sorry
(*>*)

text\<open>Next, we proof lemma @{term Scan_Earley} in detail: it describes under which assumptions the function
@{term Earley} generates a 'scanned' item:
\<close>

lemma Scan_Earley:
  assumes "i+1 \<le> k"
  assumes "x \<in> bin (Earley k \<G> \<omega>) i"
  assumes "next_symbol x = Some a"
  assumes "k \<le> |\<omega>|"
  assumes "\<omega>!i = a"
  shows "inc_item x (i+1) \<in> Earley k \<G> \<omega>"
(*<*)
  sorry
(*>*)

text\<open>
\begin{proof}

The proof is by induction in $k$ for arbitrary $i$, $x$, and $a$:

The base case @{term "k = (0::nat)"} is trivial, since we have the assumption @{term "i+(1::nat) \<le> 0"}.

For the induction step we can assume @{term "i+(1::nat) \<le> k+1"}, @{term "k+(1::nat) \<le> |\<omega>|"},
@{term "x \<in> bin (Earley (k+1) \<G> \<omega>) i"} , @{term "next_symbol x = Some a"}, and @{term "\<omega>!i = a"}.
Assumptions @{term "x \<in> bin (Earley (k+1) \<G> \<omega>) i"} and @{term "i+(1::nat) \<le> k+1"} imply that
@{term "x \<in> bin (Earley k \<G> \<omega>) i"} by lemma @{thm[source] Earley_bin_bin_idem}.

We then consider two cases: 
\begin{itemize}
  \item @{term "i+(1::nat) \<le> k"}: We can apply the induction hypothesis using assumptions
    @{term "k+(1::nat) \<le> |\<omega>|"}, @{term "next_symbol x = Some a"}, @{term "\<omega>!i = a"} and 
    additionally @{term "x \<in> bin (Earley k \<G> \<omega>) i"} and have @{term "inc_item x (i+1) \<in> Earley k \<G> \<omega>"}.
    The statement to proof follows by lemma @{thm[source] Earley_step_sub_Earley_bin} and the definition of
    @{term Earley_step}.
  \item @{term "i+(1::nat) > k"}: We have @{term "i = k"}, since @{term "i+(1::nat) \<le> k+1"}.
    Thus, we have @{term "inc_item x (i+1) \<in> Scan k \<omega> (Earley k \<G> \<omega>)"} using assumptions
    @{term "k+(1::nat) \<le> |\<omega>|"}, @{term "next_symbol x = Some a"}, @{term "\<omega>!i = a"}, and additionally
    @{term "x \<in> bin (Earley k \<G> \<omega>) i"} by the definition of the @{term Scan} operation.
    This in turn implies @{term "inc_item x (i+1) \<in> Earley_step k \<G> \<omega> (Earley k \<G> \<omega>)"} by lemma @{thm[source] Earley_step_sub_Earley_bin}
    and the definition of @{term Earley_step}. Since the function @{term Earley_bin} is idempotent
    (lemma @{thm[source] Earley_bin_idem}), we have @{term "inc_item x (i+1) \<in> Earley k \<G> \<omega>"} by definition of
    @{term Earley}. And again, the final statement follows by lemma @{thm[source] Earley_step_sub_Earley_bin} and the definition of
    @{term Earley_step}.
\end{itemize}

\end{proof}
\<close>

lemma Predict_Earley:
  assumes "i \<le> k"
  assumes "x \<in> bin (Earley k \<G> \<omega>) i"
  assumes "next_symbol x = Some N"
  assumes "(N,\<alpha>) \<in> set (\<RR> \<G>)"
  shows "init_item (N,\<alpha>) i \<in> Earley k \<G> \<omega>"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma Complete_Earley:
  assumes "i \<le> j"
  assumes "j \<le> k"
  assumes "x \<in> bin (Earley k \<G> \<omega>) i"
  assumes "next_symbol x = Some N"
  assumes "(N,\<alpha>) \<in> set (\<RR> \<G>)"
  assumes "y \<in> bin (Earley k \<G> \<omega>) j"
  assumes "item_rule y = (N,\<alpha>)"
  assumes "i = item_origin y"
  assumes "is_complete y"
  shows "inc_item x j \<in> Earley k \<G> \<omega>"
(*<*)
  sorry
(*>*)

text\<open>The proof of lemmas @{thm[source] Predict_Earley} and @{thm[source] Complete_Earley} are similar in structure
to the proof of lemma @{thm[source] Scan_Earley} with the exception of the base case that is in both cases non-trivial
but can be proven with the help of lemmas @{thm[source] Earley_step_sub_Earley_bin} and @{thm[source] Earley_bin_idem}, the
definition of @{term Earley_bin} and the definitions of @{term Predict} and @{term Complete}, respectively.

Next we give some intuition about the core idea of the completeness proof. Assume there exists an
item $N \rightarrow \, \bullet A_0 A_1 \dots A_n$ in a \textit{complete} (we define what exactly this means) set of items $I$ where $A_i$ are either terminal or non-terminal symbols.
Furthermore, assume there exist the following derivations for $i_0 \le i_1 \le \dots \le i_n \le i_{n+1}$:
\begin{equation*}
\begin{split}
  & A_0 \xRightarrow{\ast} \, \omega[i_0 .. i_1) \\
  & A_1 \xRightarrow{\ast} \, \omega[i_1 .. i_2) \\
  & \dots \\
  & A_n \xRightarrow{\ast} \, \omega[i_n .. i_{n+1}) \\
\end{split}
\end{equation*}

We have one derivation to move the bullet over each terminal or non-terminal $A_i$ and consequently the
item $N \rightarrow \, A_0 A_1 \dots A_n \bullet$ should be in $I$ if $I$ is a \textit{complete} set of items.

We formalize this idea as follows: a set $I$ is @{term partially_completed} if for each non-complete
item $x$ in $I$, the existence of a derivation $D$ from the next symbol of $x$ implies, that the item
that can be obtained by moving the bullet over the next symbol of $x$, is also present in $I$.
The full definition of @{term partially_completed} below is slightly more involved since we need to
keep track of the validity of the indices. Note that the definition also requires that an arbitrary
predicate $P$ holds for the derivation $D$. This predicate is necessary since the completeness proof
requires a proof on the length of the derivation $D$, and thus we limit the @{term partially_completed}
property to derivations that don't exceed a certain length.

Lemma @{term partially_completed_upto} then formalizes the core idea: if the item
$N \rightarrow \, \alpha \bullet \beta, i, j$ exists in a set of items $I$ and there exists a derivation
$\beta \xRightarrow{D} \omega[j..k)$, then $I$ also contains the complete item 
$N \rightarrow \, \alpha \beta \bullet, i, k$. Note that this
holds only if @{term "j \<le> k"}, @{term "k \<le> |\<omega>|"}, all items of $I$ are well-formed and most importantly
$I$ must be @{term partially_completed} up to the length of the derivation $D$.
\<close>

definition partially_completed :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentential \<Rightarrow> 'a items \<Rightarrow> ('a derivation \<Rightarrow> bool) \<Rightarrow> bool" where
  "partially_completed k \<G> \<omega> I P \<equiv>
    \<forall>i j x a D.
      i \<le> j \<and>
      j \<le> k \<and>
      k \<le> |\<omega>| \<and>
      x \<in> bin I i \<and>
      next_symbol x = Some a \<and>
      \<G> \<turnstile> [a] \<Rightarrow>\<^sup>D \<omega>[i..j\<rangle> \<and>
      P D \<longrightarrow>
      inc_item x j \<in> I"

text\<open>
To proof lemma @{term partially_completed_upto}, we need two auxiliary lemmas: The first one is about splitting derivations (lemma @{term  Derivation_append_split}):
a derivation $\alpha \beta \xRightarrow{D}\, \gamma$, can be split into two derivations $E$ and $F$
whose length is bounded by the length of $D$, and there exist @{term "\<alpha>'"} and @{term "\<beta>'"} such that
$\alpha \xRightarrow{E} \alpha'$, $\beta \xRightarrow{F} \beta'$ and @{term "\<gamma> = \<alpha>' @ \<beta>'"}. The proof
is by induction on $D$ for arbitrary $\alpha$ and $\beta$ and quite technical since we need to manipulate
the exact indices where each rewriting rule is applied in $\alpha$ and $\beta$, and thus we omit it.

The second one is a, in spirit similar, lemma about splitting slices (lemma @{term slice_append_split}). The proof
is straightforward by induction on the computation of the @{term slice} function, we also omit it, and
move on to the proof of lemmas @{term partially_completed_upto} and @{term partially_completed_Earley}.
\<close>

lemma Derivation_append_split:
  assumes "\<G> \<turnstile> (\<alpha>@\<beta>) \<Rightarrow>\<^sup>D \<gamma>"
  shows "\<exists>E F \<alpha>' \<beta>'. \<G> \<turnstile> \<alpha> \<Rightarrow>\<^sup>E \<alpha>' \<and> \<G> \<turnstile> \<beta> \<Rightarrow>\<^sup>F \<beta>' \<and> \<gamma> = \<alpha>' @ \<beta>' \<and> |E| \<le> |D| \<and> |F| \<le> |D|"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma slice_append_split:
  assumes "i \<le> k"
  assumes "xs[i..k\<rangle> = ys @ zs"
  shows "\<exists>j. ys = xs[i..j\<rangle> \<and> zs = xs[j..k\<rangle> \<and> i \<le> b \<and> b \<le> k"
(*<*)
  sorry
(*>*)

text\<open>\<close>

lemma partially_completed_upto:
  assumes "wf_items \<G> \<omega> I"
  assumes "j \<le> k" 
  assumes "k \<le> |\<omega>|"
  assumes "x = Item (N,\<alpha>) b i j"
  assumes "x \<in> I"
  assumes "\<G> \<turnstile> (item_\<beta> x) \<Rightarrow>\<^sup>D \<omega>[j..k\<rangle>"
  assumes "partially_completed k \<G> \<omega> I (\<lambda>D'. |D'| \<le> |D| )"
  shows "Item (N,\<alpha>) |\<alpha>| i k \<in> I"
(*<*)
  sorry
(*>*)

text\<open>
\begin{proof}

The proof is by induction on (@{term "item_\<beta> x"}) for arbitrary $b$, $i$, $j$, $k$, $N$, $\alpha$,
$x$, and $D$:

For the base case we have @{term "item_\<beta> x = []"} and need to show that @{term "Item (N, \<alpha>) |\<alpha>| i k \<in> I"}:

The bullet of $x$ is right before @{term "item_\<beta> x"}, or @{term "item_\<alpha> x = \<alpha>"}. Thus, the value of the
bullet must be equal to the length of $\alpha$, which implies @{term "x = Item (N,\<alpha>) |\<alpha>| i j"}, since $x$
is a well-formed item and @{term "item_\<beta> x = []"}.

We also know that $j = k$: we have @{term "\<G> \<turnstile> (item_\<beta> x) \<Rightarrow>\<^sup>D \<omega>[j..k\<rangle>"} and
@{term "item_\<beta> x = []"} which in turn implies that @{term "\<omega>[j..k\<rangle> = []"}, and thus $j = k$.

Hence, the statement follows from the assumption @{term "x \<in> I"} and the fact that @{term "x = Item (N,\<alpha>) |\<alpha>| i j"}.

For the induction step we have @{term "item_\<beta> x = a#as"} and need to show that @{term "Item (N, \<alpha>) |\<alpha>| i k \<in> I"}:

Using lemmas @{thm[source] Derivation_append_split} and @{thm[source] slice_append_split}
there exists an index $j'$ and derivations $E$ and $F$ such that

\begin{equation*}
\begin{split}
 @{term "\<G> \<turnstile> [a] \<Rightarrow>\<^sup>E \<omega>[j..j'\<rangle>"} \qquad & @{term "|E| \<le> |D|"} \\
 @{term "\<G> \<turnstile> as \<Rightarrow>\<^sup>F \<omega>[j'..k\<rangle>"} \qquad & @{term "|F| \<le> |D|"} \\
 @{term "j \<le> j'"} \qquad @{term "j' \<le> k"} &
\end{split}
\end{equation*}

Using the facts about derivation $E$, @{term "j \<le> j'"}, @{term "j' \<le> k"} and the assumptions
@{term "k \<le> |\<omega>|"}, @{term "x = Item (N, \<alpha>) b i j"}, @{term "x \<in> I"}, @{term "next_symbol x = Some a"}
(since @{term "item_\<beta> x = a#as"}) and @{term "x \<in> bin I j"}, we have @{term "inc_item x j' \<in> I"} by the
assumption @{term "partially_completed k \<G> \<omega> I (\<lambda>D'. |D'| \<le> |D| )"}.
Note that @{term "inc_item x j' = Item (N, \<alpha>) (b+1) i j'"}, which we will from now on refer to as item $x'$.

From @{term "partially_completed k \<G> \<omega> I (\<lambda>D'. |D'| \<le> |D| )"} and @{term "|F| \<le> |D|"}
follows @{term "partially_completed k \<G> \<omega> I (\<lambda>D'. |D'| \<le> |F| )"}. We also have @{term "as = item_\<beta> x'"}
and @{term "x' \<in> I"}. Hence, we can apply the induction hypothesis for $x'$ using additionally the assumptions
@{term "wf_items \<G> \<omega> I"}, @{term "k \<le> |\<omega>|"}, and the facts about derivation $F$ from above, and
have @{term "Item (N, \<alpha>) |\<alpha>| i k \<in> I"}, what we intended to show.

\end{proof}
\<close>

lemma partially_completed_Earley:
  assumes "wf_\<G> \<G>"
  shows "partially_completed k \<G> \<omega> (Earley k \<G> \<omega>) (\<lambda>_. True)"
(*<*)
  sorry
(*>*)

text\<open>
\begin{proof}

Let $x$, $i$, $a$, $D$, and $j$ be arbitrary but fixed.

By definition of @{term partially_completed} we can assume @{term "i \<le> j"}, @{term "j \<le> k"},
@{term "k \<le> |\<omega>|"}, @{term "x \<in> bin (Earley k \<G> \<omega>) i"}, @{term "next_symbol x = Some a"},
@{term "\<G> \<turnstile> [a] \<Rightarrow>\<^sup>D \<omega>[i..j\<rangle>"}, and need to show @{term "inc_item x j \<in> Earley k \<G> \<omega>"}.

We proof this by complete induction on @{term "|D|"} for arbitrary $x$, $i$, $a$, $j$, and $D$,
and split the proof into two different cases:

\begin{itemize}

  \item @{term "D = []"}: Since @{term "\<G> \<turnstile> [a] \<Rightarrow>\<^sup>D \<omega>[i..j\<rangle>"}, we have @{term "[a] = \<omega>[i..j\<rangle>"},
  and consequently @{term "\<omega>!i = a"} and @{term "j = i+(1::nat)"}. Now we discharge the assumptions of lemma @{thm[source] Scan_Earley},
  using additionally @{term "x \<in> bin (Earley k \<G> \<omega>) i"}, @{term "next_symbol x = Some a"}, and @{term "j \<le> |\<omega>|"},
  and have @{term "inc_item x (i+1) \<in> Earley k \<G> \<omega>"} which finishes the proof since @{term "j = i+(1::nat)"}.
  
  \item @{term "D = d#\<D>"}: Since @{term "\<G> \<turnstile> [a] \<Rightarrow>\<^sup>D \<omega>[i..j\<rangle>"}, there exists an $\alpha$ such that
  @{term "Derives1 \<G> [a] (fst d) (snd d) \<alpha>"} and @{term "\<G> \<turnstile> \<alpha> \<Rightarrow>\<^sup>\<D> \<omega>[i..j\<rangle>"}. From the definition
  of @{term "Derives1"} we see that there exists a non-terminal $N$ such that @{term "a = N"},
  @{term "(N, \<alpha>) \<in> set (\<RR> \<G>)"}, @{term "fst d = (0::nat)"}, and @{term "snd d = (N, \<alpha>)"}.

  Let $y$ denote @{term "Item (N,\<alpha>) 0 i i"}. Since we have @{term "i \<le> k"}, @{term "x \<in> bin (Earley k \<G> \<omega>) i"},
  and @{term "next_symbol x = Some a"} by assumption, we showed that @{term "a = N"} and @{term "(N, \<alpha>) \<in> set (\<RR> \<G>)"},
  and $y$ is an initial item, we have @{term "y \<in> Earley k \<G> \<omega>"} by lemma @{thm[source] Predict_Earley}.

  Next, we use lemma @{thm[source] partially_completed_upto} to show that we the completed version
  of item $y$ is also present in the $j$-th bin of @{term "Earley k \<G> \<omega>"} since we have a derivation
  @{term "\<G> \<turnstile> \<alpha> \<Rightarrow>\<^sup>\<D> \<omega>[i..j\<rangle>"}, or @{term "Item (N,\<alpha>) |\<alpha>| i j \<in> bin (Earley k \<G> \<omega>) j"}:
  we have @{term "i \<le> j"}, @{term "j \<le> |\<omega>|"} by assumption; have proven @{term "y \<in> Earley k \<G> \<omega>"};
  and have @{term "wf_items \<G> \<omega> (Earley k \<G> \<omega>)"} by lemma @{thm[source] wf_Earley}. Additionally, we know
  @{term "\<G> \<turnstile> (item_\<beta> y) \<Rightarrow>\<^sup>\<D> \<omega>[i..j\<rangle>"} since @{term "\<G> \<turnstile> [a] \<Rightarrow>\<^sup>\<D> \<omega>[i..j\<rangle>"} and
  @{term "a = N"}, by the definition of item $y$. Finally, we use the induction hypothesis to show
  @{term "partially_completed k \<G> \<omega> (Earley k \<G> \<omega>) (\<lambda>E. |E| \<le> |\<D>| )"}, since @{term "|\<D>| \<le> |D|"}
  by definition of @{term partially_completed}, using once again all of our assumptions. This in turn implies
  @{term "partially_completed j \<G> \<omega> (Earley k \<G> \<omega>) (\<lambda>E. |E| \<le> |\<D>| )"} since
  @{term "j \<le> k"} by definition of @{term partially_completed}. Now we can use lemma @{thm[source] partially_completed_upto}, and the statement follows
  from the definition of a bin.

  Finally, we prove @{term "inc_item x j \<in> Earley k \<G> \<omega>"} by lemma @{thm[source] Complete_Earley}:
  once again we have @{term "i \<le> j"}, @{term "j \<le> k"}, and @{term "x \<in> bin (Earley k \<G> \<omega>) i"} by assumption.
  We also know that @{term "next_symbol x = Some N"}, due to our assumption @{term "next_symbol x = Some a"}
  and @{term "a = N"}. Moreover, we have @{term "(N, \<alpha>) \<in> set (\<RR> \<G>)"} and most importantly
  @{term "Item (N,\<alpha>) |\<alpha>| i j \<in> bin (Earley k \<G> \<omega>) j"}, which concludes this proof.
  
\end{itemize}

\end{proof}
\<close>

text\<open>
Lemma @{term partially_completed_\<E>arley} follows trivially from @{thm[source] partially_completed_Earley}
by definition of @{term \<E>arley}.
\<close>

lemma partially_completed_\<E>arley:
  assumes "wf_\<G> \<G>"
  shows "partially_completed |\<omega>| \<G> \<omega> (\<E>arley \<G> \<omega>) (\<lambda>_. True)"
(*<*)
  sorry
(*>*)

text\<open>And finally, we can proof completeness of Earley's algorithm, obtaining corollary @{term correctness_\<E>arley}
due to lemma @{thm[source] soundness}.\<close>

theorem completeness:
  assumes "wf_\<G> \<G>"
  assumes "is_sentence \<G> \<omega>"
  assumes "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
  shows "recognizing (\<E>arley \<G> \<omega>) \<G> \<omega>"
(*<*)
  sorry
(*>*)

text\<open>
\begin{proof}

We know that there exists an $\alpha$ and a derivation $D$ such that @{term "(\<SS> \<G>, \<alpha>) \<in> set (\<RR> \<G>)"} and @{term "\<G> \<turnstile> \<alpha> \<Rightarrow>\<^sup>D \<omega>"},
since @{term "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"}. Let $x$ denote the item @{term "Item (\<SS> \<G>, \<alpha>) 0 0 0"}. By definition
of $x$ and the @{term Init} operation and @{term \<E>arley} function, and the fact that @{term "Init \<G> \<subseteq> Earley k \<G> \<omega>"}, 
we have @{term "x \<in> \<E>arley \<G> \<omega>"}, moreover we have @{term "partially_completed |\<omega>| \<G> \<omega> (\<E>arley \<G> \<omega>) (\<lambda>_. True)"}
using lemma @{thm[source] partially_completed_\<E>arley} and assumption @{term "wf_\<G> \<G>"}, and thus have
@{term "Item (\<SS> \<G>,\<alpha>) |\<alpha>| 0 |\<omega>| \<in> \<E>arley \<G> \<omega>"} by lemmas @{thm[source] partially_completed_upto} and
@{thm[source] wf_\<E>arley} and the definition of @{term partially_completed}. The statement @{term "recognizing (\<E>arley \<G> \<omega>) \<G> \<omega>"}
follows immediately by the definition of @{term recognizing}, @{term is_finished}, and @{term is_complete}.

\end{proof}
\<close>

corollary correctness_\<E>arley:
  assumes "wf_\<G> \<G>"
  assumes "is_sentence \<G> \<omega>"
  shows "recognizing (\<E>arley \<G> \<omega>) \<G> \<omega> \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
(*<*)
  sorry
(*>*)

section \<open>Finiteness\<close>

text\<open>At last, we prove that the set of Earley items is finite. In Chapter \ref{chap:04}
we are using this result to prove the termination of an executable version of the algorithm.

Since @{term "\<E>arley \<G> \<omega>"} only generates well-formed items (lemma @{thm[source] wf_\<E>arley}) it suffices
to prove that there only exists a finite number of well-formed items. Define 
  $$@{term "T = (set (\<RR> \<G>) \<times> {0::nat..m} \<times> {0..|\<omega>|} \<times> {0..|\<omega>| }) "} $$
where @{term "m = Max { |rule_body r| | r. r \<in> set (\<RR> \<G>) }"}. The set $T$ is finite since there
exists only a finite number of production rules and
@{term "{ x | x. wf_item \<G> \<omega> x }"} is a subset of mapping the @{term Item} constructor over $T$ (strictly speaking
we need to first unpack the quadruple).
\<close>

lemma finiteness_UNIV_wf_item:
  shows "finite { x | x. wf_item \<G> \<omega> x }"
(*<*)
  sorry
(*>*)

text\<open>\<close>

theorem finiteness:
  shows "finite (\<E>arley \<G> \<omega>)"
(*<*)
  sorry
(*>*)

(*<*)
end
(*>*)
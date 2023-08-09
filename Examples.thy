theory Examples
  imports Earley_Parser
begin

section \<open>Epsilon productions\<close>

definition \<epsilon>_free :: "('a, 'b) cfg \<Rightarrow> bool" where
  "\<epsilon>_free \<G> \<longleftrightarrow> (\<forall>r \<in> set (\<RR> \<G>). rule_body r \<noteq> [])"

lemma \<epsilon>_free_impl_non_empty_word_deriv:
  "\<epsilon>_free \<G> \<Longrightarrow> a \<noteq> [] \<Longrightarrow> \<not> Derivation \<G> a D []"
proof (induction "length D" arbitrary: a D rule: nat_less_induct)
  case 1
  show ?case
  proof (rule ccontr)
    assume assm: "\<not> \<not> Derivation \<G> a D []"
    show False
    proof (cases "D = []")
      case True
      then show ?thesis
        using "1.prems"(2) assm by auto
    next
      case False
      then obtain d D' \<alpha> where *:
        "D = d # D'" "Derives1 \<G> a (fst d) (snd d) \<alpha>" "Derivation \<G> \<alpha> D' []" "snd d \<in> set (\<RR> \<G>)"
        using list.exhaust assm Derives1_def by (metis Derivation.simps(2))
      show ?thesis
      proof cases
        assume "\<alpha> = []"
        thus ?thesis
          using *(2,4) Derives1_split \<epsilon>_free_def rule_body_def "1.prems"(1) by (metis append_is_Nil_conv)
      next
        assume "\<not> \<alpha> = []"
        thus ?thesis
          using *(1,3) "1.hyps" "1.prems"(1) by auto
      qed
    qed
  qed
qed

lemma \<epsilon>_free_impl_non_empty_deriv:
  "\<epsilon>_free \<G> \<Longrightarrow> \<forall>s. \<not> \<G> \<turnstile> [s] \<Rightarrow>\<^sup>* []"
  using \<epsilon>_free_impl_non_empty_word_deriv derives_implies_Derivation by (metis not_Cons_self2)

lemma nonempty_deriv_impl_\<epsilon>_free:
  assumes "\<forall>s. \<not> \<G> \<turnstile> [s] \<Rightarrow>\<^sup>* []"
  shows "\<epsilon>_free \<G>"
proof (rule ccontr)
  assume "\<not> \<epsilon>_free \<G>"
  then obtain N \<alpha> where *: "(N, \<alpha>) \<in> set (\<RR> \<G>)" "rule_body (N, \<alpha>) = []"
    unfolding \<epsilon>_free_def by auto
  hence "\<G> \<turnstile> [N] \<Rightarrow> []"
    unfolding derives1_def rule_body_def by auto
  hence "\<G> \<turnstile> [N] \<Rightarrow>\<^sup>* []"
    by auto
  thus False
    using assms(1) by blast
qed

lemma nonempty_deriv_iff_\<epsilon>_free:
  shows "(\<forall>s. \<not> \<G> \<turnstile> [s] \<Rightarrow>\<^sup>* []) \<longleftrightarrow> \<epsilon>_free \<G>"
  using \<epsilon>_free_impl_non_empty_deriv nonempty_deriv_impl_\<epsilon>_free by blast

section \<open>recognizing executable code\<close>

definition recognizing_code :: "('a, 'b) bins \<Rightarrow> ('a, 'b) cfg \<Rightarrow> ('a, 'b) word \<Rightarrow> bool" where
  "recognizing_code bs \<G> \<omega> \<equiv> \<exists>x \<in> set (items (bs ! length \<omega>)). is_finished \<G> \<omega> x"

lemma recognizing_code_iff_recognizing:
  assumes "wf_bins \<G> \<omega> bs" "length bs = length \<omega> + 1"
  shows "recognizing_code bs \<G> \<omega> \<longleftrightarrow> recognizing (bins bs) \<G> \<omega>" (is "?L \<longleftrightarrow> ?R")
proof standard
  assume ?L
  then obtain x where "x \<in> set (items (bs ! length \<omega>))" "is_finished \<G> \<omega> x"
    using assms(1) unfolding recognizing_code_def by blast
  moreover have "x \<in> bins bs"
    using assms(2) kth_bin_sub_bins \<open>x \<in> set (items (bs ! length \<omega>))\<close> by (metis (no_types, lifting) less_add_one subsetD)
  ultimately show ?R
    unfolding recognizing_def by blast
next
  assume ?R
  thus ?L
    using assms wf_item_in_kth_bin unfolding recognizing_code_def recognizing_def is_finished_def by blast
qed

corollary recognizing_code_iff_recognizing_Earley\<^sub>L:
  assumes "wf_\<G> \<G>"
  shows "recognizing_code (Earley\<^sub>L \<G> \<omega>) \<G> \<omega> \<longleftrightarrow> recognizing (bins (Earley\<^sub>L \<G> \<omega>)) \<G> \<omega>"
  using recognizing_code_iff_recognizing assms wf_bins_Earley\<^sub>L length_Earley\<^sub>L_bins length_bins_Init\<^sub>L
  by (metis Earley\<^sub>L_def nle_le)

section \<open>Example 1: Addition\<close>

datatype T1 = x | plus
datatype N1 = S

definition rules1 :: "(T1, N1) rule list" where
  "rules1 = [
    (NT S, [T x]),
    (NT S, [NT S, T plus, NT S])
  ]"

definition start_symbol1 :: "(T1, N1) symbol" where
  "start_symbol1 = NT S"

definition cfg1 :: "(T1, N1) cfg" where
  "cfg1 = CFG rules1 start_symbol1"

definition inp1 :: "(T1, N1) word" where
  "inp1 = [T x, T plus, T x, T plus, T x]"

lemmas cfg1_defs = cfg1_def rules1_def start_symbol1_def

value "Earley\<^sub>L cfg1 inp1"
value "recognizing_code (Earley\<^sub>L cfg1 inp1) cfg1 inp1"
value "build_tree cfg1 inp1 (Earley\<^sub>L cfg1 inp1)"
value "build_trees cfg1 inp1 (Earley\<^sub>L cfg1 inp1)"

lemma wf_\<G>1:
  "wf_\<G> cfg1"
  by (auto simp: wf_\<G>_def cfg1_defs)

lemma is_word_inp1:
  "is_word inp1"
  by (auto simp: is_word_def is_terminal_def cfg1_defs inp1_def)

lemma nonempty_derives1:
  "nonempty_derives cfg1"
  by (auto simp: \<epsilon>_free_def cfg1_defs rule_body_def nonempty_derives_def \<epsilon>_free_impl_non_empty_deriv)

lemma correctness1:
  "recognizing_code (Earley\<^sub>L cfg1 inp1) cfg1 inp1 \<longleftrightarrow> cfg1 \<turnstile> [\<SS> cfg1] \<Rightarrow>\<^sup>* inp1"
  using correctness_Earley\<^sub>L wf_\<G>1 is_word_inp1 nonempty_derives1 recognizing_code_iff_recognizing_Earley\<^sub>L by blast

lemma wf_tree1:
  assumes "build_tree cfg1 inp1 (Earley\<^sub>L cfg1 inp1) = Some t"
  shows "wf_rule_tree cfg1 t \<and> root_tree t = \<SS> cfg1 \<and> yield_tree t = inp1"
  using assms nonempty_derives1 wf_\<G>1 wf_rule_root_yield_tree_build_tree_Earley\<^sub>L by blast

lemma correctness_tree1:
  "(\<exists>t. build_tree cfg1 inp1 (Earley\<^sub>L cfg1 inp1) = Some t) \<longleftrightarrow> cfg1 \<turnstile> [\<SS> cfg1] \<Rightarrow>\<^sup>* inp1"
  using correctness_build_tree_Earley\<^sub>L is_word_inp1 nonempty_derives1 wf_\<G>1 by blast

lemma wf_trees1:
  assumes "build_trees cfg1 inp1 (Earley\<^sub>L cfg1 inp1) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree cfg1 t \<and> root_tree t = \<SS> cfg1 \<and> yield_tree t = inp1"
  using assms nonempty_derives1 wf_\<G>1 wf_rule_root_yield_tree_build_trees_Earley\<^sub>L by blast

lemma soundness_trees1:
  assumes "build_trees cfg1 inp1 (Earley\<^sub>L cfg1 inp1) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "cfg1 \<turnstile> [\<SS> cfg1] \<Rightarrow>\<^sup>* inp1"
  using assms is_word_inp1 nonempty_derives1 soundness_build_trees_Earley\<^sub>L wf_\<G>1 by blast

section \<open>Example 2: Cyclic reduction pointers\<close>

datatype T2 = x
datatype N2 = A | B

definition rules2 :: "(T2, N2) rule list" where
  "rules2 = [
    (NT B, [NT A]),
    (NT A, [NT B]),
    (NT A, [T x])
  ]"

definition start_symbol2 :: "(T2, N2) symbol" where
  "start_symbol2 = NT A"

definition cfg2 :: "(T2, N2) cfg" where
  "cfg2 = CFG rules2 start_symbol2"

definition inp2 :: "(T2, N2) word" where
  "inp2 = [T x]"

lemmas cfg2_defs = cfg2_def rules2_def start_symbol2_def

value "Earley\<^sub>L cfg2 inp2"
value "recognizing_code (Earley\<^sub>L cfg2 inp2) cfg2 inp2"
value "build_tree cfg2 inp2 (Earley\<^sub>L cfg2 inp2)"
value "build_trees cfg2 inp2 (Earley\<^sub>L cfg2 inp2)"

lemma wf_\<G>2:
  "wf_\<G> cfg2"
  by (auto simp: wf_\<G>_def cfg2_defs)

lemma is_word_inp2:
  "is_word inp2"
  by (auto simp: is_word_def is_terminal_def cfg2_defs inp2_def)

lemma nonempty_derives2:
  "nonempty_derives cfg2"
  by (auto simp: \<epsilon>_free_def cfg2_defs rule_body_def nonempty_derives_def \<epsilon>_free_impl_non_empty_deriv)

lemma correctness2:
  "recognizing_code (Earley\<^sub>L cfg2 inp2) cfg2 inp2 \<longleftrightarrow> cfg2 \<turnstile> [\<SS> cfg2] \<Rightarrow>\<^sup>* inp2"
  using correctness_Earley\<^sub>L wf_\<G>2 is_word_inp2 nonempty_derives2 recognizing_code_iff_recognizing_Earley\<^sub>L by blast

lemma wf_tree2:
  assumes "build_tree cfg2 inp2 (Earley\<^sub>L cfg2 inp2) = Some t"
  shows "wf_rule_tree cfg2 t \<and> root_tree t = \<SS> cfg2 \<and> yield_tree t = inp2"
  using assms nonempty_derives2 wf_\<G>2 wf_rule_root_yield_tree_build_tree_Earley\<^sub>L by blast

lemma correctness_tree2:
  "(\<exists>t. build_tree cfg2 inp2 (Earley\<^sub>L cfg2 inp2) = Some t) \<longleftrightarrow> cfg2 \<turnstile> [\<SS> cfg2] \<Rightarrow>\<^sup>* inp2"
  using correctness_build_tree_Earley\<^sub>L is_word_inp2 nonempty_derives2 wf_\<G>2 by blast

lemma wf_trees2:
  assumes "build_trees cfg2 inp2 (Earley\<^sub>L cfg2 inp2) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree cfg2 t \<and> root_tree t = \<SS> cfg2 \<and> yield_tree t = inp2"
  using assms nonempty_derives2 wf_\<G>2 wf_rule_root_yield_tree_build_trees_Earley\<^sub>L by blast

lemma soundness_trees2:
  assumes "build_trees cfg2 inp2 (Earley\<^sub>L cfg2 inp2) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "cfg2 \<turnstile> [\<SS> cfg2] \<Rightarrow>\<^sup>* inp2"
  using assms is_word_inp2 nonempty_derives2 soundness_build_trees_Earley\<^sub>L wf_\<G>2 by blast

section \<open>Example 3: JSON\<close>

text\<open>

json ::= element

value ::= object | array | string | number | "true" | "false" | "null"

object     ::= '{' '}' | '{' ws '}' | '{' members '}'
members    ::= member | member ',' members
member     ::= identifier ':' element
identifier ::= string | ws string | string ws | ws string ws

array    ::= '[' ']' | '[' ws ']' | '[' elements ']'
elements ::= element | element ',' elements
element  ::= value | ws value | value ws | ws value ws

ws       ::= wssymbol | wssymbol ws
wssymbol ::= '0x20' | '0x0A' | '0x0D' | '0x09'

string     ::= '"' '"' | '"' characters '"'
characters ::= character | character characters
character  ::= 0x20 | .. | 0xFF (- '"') (- '\') | '\' escape
escape     ::= '"' | '\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' | 'u' hex hex hex hex
hex        ::= digit | 'A' . 'F' | 'a' . 'f'

number    ::= integer | integer exponent | integer fraction | integer fraction exponent
fraction  ::= '.' digits
exponent  ::= expsymbol digits | expsymbol sign digits
expsymbol ::= 'E' | 'e'
sign      ::= '+' | '-'
integer   ::= digit | onenine digits | '-' digit | '-' onenine digits
digits    ::= digit | digit digits
digit     ::= '0' | onenine
onenine   ::= '1' | .. | '9'

OMITTED:

character ::= '00FF' . '10FFFF'
\<close>

datatype JSON_NT =
  json
  | val
  | object
  | members
  | member
  | identifier
  | array
  | elements
  | element
  | ws
  | wssymbol
  | string
  | characters
  | character
  | escape
  | hex
  | number
  | fraction
  | exponent
  | expsymbol
  | sign
  | integer
  | digits
  | digit
  | onenine

definition JSON_rules :: "(char, JSON_NT) rule list" where
  "JSON_rules = [
    (NT json, [NT element]),
  
    (NT val, [NT object]),
    (NT val, [NT array]),
    (NT val, [NT string]),
    (NT val, [NT number]),
    (NT val, [T CHR ''t'', T CHR ''r'', T CHR ''u'', T CHR ''e'']),
    (NT val, [T CHR ''f'', T CHR ''a'', T CHR ''l'', T CHR ''s'', T CHR ''e'']),
    (NT val, [T CHR ''n'', T CHR ''u'', T CHR ''l'', T CHR ''l'']),

    (NT object, [T CHR ''{'', T CHR ''}'']),
    (NT object, [T CHR ''{'', NT ws, T CHR ''}'']),
    (NT object, [T CHR ''{'', NT members, T CHR ''}'']),

    (NT members, [NT member]),
    (NT members, [NT member, T CHR '','', NT members]),

    (NT member, [NT identifier, T CHR '':'', NT element]),

    (NT identifier, [NT string]),
    (NT identifier, [NT ws, NT string]),
    (NT identifier, [NT string, NT ws]),
    (NT identifier, [NT ws, NT string, NT ws]),

    (NT array, [T CHR ''['', T CHR '']'']),
    (NT array, [T CHR ''['', NT ws, T CHR '']'']),
    (NT array, [T CHR ''['', NT elements, T CHR '']'']),

    (NT elements, [NT element]),
    (NT elements, [NT element, T CHR '','', NT elements]),

    (NT element, [NT val]),
    (NT element, [NT ws, NT val]),
    (NT element, [NT val, NT ws]),
    (NT element, [NT ws, NT val, NT ws]),

    (NT ws, [NT wssymbol]),
    (NT ws, [NT wssymbol, NT ws]),

    (NT wssymbol, [T CHR '' '']),
    (NT wssymbol, [T CHR 0x0A]),
    (NT wssymbol, [T CHR 0x0D]),
    (NT wssymbol, [T CHR 0x09]),

    (NT string, [T CHR 0x22, T CHR 0x22]),
    (NT string, [T CHR 0x22, NT characters, T CHR 0x22]),

    (NT characters, [NT character]),
    (NT characters, [NT character, NT characters]),

    (NT character, [T CHR '' '']),
    (NT character, [T CHR ''!'']),
    (NT character, [T CHR ''#'']),
    (NT character, [T CHR ''$'']),
    (NT character, [T CHR ''%'']),
    (NT character, [T CHR ''&'']),
    (NT character, [T CHR 0x27]),
    (NT character, [T CHR ''('']),
    (NT character, [T CHR '')'']),
    (NT character, [T CHR ''*'']),
    (NT character, [T CHR ''+'']),
    (NT character, [T CHR '','']),
    (NT character, [T CHR ''-'']),
    (NT character, [T CHR ''.'']),
    (NT character, [T CHR ''/'']),
    (NT character, [T CHR ''0'']),
    (NT character, [T CHR ''1'']),
    (NT character, [T CHR ''2'']),
    (NT character, [T CHR ''3'']),
    (NT character, [T CHR ''4'']),
    (NT character, [T CHR ''5'']),
    (NT character, [T CHR ''6'']),
    (NT character, [T CHR ''7'']),
    (NT character, [T CHR ''8'']),
    (NT character, [T CHR ''9'']),
    (NT character, [T CHR '':'']),
    (NT character, [T CHR '';'']),
    (NT character, [T CHR ''<'']),
    (NT character, [T CHR ''='']),
    (NT character, [T CHR ''>'']),
    (NT character, [T CHR ''?'']),
    (NT character, [T CHR ''@'']),
    (NT character, [T CHR ''A'']),
    (NT character, [T CHR ''B'']),
    (NT character, [T CHR ''C'']),
    (NT character, [T CHR ''D'']),
    (NT character, [T CHR ''E'']),
    (NT character, [T CHR ''F'']),
    (NT character, [T CHR ''G'']),
    (NT character, [T CHR ''H'']),
    (NT character, [T CHR ''I'']),
    (NT character, [T CHR ''J'']),
    (NT character, [T CHR ''K'']),
    (NT character, [T CHR ''L'']),
    (NT character, [T CHR ''M'']),
    (NT character, [T CHR ''N'']),
    (NT character, [T CHR ''O'']),
    (NT character, [T CHR ''P'']),
    (NT character, [T CHR ''Q'']),
    (NT character, [T CHR ''R'']),
    (NT character, [T CHR ''S'']),
    (NT character, [T CHR ''T'']),
    (NT character, [T CHR ''U'']),
    (NT character, [T CHR ''V'']),
    (NT character, [T CHR ''W'']),
    (NT character, [T CHR ''X'']),
    (NT character, [T CHR ''Y'']),
    (NT character, [T CHR ''Z'']),
    (NT character, [T CHR ''['']),
    (NT character, [T CHR '']'']),
    (NT character, [T CHR ''^'']),
    (NT character, [T CHR ''_'']),
    (NT character, [T CHR 0x60]),
    (NT character, [T CHR ''a'']),
    (NT character, [T CHR ''b'']),
    (NT character, [T CHR ''c'']),
    (NT character, [T CHR ''d'']),
    (NT character, [T CHR ''e'']),
    (NT character, [T CHR ''f'']),
    (NT character, [T CHR ''g'']),
    (NT character, [T CHR ''h'']),
    (NT character, [T CHR ''i'']),
    (NT character, [T CHR ''j'']),
    (NT character, [T CHR ''k'']),
    (NT character, [T CHR ''l'']),
    (NT character, [T CHR ''m'']),
    (NT character, [T CHR ''n'']),
    (NT character, [T CHR ''o'']),
    (NT character, [T CHR ''p'']),
    (NT character, [T CHR ''q'']),
    (NT character, [T CHR ''r'']),
    (NT character, [T CHR ''s'']),
    (NT character, [T CHR ''t'']),
    (NT character, [T CHR ''u'']),
    (NT character, [T CHR ''v'']),
    (NT character, [T CHR ''w'']),
    (NT character, [T CHR ''x'']),
    (NT character, [T CHR ''y'']),
    (NT character, [T CHR ''z'']),
    (NT character, [T CHR ''{'']),
    (NT character, [T CHR ''|'']),
    (NT character, [T CHR ''}'']),
    (NT character, [T CHR ''~'']),
    (NT character, [T CHR 0x7F]),
    (NT character, [T CHR 0x80]),
    (NT character, [T CHR 0x81]),
    (NT character, [T CHR 0x82]),
    (NT character, [T CHR 0x83]),
    (NT character, [T CHR 0x84]),
    (NT character, [T CHR 0x85]),
    (NT character, [T CHR 0x86]),
    (NT character, [T CHR 0x87]),
    (NT character, [T CHR 0x88]),
    (NT character, [T CHR 0x89]),
    (NT character, [T CHR 0x8A]),
    (NT character, [T CHR 0x8B]),
    (NT character, [T CHR 0x8C]),
    (NT character, [T CHR 0x8D]),
    (NT character, [T CHR 0x8E]),
    (NT character, [T CHR 0x8F]),
    (NT character, [T CHR 0x90]),
    (NT character, [T CHR 0x91]),
    (NT character, [T CHR 0x92]),
    (NT character, [T CHR 0x93]),
    (NT character, [T CHR 0x94]),
    (NT character, [T CHR 0x95]),
    (NT character, [T CHR 0x96]),
    (NT character, [T CHR 0x97]),
    (NT character, [T CHR 0x98]),
    (NT character, [T CHR 0x99]),
    (NT character, [T CHR 0x9A]),
    (NT character, [T CHR 0x9B]),
    (NT character, [T CHR 0x9C]),
    (NT character, [T CHR 0x9D]),
    (NT character, [T CHR 0x9E]),
    (NT character, [T CHR 0x9F]),
    (NT character, [T CHR 0xA0]),
    (NT character, [T CHR 0xA1]),
    (NT character, [T CHR 0xA2]),
    (NT character, [T CHR 0xA3]),
    (NT character, [T CHR 0xA4]),
    (NT character, [T CHR 0xA5]),
    (NT character, [T CHR 0xA6]),
    (NT character, [T CHR 0xA7]),
    (NT character, [T CHR 0xA8]),
    (NT character, [T CHR 0xA9]),
    (NT character, [T CHR 0xAA]),
    (NT character, [T CHR 0xAB]),
    (NT character, [T CHR 0xAC]),
    (NT character, [T CHR 0xAD]),
    (NT character, [T CHR 0xAE]),
    (NT character, [T CHR 0xAF]),
    (NT character, [T CHR 0xB0]),
    (NT character, [T CHR 0xB1]),
    (NT character, [T CHR 0xB2]),
    (NT character, [T CHR 0xB3]),
    (NT character, [T CHR 0xB4]),
    (NT character, [T CHR 0xB5]),
    (NT character, [T CHR 0xB6]),
    (NT character, [T CHR 0xB7]),
    (NT character, [T CHR 0xB8]),
    (NT character, [T CHR 0xB9]),
    (NT character, [T CHR 0xBA]),
    (NT character, [T CHR 0xBB]),
    (NT character, [T CHR 0xBC]),
    (NT character, [T CHR 0xBD]),
    (NT character, [T CHR 0xBE]),
    (NT character, [T CHR 0xBF]),
    (NT character, [T CHR 0xC0]),
    (NT character, [T CHR 0xC1]),
    (NT character, [T CHR 0xC2]),
    (NT character, [T CHR 0xC3]),
    (NT character, [T CHR 0xC4]),
    (NT character, [T CHR 0xC5]),
    (NT character, [T CHR 0xC6]),
    (NT character, [T CHR 0xC7]),
    (NT character, [T CHR 0xC8]),
    (NT character, [T CHR 0xC9]),
    (NT character, [T CHR 0xCA]),
    (NT character, [T CHR 0xCB]),
    (NT character, [T CHR 0xCC]),
    (NT character, [T CHR 0xCD]),
    (NT character, [T CHR 0xCE]),
    (NT character, [T CHR 0xCF]),
    (NT character, [T CHR 0xD0]),
    (NT character, [T CHR 0xD1]),
    (NT character, [T CHR 0xD2]),
    (NT character, [T CHR 0xD3]),
    (NT character, [T CHR 0xD4]),
    (NT character, [T CHR 0xD5]),
    (NT character, [T CHR 0xD6]),
    (NT character, [T CHR 0xD7]),
    (NT character, [T CHR 0xD8]),
    (NT character, [T CHR 0xD9]),
    (NT character, [T CHR 0xDA]),
    (NT character, [T CHR 0xDB]),
    (NT character, [T CHR 0xDC]),
    (NT character, [T CHR 0xDD]),
    (NT character, [T CHR 0xDE]),
    (NT character, [T CHR 0xDF]),
    (NT character, [T CHR 0xE0]),
    (NT character, [T CHR 0xE1]),
    (NT character, [T CHR 0xE2]),
    (NT character, [T CHR 0xE3]),
    (NT character, [T CHR 0xE4]),
    (NT character, [T CHR 0xE5]),
    (NT character, [T CHR 0xE6]),
    (NT character, [T CHR 0xE7]),
    (NT character, [T CHR 0xE8]),
    (NT character, [T CHR 0xE9]),
    (NT character, [T CHR 0xEA]),
    (NT character, [T CHR 0xEB]),
    (NT character, [T CHR 0xEC]),
    (NT character, [T CHR 0xED]),
    (NT character, [T CHR 0xEE]),
    (NT character, [T CHR 0xEF]),
    (NT character, [T CHR 0xF0]),
    (NT character, [T CHR 0xF1]),
    (NT character, [T CHR 0xF2]),
    (NT character, [T CHR 0xF3]),
    (NT character, [T CHR 0xF4]),
    (NT character, [T CHR 0xF5]),
    (NT character, [T CHR 0xF6]),
    (NT character, [T CHR 0xF7]),
    (NT character, [T CHR 0xF8]),
    (NT character, [T CHR 0xF9]),
    (NT character, [T CHR 0xFA]),
    (NT character, [T CHR 0xFB]),
    (NT character, [T CHR 0xFC]),
    (NT character, [T CHR 0xFD]),
    (NT character, [T CHR 0xFE]),
    (NT character, [T CHR 0xFF]),
    (NT character, [T CHR 0x5C, NT escape]),

    (NT escape, [T CHR 0x22]),
    (NT escape, [T CHR 0x5C]),
    (NT escape, [T CHR ''/'']),
    (NT escape, [T CHR ''b'']),
    (NT escape, [T CHR ''f'']),
    (NT escape, [T CHR ''n'']),
    (NT escape, [T CHR ''r'']),
    (NT escape, [T CHR ''t'']),
    (NT escape, [T CHR ''u'', NT hex, NT hex, NT hex, NT hex]),

    (NT hex, [NT digit]),
    (NT hex, [T CHR ''A'']),
    (NT hex, [T CHR ''B'']),
    (NT hex, [T CHR ''C'']),
    (NT hex, [T CHR ''D'']),
    (NT hex, [T CHR ''E'']),
    (NT hex, [T CHR ''F'']),
    (NT hex, [T CHR ''a'']),
    (NT hex, [T CHR ''b'']),
    (NT hex, [T CHR ''c'']),
    (NT hex, [T CHR ''d'']),
    (NT hex, [T CHR ''e'']),
    (NT hex, [T CHR ''f'']),

    (NT number, [NT integer]),
    (NT number, [NT integer, NT exponent]),
    (NT number, [NT integer, NT fraction]),
    (NT number, [NT integer, NT fraction, NT exponent]),

    (NT fraction, [T CHR ''.'', NT digits]),

    (NT exponent, [NT expsymbol, NT digits]),
    (NT exponent, [NT expsymbol, NT sign, NT digits]),
  
    (NT expsymbol, [T CHR ''E'']),
    (NT expsymbol, [T CHR ''e'']),

    (NT sign, [T CHR ''+'']),
    (NT sign, [T CHR ''-'']),

    (NT integer, [NT digit]),
    (NT integer, [NT onenine, NT digits]),
    (NT integer, [T CHR ''-'', NT digit]),
    (NT integer, [T CHR ''-'', NT onenine, NT digits]),

    (NT digits, [NT digit]),
    (NT digits, [NT digit, NT digits]),

    (NT digit, [T CHR ''0'']),
    (NT digit, [NT onenine]),

    (NT onenine, [T CHR ''1'']),
    (NT onenine, [T CHR ''2'']),
    (NT onenine, [T CHR ''3'']),
    (NT onenine, [T CHR ''4'']),
    (NT onenine, [T CHR ''5'']),
    (NT onenine, [T CHR ''6'']),
    (NT onenine, [T CHR ''7'']),
    (NT onenine, [T CHR ''8'']),
    (NT onenine, [T CHR ''9''])
  ]"

definition JSON_start_symbol :: "(char, JSON_NT) symbol" where
  "JSON_start_symbol = NT json"

definition JSON_cfg :: "(char, JSON_NT) cfg" where
  "JSON_cfg = CFG JSON_rules JSON_start_symbol"

lemmas JSON_cfg_defs = JSON_cfg_def JSON_rules_def JSON_start_symbol_def

lemma wf_\<G>_JSON:
  "wf_\<G> JSON_cfg"
  by (auto simp: wf_\<G>_def JSON_cfg_defs)

lemma nonempty_derives_JSON_cfg:
  "nonempty_derives JSON_cfg"
  by (auto simp: \<epsilon>_free_def JSON_cfg_defs rule_body_def nonempty_derives_def \<epsilon>_free_impl_non_empty_deriv)

definition size_bins :: "('a, 'b) bins \<Rightarrow> nat" where
  "size_bins bs = fold (+) (map length bs) 0"

definition JSON_inp1 :: "(char, JSON_NT) word" where
  \<open>JSON_inp1 = map T ''
{
    "glossary": {
        "title": "example glossary",
		"GlossDiv": {
            "title": "S",
			"GlossList": {
                "GlossEntry": {
                    "ID": "SGML",
					"SortAs": "SGML",
					"GlossTerm": "Standard Generalized Markup Language",
					"Acronym": "SGML",
					"Abbrev": "ISO 8879:1986",
					"GlossDef": {
                        "para": "A meta-markup language, used to create markup languages such as DocBook.",
						"GlossSeeAlso": ["GML", "XML"]
                    },
					"GlossSee": "markup"
                }
            }
        }
    }
}
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp1)" \<comment>\<open>77921\<close>
value "recognizing_code (Earley\<^sub>L JSON_cfg JSON_inp1) JSON_cfg JSON_inp1"
value "build_tree JSON_cfg JSON_inp1 (Earley\<^sub>L JSON_cfg JSON_inp1)"
value "build_trees JSON_cfg JSON_inp1 (Earley\<^sub>L JSON_cfg JSON_inp1)"

definition JSON_inp2 :: "(char, JSON_NT) word" where
  \<open>JSON_inp2 = map T ''
{"menu": {
  "id": "file",
  "value": "File",
  "popup": {
    "menuitem": [
      {"value": "New", "onclick": "CreateNewDoc()"},
      {"value": "Open", "onclick": "OpenDoc()"},
      {"value": "Close", "onclick": "CloseDoc()"}
    ]
  }
}}
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp2)" \<comment>\<open>33720\<close>
value "recognizing_code (Earley\<^sub>L JSON_cfg JSON_inp2) JSON_cfg JSON_inp2"
value "build_tree JSON_cfg JSON_inp2 (Earley\<^sub>L JSON_cfg JSON_inp2)"
value "build_trees JSON_cfg JSON_inp2 (Earley\<^sub>L JSON_cfg JSON_inp2)"

definition JSON_inp3 :: "(char, JSON_NT) word" where
  \<open>JSON_inp3 = map T ''
{"widget": {
    "debug": "on",
    "window": {
        "title": "Sample Konfabulator Widget",
        "name": "main_window",
        "width": 500,
        "height": 500
    },
    "image": { 
        "src": "Images/Sun.png",
        "name": "sun1",
        "hOffset": 250,
        "vOffset": 250,
        "alignment": "center"
    },
    "text": {
        "data": "Click Here",
        "size": 36,
        "style": "bold",
        "name": "text1",
        "hOffset": 250,
        "vOffset": 100,
        "alignment": "center",
        "onMouseUp": "sun1.opacity = (sun1.opacity / 100) * 90;"
    }
}}  
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp3)" \<comment>\<open>74472\<close>
value "recognizing_code (Earley\<^sub>L JSON_cfg JSON_inp3) JSON_cfg JSON_inp3"
value "build_tree JSON_cfg JSON_inp3 (Earley\<^sub>L JSON_cfg JSON_inp3)"
value "build_trees JSON_cfg JSON_inp3 (Earley\<^sub>L JSON_cfg JSON_inp3)"

definition JSON_inp4 :: "(char, JSON_NT) word" where
  \<open>JSON_inp4 = map T ''
{"web-app": {
  "servlet": [   
    {
      "servlet-name": "cofaxCDS",
      "servlet-class": "org.cofax.cds.CDSServlet",
      "init-param": {
        "configGlossary:installationAt": "Philadelphia, PA",
        "configGlossary:adminEmail": "ksm@pobox.com",
        "configGlossary:poweredBy": "Cofax",
        "configGlossary:poweredByIcon": "/images/cofax.gif",
        "configGlossary:staticPath": "/content/static",
        "templateProcessorClass": "org.cofax.WysiwygTemplate",
        "templateLoaderClass": "org.cofax.FilesTemplateLoader",
        "templatePath": "templates",
        "templateOverridePath": "",
        "defaultListTemplate": "listTemplate.htm",
        "defaultFileTemplate": "articleTemplate.htm",
        "useJSP": false,
        "jspListTemplate": "listTemplate.jsp",
        "jspFileTemplate": "articleTemplate.jsp",
        "cachePackageTagsTrack": 200,
        "cachePackageTagsStore": 200,
        "cachePackageTagsRefresh": 60,
        "cacheTemplatesTrack": 100,
        "cacheTemplatesStore": 50,
        "cacheTemplatesRefresh": 15,
        "cachePagesTrack": 200,
        "cachePagesStore": 100,
        "cachePagesRefresh": 10,
        "cachePagesDirtyRead": 10,
        "searchEngineListTemplate": "forSearchEnginesList.htm",
        "searchEngineFileTemplate": "forSearchEngines.htm",
        "searchEngineRobotsDb": "WEB-INF/robots.db",
        "useDataStore": true,
        "dataStoreClass": "org.cofax.SqlDataStore",
        "redirectionClass": "org.cofax.SqlRedirection",
        "dataStoreName": "cofax",
        "dataStoreDriver": "com.microsoft.jdbc.sqlserver.SQLServerDriver",
        "dataStoreUrl": "jdbc:microsoft:sqlserver://LOCALHOST:1433;DatabaseName=goon",
        "dataStoreUser": "sa",
        "dataStorePassword": "dataStoreTestQuery",
        "dataStoreTestQuery": "SET NOCOUNT ON;select test='test';",
        "dataStoreLogFile": "/usr/local/tomcat/logs/datastore.log",
        "dataStoreInitConns": 10,
        "dataStoreMaxConns": 100,
        "dataStoreConnUsageLimit": 100,
        "dataStoreLogLevel": "debug",
        "maxUrlLength": 500}},
    {
      "servlet-name": "cofaxEmail",
      "servlet-class": "org.cofax.cds.EmailServlet",
      "init-param": {
      "mailHost": "mail1",
      "mailHostOverride": "mail2"}},
    {
      "servlet-name": "cofaxAdmin",
      "servlet-class": "org.cofax.cds.AdminServlet"},
 
    {
      "servlet-name": "fileServlet",
      "servlet-class": "org.cofax.cds.FileServlet"},
    {
      "servlet-name": "cofaxTools",
      "servlet-class": "org.cofax.cms.CofaxToolsServlet",
      "init-param": {
        "templatePath": "toolstemplates/",
        "log": 1,
        "logLocation": "/usr/local/tomcat/logs/CofaxTools.log",
        "logMaxSize": "",
        "dataLog": 1,
        "dataLogLocation": "/usr/local/tomcat/logs/dataLog.log",
        "dataLogMaxSize": "",
        "removePageCache": "/content/admin/remove?cache=pages&id=",
        "removeTemplateCache": "/content/admin/remove?cache=templates&id=",
        "fileTransferFolder": "/usr/local/tomcat/webapps/content/fileTransferFolder",
        "lookInContext": 1,
        "adminGroupID": 4,
        "betaServer": true}}],
  "servlet-mapping": {
    "cofaxCDS": "/",
    "cofaxEmail": "/cofaxutil/aemail/*",
    "cofaxAdmin": "/admin/*",
    "fileServlet": "/static/*",
    "cofaxTools": "/tools/*"},
 
  "taglib": {
    "taglib-uri": "cofax.tld",
    "taglib-location": "/WEB-INF/tlds/cofax.tld"}}}
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp4)" \<comment>\<open>585597\<close>
value "recognizing_code (Earley\<^sub>L JSON_cfg JSON_inp4) JSON_cfg JSON_inp4"
value "build_tree JSON_cfg JSON_inp4 (Earley\<^sub>L JSON_cfg JSON_inp4)"
value "build_trees JSON_cfg JSON_inp4 (Earley\<^sub>L JSON_cfg JSON_inp4)"


definition JSON_inp5 :: "(char, JSON_NT) word" where
  \<open>JSON_inp5 = map T ''
{"menu": {
    "header": "SVG Viewer",
    "items": [
        {"id": "Open"},
        {"id": "OpenNew", "label": "Open New"},
        null,
        {"id": "ZoomIn", "label": "Zoom In"},
        {"id": "ZoomOut", "label": "Zoom Out"},
        {"id": "OriginalView", "label": "Original View"},
        null,
        {"id": "Quality"},
        {"id": "Pause"},
        {"id": "Mute"},
        null,
        {"id": "Find", "label": "Find..."},
        {"id": "FindAgain", "label": "Find Again"},
        {"id": "Copy"},
        {"id": "CopyAgain", "label": "Copy Again"},
        {"id": "CopySVG", "label": "Copy SVG"},
        {"id": "ViewSVG", "label": "View SVG"},
        {"id": "ViewSource", "label": "View Source"},
        {"id": "SaveAs", "label": "Save As"},
        null,
        {"id": "Help"},
        {"id": "About", "label": "About Adobe CVG Viewer..."}
    ]
}}
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp5)" \<comment>\<open>114506\<close>
value "recognizing_code (Earley\<^sub>L JSON_cfg JSON_inp5) JSON_cfg JSON_inp5"
value "build_tree JSON_cfg JSON_inp5 (Earley\<^sub>L JSON_cfg JSON_inp5)"
value "build_trees JSON_cfg JSON_inp5 (Earley\<^sub>L JSON_cfg JSON_inp5)"

end
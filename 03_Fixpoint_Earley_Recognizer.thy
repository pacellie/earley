(*<*)
theory "03_Fixpoint_Earley_Recognizer"
  imports
    "02_Earleys_Algorithm"
    "HOL-Library.LaTeXsugar"
begin
(*>*)

chapter\<open>Earley Formalization\<close>

section\<open>Auxiliary Definitions\<close>

fun slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slice _ _ [] = []"
| "slice _ 0 (x#xs) = []"
| "slice 0 (Suc b) (x#xs) = x # slice 0 b xs"
| "slice (Suc a) (Suc b) (x#xs) = slice a b xs"

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

definition item_rule_body :: "'a item \<Rightarrow> 'a sentence" where
  "item_rule_body x = rule_body (item_rule x)"

definition item_\<alpha> :: "'a item \<Rightarrow> 'a sentence" where
  "item_\<alpha> x = take (item_dot x) (item_rule_body x)"

definition item_\<beta> :: "'a item \<Rightarrow> 'a sentence" where 
  "item_\<beta> x = drop (item_dot x) (item_rule_body x)"

definition init_item :: "'a rule \<Rightarrow> nat \<Rightarrow> 'a item" where
  "init_item r k = Item r 0 k k"

definition is_complete :: "'a item \<Rightarrow> bool" where
  "is_complete x = (item_dot x \<ge> length (item_rule_body x))"

definition next_symbol :: "'a item \<Rightarrow> 'a option" where
  "next_symbol x = (if is_complete x then None else Some ((item_rule_body x) ! (item_dot x)))"

definition inc_item :: "'a item \<Rightarrow> nat \<Rightarrow> 'a item" where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

definition bin :: "'a items \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"

definition wf_item :: "'a cfg \<Rightarrow> 'a sentence => 'a item \<Rightarrow> bool" where 
  "wf_item cfg inp x = (
    item_rule x \<in> set (\<RR> cfg) \<and> 
    item_dot x \<le> length (item_rule_body x) \<and>
    item_origin x \<le> item_end x \<and> 
    item_end x \<le> length inp)"

definition wf_items :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> bool" where
  "wf_items cfg inp I = (\<forall>x \<in> I. wf_item cfg inp x)"

definition is_finished :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item \<Rightarrow> bool" where
  "is_finished cfg inp x \<longleftrightarrow> (
    item_rule_head x = \<SS> cfg \<and>
    item_origin x = 0 \<and>
    item_end x = length inp \<and> 
    is_complete x)"

definition earley_recognized :: "'a items \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "earley_recognized I cfg inp = (\<exists>x \<in> I. is_finished cfg inp x)"

section \<open>Main Definitions\<close>

fun funpower :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "funpower f 0 x = x"
| "funpower f (Suc n) x = f (funpower f n x)"

definition natUnion :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "natUnion f = \<Union> { f n | n. True }"

definition limit  :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit f x = natUnion (\<lambda> n. funpower f n x)"

definition Init :: "'a cfg \<Rightarrow> 'a items" where
  "Init cfg = { init_item r 0 | r. r \<in> set (\<RR> cfg) \<and> fst r = (\<SS> cfg) }"

definition Scan :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
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

definition \<pi>_step :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "\<pi>_step k cfg inp I = I \<union> Scan k inp I \<union> Complete k I \<union> Predict k cfg I"

definition \<pi> :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> 'a items" where
  "\<pi> k cfg inp I = limit (\<pi>_step k cfg inp) I"

fun \<I> :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items" where
  "\<I> 0 cfg inp = \<pi> 0 cfg inp (Init cfg)"
| "\<I> (Suc n) cfg inp = \<pi> (Suc n) cfg inp (\<I> n cfg inp)"

definition \<II> :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items" where
  "\<II> cfg inp = \<I> (length inp) cfg inp"

section \<open>Wellformedness\<close>

lemma wf_Init:
  "x \<in> Init cfg \<Longrightarrow> wf_item cfg inp x"
(*<*)
  sorry
(*>*)

lemma wf_Scan:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (Scan k inp I)"
(*<*)
  sorry
(*>*)

lemma wf_Predict:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (Predict k cfg I)"
(*<*)
  sorry
(*>*)

lemma wf_Complete:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (Complete k I)"
(*<*)
  sorry
(*>*)

lemma wf_\<pi>_step:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (\<pi>_step k cfg inp I)"
(*<*)
  sorry
(*>*)

lemma wf_funpower:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (funpower (\<pi>_step k cfg inp) n I)"
(*<*)
  sorry
(*>*)

lemma wf_\<pi>:
  "wf_items cfg inp I \<Longrightarrow> wf_items cfg inp (\<pi> k cfg inp I)"
(*<*)
  sorry
(*>*)

lemma wf_\<pi>0:
  "wf_items cfg inp (\<pi> 0 cfg inp (Init cfg))"
(*<*)
  sorry
(*>*)

lemma wf_\<I>:
  "wf_items cfg inp (\<I> n cfg inp)"
(*<*)
  sorry
(*>*)

lemma wf_\<II>:
  "wf_items cfg inp (\<II> cfg inp)"
(*<*)
  sorry
(*>*)

section \<open>Soundness\<close>

definition sound_item :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item \<Rightarrow> bool" where
  "sound_item cfg inp x = derives cfg [item_rule_head x] (slice (item_origin x) (item_end x) inp @ item_\<beta> x)"

definition sound_items :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> bool" where
  "sound_items cfg inp I = (\<forall>x \<in> I. sound_item cfg inp x)"

lemma sound_Init:
  "sound_items cfg inp (Init cfg)"
(*<*)
  sorry
(*>*)

lemma sound_item_inc_item:
  assumes "wf_item cfg inp x" "sound_item cfg inp x"
  assumes "next_symbol x = Some a"
  assumes "k < length inp" "inp!k = a" "item_end x = k"
  shows "sound_item cfg inp (inc_item x (k+1))"
(*<*)
  sorry
(*>*)

lemma sound_Scan:
  "wf_items cfg inp I \<Longrightarrow> sound_items cfg inp I \<Longrightarrow> sound_items cfg inp (Scan k inp I)"
(*<*)
  sorry
(*>*)

lemma sound_Predict:
  "sound_items cfg inp I \<Longrightarrow> sound_items cfg inp (Predict k cfg I)"
(*<*)
  sorry
(*>*)

lemma sound_Complete:
  assumes "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (Complete k I)"
(*<*)
  sorry
(*>*)

lemma sound_\<pi>_step:
  "wf_items cfg inp I \<Longrightarrow> sound_items cfg inp I \<Longrightarrow> sound_items cfg inp (\<pi>_step k cfg inp I)"
(*<*)
  sorry
(*>*)

lemma sound_funpower:
  "wf_items cfg inp I \<Longrightarrow> sound_items cfg inp I \<Longrightarrow> sound_items cfg inp (funpower (\<pi>_step k cfg inp) n I)"
(*<*)
  sorry
(*>*)

lemma sound_\<pi>:
  assumes "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (\<pi> k cfg inp I)"
(*<*)
  sorry
(*>*)

lemma sound_\<pi>0:
  "sound_items cfg inp (\<pi> 0 cfg inp (Init cfg))"
(*<*)
  sorry
(*>*)

lemma sound_\<I>:
  "sound_items cfg inp (\<I> k cfg inp)"
(*<*)
  sorry
(*>*)

lemma sound_\<II>:
  "sound_items cfg inp (\<II> cfg inp)"
(*<*)
  sorry
(*>*)

theorem soundness:
  "earley_recognized (\<II> cfg inp) cfg inp \<Longrightarrow> derives cfg [\<SS> cfg] inp"
(*<*)
  sorry
(*>*)

section \<open>Monotonicity and Absorption\<close>

lemma \<pi>_idem:
  "\<pi> k cfg inp (\<pi> k cfg inp I) = \<pi> k cfg inp I"
(*<*)
  sorry
(*>*)


lemma Scan_bin_absorb:
  "Scan k inp (bin I k) = Scan k inp I"
(*<*)
  sorry
(*>*)

lemma Predict_bin_absorb:
  "Predict k cfg (bin I k) = Predict k cfg I"
(*<*)
  sorry
(*>*)

lemma Complete_bin_absorb:
  "Complete k (bin I k) \<subseteq> Complete k I"
(*<*)
  sorry
(*>*)

lemma Scan_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Scan k inp I \<subseteq> Scan k inp J"
(*<*)
  sorry
(*>*)

lemma Predict_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Predict k cfg I \<subseteq> Predict k cfg J"
(*<*)
  sorry
(*>*)

lemma Complete_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Complete k I \<subseteq> Complete k J"
(*<*)
  sorry
(*>*)

lemma \<pi>_step_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi>_step k cfg inp I \<subseteq> \<pi>_step k cfg inp J"
(*<*)
  sorry
(*>*)

lemma funpower_sub_mono:
  "I \<subseteq> J \<Longrightarrow> funpower (\<pi>_step k cfg inp) n I \<subseteq> funpower (\<pi>_step k cfg inp) n J"
(*<*)
  sorry
(*>*)

lemma \<pi>_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi> k cfg inp I \<subseteq> \<pi> k cfg inp J"
(*<*)
  sorry
(*>*)

lemma Scan_\<pi>_step_mono:
  "Scan k inp I \<subseteq> \<pi>_step k cfg inp I"
(*<*)
  sorry
(*>*)

lemma Predict_\<pi>_step_mono:
  "Predict k cfg I \<subseteq> \<pi>_step k cfg inp I"
(*<*)
  sorry
(*>*)

lemma Complete_\<pi>_step_mono:
  "Complete k I \<subseteq> \<pi>_step k cfg inp I"
(*<*)
  sorry
(*>*)

lemma \<pi>_step_\<pi>_mono:
  "\<pi>_step k cfg inp I \<subseteq> \<pi> k cfg inp I"
(*<*)
  sorry
(*>*)

lemma Scan_\<pi>_mono:
  "Scan k inp I \<subseteq> \<pi> k cfg inp I"
(*<*)
  sorry
(*>*)

lemma Predict_\<pi>_mono:
  "Predict k cfg I \<subseteq> \<pi> k cfg inp I"
(*<*)
  sorry
(*>*)

lemma Complete_\<pi>_mono:
  "Complete k I \<subseteq> \<pi> k cfg inp I"
(*<*)
  sorry
(*>*)

lemma \<pi>_mono:
  "I \<subseteq> \<pi> k cfg inp I"
(*<*)
  sorry
(*>*)

lemma Scan_bin_empty:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Scan k inp I) i = {}"
(*<*)
  sorry
(*>*)

lemma Predict_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Predict k cfg I) i = {}"
(*<*)
  sorry
(*>*)

lemma Complete_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Complete k I) i = {}"
(*<*)
  sorry
(*>*)

lemma \<pi>_step_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k + 1 \<Longrightarrow> bin (\<pi>_step k cfg inp I) i = bin I i"
(*<*)
  sorry
(*>*)

lemma funpower_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (funpower (\<pi>_step k cfg inp) n I) i = bin I i"
(*<*)
  sorry
(*>*)

lemma \<pi>_bin_absorb:
  assumes "i \<noteq> k" "i \<noteq> k+1" 
  shows "bin (\<pi> k cfg inp I) i = bin I i"
(*<*)
  sorry
(*>*)

section \<open>Completeness\<close>

lemma Scan_\<I>:
  assumes "i+1 \<le> k" "k \<le> length inp" "x \<in> bin (\<I> k cfg inp) i"
  assumes "next_symbol x = Some a" "inp!i = a"
  shows "inc_item x (i+1) \<in> \<I> k cfg inp"
(*<*)
  sorry
(*>*)

lemma Predict_\<I>:
  assumes "i \<le> k" "x \<in> bin (\<I> k cfg inp) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set (\<RR> cfg)"
  shows "init_item (N,\<alpha>) i \<in> \<I> k cfg inp"
(*<*)
  sorry
(*>*)

lemma Complete_\<I>:
  assumes "i \<le> j" "j \<le> k" "x \<in> bin (\<I> k cfg inp) i" "next_symbol x = Some N" "(N,\<alpha>) \<in> set (\<RR> cfg)"
  assumes "i = item_origin y" "y \<in> bin (\<I> k cfg inp) j" "item_rule y = (N,\<alpha>)" "is_complete y"
  shows "inc_item x j \<in> \<I> k cfg inp"
(*<*)
  sorry
(*>*)

type_synonym 'a derivation = "(nat \<times> 'a rule) list"

definition Derives1 :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a rule \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "Derives1 cfg u i r v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> (N, \<alpha>) \<in> set (\<RR> cfg)
        \<and> r = (N, \<alpha>) \<and> i = length x)"

fun Derivation :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a derivation \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "Derivation _ a [] b = (a = b)"
| "Derivation cfg a (d#D) b = (\<exists> x. Derives1 cfg a (fst d) (snd d) x \<and> Derivation cfg x D b)"

definition partially_completed :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a items \<Rightarrow> ('a derivation \<Rightarrow> bool) \<Rightarrow> bool" where
  "partially_completed k cfg inp I P = (
    \<forall>i j x a D.
      i \<le> j \<and> j \<le> k \<and> k \<le> length inp \<and>
      x \<in> bin I i \<and> next_symbol x = Some a \<and>
      Derivation cfg [a] D (slice i j inp) \<and> P D \<longrightarrow>
      inc_item x j \<in> I
  )"

lemma fully_completed:
  assumes "j \<le> k" "k \<le> length inp"
  assumes "x = Item (N,\<alpha>) d i j" "x \<in> I" "wf_items cfg inp I"
  assumes "Derivation cfg (item_\<beta> x) D (slice j k inp)"
  assumes "partially_completed k cfg inp I (\<lambda>D'. length D' \<le> length D)"
  shows "Item (N,\<alpha>) (length \<alpha>) i k \<in> I"
(*<*)
  sorry
(*>*)

lemma partially_completed_\<I>:
  assumes "wf_cfg cfg"
  shows "partially_completed k cfg inp (\<I> k cfg inp) (\<lambda>_. True)"
(*<*)
  sorry
(*>*)

lemma partially_completed_\<II>:
  "wf_cfg cfg \<Longrightarrow> partially_completed (length inp) cfg inp (\<II> cfg inp) (\<lambda>_. True)"
(*<*)
  sorry
(*>*)

lemma Derivation_\<SS>1:
  assumes "Derivation cfg [\<SS> cfg] D inp" "is_word cfg inp" "wf_cfg cfg"
  shows "\<exists>\<alpha> E. Derivation cfg \<alpha> E inp \<and> (\<SS> cfg,\<alpha>) \<in> set (\<RR> cfg)"
(*<*)
  sorry
(*>*)

theorem completeness:
  assumes "derives cfg [\<SS> cfg] inp" "is_word cfg inp" "wf_cfg cfg"
  shows "earley_recognized (\<II> cfg inp) cfg inp"
(*<*)
  sorry
(*>*)

corollary
  assumes "wf_cfg cfg" "is_word cfg inp"
  shows "earley_recognized (\<II> cfg inp) cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
(*<*)
  sorry
(*>*)

(*<*)
end
(*>*)
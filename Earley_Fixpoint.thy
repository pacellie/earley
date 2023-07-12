theory Earley_Fixpoint
  imports
    Earley
    Derivations
    Limit
begin

section \<open>Earley recognizer\<close>

subsection \<open>Earley Fixpoint\<close>

definition init_item :: "'a rule \<Rightarrow> nat \<Rightarrow> 'a item" where
  "init_item r k = Item r 0 k k"

definition inc_item :: "'a item \<Rightarrow> nat \<Rightarrow> 'a item" where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

definition bin :: "'a item set \<Rightarrow> nat \<Rightarrow> 'a item set" where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"

definition Init :: "'a cfg \<Rightarrow> 'a item set" where
  "Init cfg = { init_item r 0 | r. r \<in> set (\<RR> cfg) \<and> fst r = (\<SS> cfg) }"

definition Scan :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "Scan k inp I =
    { inc_item x (k+1) | x a.
        x \<in> bin I k \<and>
        inp!k = a \<and>
        k < length inp \<and>
        next_symbol x = Some a }"

definition Predict :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "Predict k cfg I =
    { init_item r k | r x.
        r \<in> set (\<RR> cfg) \<and>
        x \<in> bin I k \<and>
        next_symbol x = Some (rule_head r) }"

definition Complete :: "nat \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "Complete k I =
    { inc_item x k | x y.
        x \<in> bin I (item_origin y) \<and>
        y \<in> bin I k \<and>
        is_complete y \<and>
        next_symbol x = Some (item_rule_head y) }"

definition \<pi>_step :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "\<pi>_step k cfg inp I = I \<union> Scan k inp I \<union> Complete k I \<union> Predict k cfg I"

definition \<pi> :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "\<pi> k cfg inp I = limit (\<pi>_step k cfg inp) I"

fun \<I> :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set" where
  "\<I> 0 cfg inp = \<pi> 0 cfg inp (Init cfg)"
| "\<I> (Suc n) cfg inp = \<pi> (Suc n) cfg inp (\<I> n cfg inp)"

definition \<II> :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set" where
  "\<II> cfg inp = \<I> (length inp) cfg inp"


subsection \<open>Monotonicity and Absorption\<close>

lemma \<pi>_step_empty:
  "\<pi>_step k cfg inp {} = {}"
  unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast

lemma \<pi>_step_setmonotone:
  "setmonotone (\<pi>_step k cfg inp)"
  by (simp add: Un_assoc \<pi>_step_def setmonotone_def)

lemma \<pi>_step_continuous:
  "continuous (\<pi>_step k cfg inp)"
  unfolding continuous_def
proof (standard, standard, standard)
  fix C :: "nat \<Rightarrow> 'a item set"
  assume "chain C"
  thus "chain (\<pi>_step k cfg inp \<circ> C)"
    unfolding chain_def \<pi>_step_def by (auto simp: Scan_def Predict_def Complete_def bin_def subset_eq)
next
  fix C :: "nat \<Rightarrow> 'a item set"
  assume *: "chain C"
  show "\<pi>_step k cfg inp (natUnion C) = natUnion (\<pi>_step k cfg inp \<circ> C)"
    unfolding natUnion_def
  proof standard
    show "\<pi>_step k cfg inp (\<Union> {C n |n. True}) \<subseteq> \<Union> {(\<pi>_step k cfg inp \<circ> C) n |n. True}"
    proof standard
      fix x
      assume #: "x \<in> \<pi>_step k cfg inp (\<Union> {C n |n. True})"
      show "x \<in> \<Union> {(\<pi>_step k cfg inp \<circ> C) n |n. True}"
      proof (cases "x \<in> Complete k (\<Union> {C n |n. True})")
        case True
        then show ?thesis
          using * unfolding chain_def
          apply (auto simp: \<pi>_step_def Complete_def bin_def)
        proof -
          fix y :: "'a item" and z :: "'a item" and n :: nat and m :: nat
          assume a1: "is_complete z"
          assume a2: "item_end y = item_origin z"
          assume a3: "y \<in> C n"
          assume a4: "z \<in> C m"
          assume a5: "next_symbol y = Some (item_rule_head z)"
          assume "\<forall>i. C i \<subseteq> C (Suc i)"
          hence f6: "\<And>n m. \<not> n \<le> m \<or> C n \<subseteq> C m"
            by (meson lift_Suc_mono_le)
          hence f7: "\<And>n. \<not> m \<le> n \<or> z \<in> C n"
            using a4 by blast
          have "\<exists>n \<ge> m. y \<in> C n"
            using f6 a3 by (meson le_sup_iff subset_eq sup_ge1)
          thus "\<exists>I.
                  (\<exists>n. I = C n \<union>
                           Scan (item_end z) inp (C n) \<union>
                           {inc_item i (item_end z) |i.
                              i \<in> C n \<and>
                              (\<exists>j.
                                item_end i = item_origin j \<and>
                                j \<in> C n \<and>
                                item_end j = item_end z \<and>
                                is_complete j \<and>
                                next_symbol i = Some (item_rule_head j))} \<union>
                           Predict (item_end z) cfg (C n))
                  \<and> inc_item y (item_end z) \<in> I"
            using f7 a5 a2 a1 by blast
        qed
      next
        case False
        thus ?thesis
          using # Un_iff by (auto simp: \<pi>_step_def Scan_def Predict_def bin_def; blast)
      qed
    qed
  next
    show "\<Union> {(\<pi>_step k cfg inp \<circ> C) n |n. True} \<subseteq> \<pi>_step k cfg inp (\<Union> {C n |n. True})"
      unfolding \<pi>_step_def
      using * by (auto simp: Scan_def Predict_def Complete_def chain_def bin_def, metis+)
  qed
qed

lemma \<pi>_step_regular:
  "regular (\<pi>_step k cfg inp)"
  by (simp add: \<pi>_step_continuous \<pi>_step_setmonotone regular_def)

lemma \<pi>_idem:
  "\<pi> k cfg inp (\<pi> k cfg inp I) = \<pi> k cfg inp I"
  by (simp add: \<pi>_def \<pi>_step_regular limit_is_idempotent)

lemma Scan_bin_absorb:
  "Scan k inp (bin I k) = Scan k inp I"
  unfolding Scan_def bin_def by simp

lemma Predict_bin_absorb:
  "Predict k cfg (bin I k) = Predict k cfg I"
  unfolding Predict_def bin_def by simp

lemma Complete_bin_absorb:
  "Complete k (bin I k) \<subseteq> Complete k I"
  unfolding Complete_def bin_def by blast

lemma Scan_Un:
  "Scan k inp (I \<union> J) = Scan k inp I \<union> Scan k inp J"
  unfolding Scan_def bin_def by blast

lemma Predict_Un:
  "Predict k cfg (I \<union> J) = Predict k cfg I \<union> Predict k cfg J"
  unfolding Predict_def bin_def by blast

lemma Scan_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Scan k inp I \<subseteq> Scan k inp J"
  unfolding Scan_def bin_def by blast

lemma Predict_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Predict k cfg I \<subseteq> Predict k cfg J"
  unfolding Predict_def bin_def by blast

lemma Complete_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Complete k I \<subseteq> Complete k J"
  unfolding Complete_def bin_def by blast

lemma \<pi>_step_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi>_step k cfg inp I \<subseteq> \<pi>_step k cfg inp J"
  unfolding \<pi>_step_def using Scan_sub_mono Predict_sub_mono Complete_sub_mono by (metis sup.mono)

lemma funpower_sub_mono:
  "I \<subseteq> J \<Longrightarrow> funpower (\<pi>_step k cfg inp) n I \<subseteq> funpower (\<pi>_step k cfg inp) n J"
  by (induction n) (auto simp: \<pi>_step_sub_mono)

lemma \<pi>_sub_mono:
  "I \<subseteq> J \<Longrightarrow> \<pi> k cfg inp I \<subseteq> \<pi> k cfg inp J"
proof standard
  fix x
  assume "I \<subseteq> J" "x \<in> \<pi> k cfg inp I"
  then obtain n where "x \<in> funpower (\<pi>_step k cfg inp) n I"
    unfolding \<pi>_def limit_def natUnion_def by blast
  hence "x \<in> funpower (\<pi>_step k cfg inp) n J"
    using \<open>I \<subseteq> J\<close> funpower_sub_mono by blast
  thus "x \<in> \<pi> k cfg inp J"
    unfolding \<pi>_def limit_def natUnion_def by blast
qed

lemma Scan_\<pi>_step_mono:
  "Scan k inp I \<subseteq> \<pi>_step k cfg inp I"
  using \<pi>_step_def by blast

lemma Predict_\<pi>_step_mono:
  "Predict k cfg I \<subseteq> \<pi>_step k cfg inp I"
  using \<pi>_step_def by blast

lemma Complete_\<pi>_step_mono:
  "Complete k I \<subseteq> \<pi>_step k cfg inp I"
  using \<pi>_step_def by blast

lemma \<pi>_step_\<pi>_mono:
  "\<pi>_step k cfg inp I \<subseteq> \<pi> k cfg inp I"
proof -
  have "\<pi>_step k cfg inp I \<subseteq> funpower (\<pi>_step k cfg inp) 1 I"
    by simp
  thus ?thesis
    by (metis \<pi>_def limit_elem subset_eq)
qed

lemma Scan_\<pi>_mono:
  "Scan k inp  I \<subseteq> \<pi> k cfg inp I"
  using Scan_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma Predict_\<pi>_mono:
  "Predict k cfg I \<subseteq> \<pi> k cfg inp I"
  using Predict_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma Complete_\<pi>_mono:
  "Complete k I \<subseteq> \<pi> k cfg inp I"
  using Complete_\<pi>_step_mono \<pi>_step_\<pi>_mono by force

lemma \<pi>_mono:
  "I \<subseteq> \<pi> k cfg inp I"
  using \<pi>_step_\<pi>_mono \<pi>_step_def by blast

lemma Scan_bin_empty:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (Scan k inp I) i = {}"
  unfolding Scan_def bin_def inc_item_def by fastforce

lemma Predict_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Predict k cfg I) i = {}"
  unfolding Predict_def bin_def init_item_def by auto

lemma Complete_bin_empty:
  "i \<noteq> k \<Longrightarrow> bin (Complete k I) i = {}"
  unfolding Complete_def bin_def inc_item_def by auto

lemma \<pi>_step_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k + 1 \<Longrightarrow> bin (\<pi>_step k cfg inp I) i = bin I i"
  unfolding \<pi>_step_def using Scan_bin_empty Predict_bin_empty Complete_bin_empty
  unfolding bin_def using Un_iff empty_iff mem_Collect_eq by fastforce

lemma funpower_bin_absorb:
  "i \<noteq> k \<Longrightarrow> i \<noteq> k+1 \<Longrightarrow> bin (funpower (\<pi>_step k cfg inp) n I) i = bin I i"
  by (induction n) (auto simp: \<pi>_step_bin_absorb)

lemma \<pi>_bin_absorb:
  assumes "i \<noteq> k" "i \<noteq> k+1"
  shows "bin (\<pi> k cfg inp I) i = bin I i"
proof (standard; standard)
  fix x
  assume "x \<in> bin (\<pi> k cfg inp I) i"
  then obtain n where "x \<in> bin (funpower (\<pi>_step k cfg inp) n I) i"
    unfolding \<pi>_def limit_def natUnion_def by (auto simp: bin_def)
  then show "x \<in> bin I i"
    using funpower_bin_absorb assms by blast
next
  fix x
  assume "x \<in> bin I i"
  show "x \<in> bin (\<pi> k cfg inp I) i"
    using \<pi>_mono \<open>x \<in> bin I i\<close> by (metis (no_types, lifting) bin_def mem_Collect_eq subsetD)
qed


subsection \<open>Soundness\<close>

lemma Init_sub_Earley:
  "Init cfg \<subseteq> Earley cfg inp"
  unfolding Init_def init_item_def using Earley.Init by blast

lemma Scan_sub_Earley:
  assumes "I \<subseteq> Earley cfg inp"
  shows "Scan k inp I \<subseteq> Earley cfg inp"
  unfolding Scan_def inc_item_def bin_def using assms Earley.Scan 
  by (smt (verit, ccfv_SIG) item.exhaust_sel mem_Collect_eq subsetD subsetI)

lemma Predict_sub_Earley:
  assumes "I \<subseteq> Earley cfg inp"
  shows "Predict k cfg I \<subseteq> Earley cfg inp"
  unfolding Predict_def init_item_def bin_def using assms Earley.Predict
  using item.exhaust_sel by blast

lemma Complete_sub_Earley:
  assumes "I \<subseteq> Earley cfg inp"
  shows "Complete k I \<subseteq> Earley cfg inp"
  unfolding Complete_def inc_item_def bin_def using assms Earley.Complete
  by (smt (verit, del_insts) item.exhaust_sel mem_Collect_eq subset_eq)

lemma \<pi>_step_sub_Earley:
  assumes "I \<subseteq> Earley cfg inp"
  shows "\<pi>_step k cfg inp I \<subseteq> Earley cfg inp"
  unfolding \<pi>_step_def using assms Complete_sub_Earley Predict_sub_Earley Scan_sub_Earley by (metis le_supI)

lemma \<pi>_sub_Earley:
  assumes "I \<subseteq> Earley cfg inp"
  shows "\<pi> k cfg inp I \<subseteq> Earley cfg inp"
  using assms \<pi>_step_sub_Earley by (metis \<pi>_def limit_upperbound)

lemma \<I>_sub_Earley:
  shows "\<I> n cfg inp \<subseteq> Earley cfg inp"
  by (induction n) (auto simp: \<pi>_sub_Earley Init_sub_Earley)

lemma \<II>_sub_Earley:
  shows "\<II> cfg inp \<subseteq> Earley cfg inp"
  by (simp add: \<I>_sub_Earley \<II>_def)


subsection \<open>Completeness\<close>

lemma Earley_bin0_sub_\<pi>0:
  assumes "Init cfg \<subseteq> I"
  shows "bin (Earley cfg inp) 0 \<subseteq> bin (\<pi> 0 cfg inp I) 0"
proof standard
  fix x
  assume *: "x \<in> bin (Earley cfg inp) 0" 
  hence "x \<in> Earley cfg inp"
    using bin_def by blast
  thus "x \<in> bin (\<pi> 0 cfg inp I) 0"
    using assms *
  proof (induction rule: Earley.induct)
    case (Init r)
    thus ?case
      unfolding Init_def init_item_def bin_def using \<pi>_mono
      by (smt (verit, ccfv_SIG) CollectI item.sel(4) subsetD)
  next
    case (Scan x r b i j a)
    thus ?case
      by (simp add: bin_def)
  next
    case (Predict x r b i j r')
    have "j = 0"
      using Predict.prems(2) bin_def by (metis (mono_tags, lifting) item.sel(4) mem_Collect_eq)
    hence "x \<in> bin (Earley cfg inp) 0"
      using Predict.hyps(1,2) bin_def by force
    hence "x \<in> bin (\<pi> 0 cfg inp I) 0"
      using Predict.IH Predict.prems(1) by blast
    hence "Item r' 0 j j \<in> Predict 0 cfg (\<pi> 0 cfg inp I)"
      using Predict.hyps(1,3,4) Predict_def init_item_def bin_def \<open>j = 0\<close>
      by (smt (verit, del_insts) mem_Collect_eq)
    hence "Item r' 0 j j \<in> \<pi>_step 0 cfg inp (\<pi> 0 cfg inp I)"
      unfolding \<pi>_step_def by blast
    hence "Item r' 0 j j \<in> \<pi> 0 cfg inp I"
      using \<pi>_idem \<pi>_step_\<pi>_mono by blast
    thus ?case
      using bin_def \<open>j = 0\<close> by fastforce
  next
    case (Complete x r\<^sub>x b\<^sub>x i j y r\<^sub>y b\<^sub>y k)
    have "k = 0"
      using Complete.prems(2) bin_def by (metis (mono_tags, lifting) item.sel(4) mem_Collect_eq)
    hence "y \<in> bin (Earley cfg inp) 0"
      unfolding bin_def using Complete.hyps(3,4) by auto
    hence 0: "y \<in> bin (\<pi> 0 cfg inp I) 0"
      using Complete.IH Complete.prems(1) by blast
    have "j = 0"
      using wf_Earley Complete.hyps(3,4) wf_item_def \<open>k = 0\<close> by force
    hence "x \<in> bin (Earley cfg inp) 0"
      unfolding bin_def using Complete.hyps(1,2) by auto
    hence "x \<in> bin (\<pi> 0 cfg inp I) 0"
      using Complete.IH Complete.prems(1) by blast
    hence 1: "x \<in> bin (\<pi> 0 cfg inp I) (item_origin y)"
      by (auto simp: Complete.hyps(1) Complete.hyps(3) bin_def)
    have "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> Complete 0 (\<pi> 0 cfg inp I)"
      unfolding Complete_def inc_item_def using 0 1 Complete.hyps(1,3,5,6) \<open>k = 0\<close> by force
    hence "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> \<pi>_step 0 cfg inp (\<pi> 0 cfg inp I)"
      unfolding \<pi>_step_def by blast
    hence "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> \<pi> 0 cfg inp I"
      using \<pi>_idem \<pi>_step_\<pi>_mono by blast
    thus ?case
      using bin_def \<open>k = 0\<close> by fastforce
  qed
qed

definition prev_symbol :: "'a item \<Rightarrow> 'a option" where
  "prev_symbol x = (if item_dot x = 0 then None else Some (item_rule_body x ! (item_dot x - 1)))"

definition stem :: "'a sentence \<Rightarrow> 'a item set \<Rightarrow> nat \<Rightarrow> 'a item set" where
  "stem inp I k = { x . x \<in> I \<and> item_end x = k \<and> prev_symbol x = Some (inp!(k-1)) }"

lemma Earley_bink_sub_\<pi>k:
  assumes "k > 0"
  assumes "\<forall>k' < k. bin (Earley cfg inp) k' \<subseteq> I"
  assumes "stem inp (Earley cfg inp) k \<subseteq> I"
  shows "bin (Earley cfg inp) k \<subseteq> bin (\<pi> k cfg inp I) k"
proof standard
  fix x
  assume *: "x \<in> bin (Earley cfg inp) k" 
  hence "x \<in> Earley cfg inp"
    using bin_def by blast
  thus "x \<in> bin (\<pi> k cfg inp I) k"
    using assms *
  proof (induction rule: Earley.induct)
    case (Init r)
    have "k = 0"
      using Init.prems(4) unfolding bin_def by simp
    hence "False"
      using Init.prems(1) by blast
    thus ?case
      by blast
  next
    case (Scan x r b i j a)
    have "j+1 = k"
      using Scan.prems(4) bin_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    have "prev_symbol (Item r (b + 1) i (j + 1)) = Some (inp ! (k - 1))"
      using Scan.hyps(1,3,5) \<open>j+1 = k\<close> by (auto simp: next_symbol_def prev_symbol_def item_rule_body_def split: if_splits)
    hence "Item r (b + 1) i (j + 1) \<in> stem inp (Earley cfg inp) k"
      unfolding stem_def using Scan.prems(4) bin_def by fastforce
    hence "Item r (b + 1) i (j + 1) \<in> I"
      using Scan.prems(3) by blast
    hence "Item r (b + 1) i (j + 1) \<in> \<pi> k cfg inp I"
      using \<pi>_mono by blast
    thus ?case
      using \<open>j+1 = k\<close> bin_def by fastforce
  next
    case (Predict x r b i j r')
    have "j = k"
      using Predict.prems(4) bin_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    hence "x \<in> bin (Earley cfg inp) k"
      using Predict.hyps(1,2) bin_def by fastforce
    hence "x \<in> bin (\<pi> k cfg inp I) k"
      using Predict.IH Predict.prems(1-3) by blast
    hence "Item r' 0 j j \<in> Predict k cfg (\<pi> k cfg inp I)"
      unfolding Predict_def init_item_def using Predict.hyps(1,3,4) \<open>j = k\<close> by blast
    hence "Item r' 0 j j \<in> \<pi>_step k cfg inp (\<pi> k cfg inp I)"
      using Predict_\<pi>_step_mono by blast
    hence "Item r' 0 j j \<in> \<pi> k cfg inp I"
      using \<pi>_idem \<pi>_step_\<pi>_mono by blast
    thus ?case
      by (simp add: \<open>j = k\<close> bin_def)
  next
    case (Complete x r\<^sub>x b\<^sub>x i j y r\<^sub>y b\<^sub>y l)
    have "l = k"
      using Complete.prems(4) bin_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    hence "y \<in> bin (Earley cfg inp) l"
      using Complete.hyps(3,4) bin_def by fastforce
    hence 0: "y \<in> bin (\<pi> k cfg inp I) k"
      using Complete.IH(2) Complete.prems(1-3) \<open>l = k\<close> by blast
    have 1: "x \<in> bin (\<pi> k cfg inp I) (item_origin y)"
    proof (cases "j = k")
      case True
      hence "x \<in> bin (Earley cfg inp) k"
        using Complete.hyps(1,2) bin_def by fastforce
      hence "x \<in> bin (\<pi> k cfg inp I) k"
        using Complete.IH(1) Complete.prems(1-3) by blast
      thus ?thesis
        using Complete.hyps(3) True by simp
    next
      case False
      hence "j < k"
        using \<open>l = k\<close> wf_Earley wf_item_def Complete.hyps(3,4) by force
      moreover have "x \<in> bin (Earley cfg inp) j"
        using Complete.hyps(1,2) bin_def by force
      ultimately have "x \<in> I"
        using Complete.prems(2) by blast
      hence "x \<in> bin (\<pi> k cfg inp I) j"
        using Complete.hyps(1) \<pi>_mono bin_def by fastforce
      thus ?thesis
        using Complete.hyps(3) by simp
    qed
    have "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> Complete k (\<pi> k cfg inp I)"
      unfolding Complete_def inc_item_def using 0 1 Complete.hyps(1,5,6) by force
    hence "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> \<pi>_step k cfg inp (\<pi> k cfg inp I)"
      unfolding \<pi>_step_def by blast
    hence "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> \<pi> k cfg inp I"
      using \<pi>_idem \<pi>_step_\<pi>_mono by blast
    thus ?case
      using bin_def \<open>l = k\<close> by fastforce
  qed
qed

lemma Earley_stem1_sub_\<pi>0:
  assumes "Init cfg \<subseteq> I" "wf_cfg cfg" "is_word cfg inp"
  shows "stem inp (Earley cfg inp) 1 \<subseteq> bin (\<pi> 0 cfg inp I) 1"
proof standard
  fix x
  assume *: "x \<in> stem inp (Earley cfg inp) 1" 
  hence "x \<in> Earley cfg inp"
    using stem_def by blast
  thus "x \<in> bin (\<pi> 0 cfg inp I) 1"
    using assms *
  proof (induction rule: Earley.induct)
    case (Init r)
    have False
      using Init.prems(4) unfolding stem_def by simp
    thus ?case
      by blast
  next
    case (Scan x r b i j a)
    have "j = 0"
      using Scan.prems(4) unfolding stem_def by simp
    hence "x \<in> bin (\<pi> 0 cfg inp I) 0"
      using Earley_bin0_sub_\<pi>0 Scan.prems(1) Scan.hyps(1,2) bin_def
      by (metis (mono_tags, lifting) CollectI item.sel(4) subsetD)
    hence "Item r (b + 1) i (j + 1) \<in> Scan 0 inp (\<pi> 0 cfg inp I)"
      unfolding Scan_def inc_item_def using Scan.hyps \<open>j = 0\<close> by force
    hence "Item r (b + 1) i (j + 1) \<in> \<pi>_step 0 cfg inp (\<pi> 0 cfg inp I)"
      using Scan_\<pi>_step_mono by blast
    hence "Item r (b + 1) i (j + 1) \<in> \<pi> 0 cfg inp I"
      using \<pi>_idem \<pi>_step_\<pi>_mono by blast
    thus ?case
      using \<open>j = 0\<close> bin_def by fastforce
  next
    case (Predict x r b i j r')
    have False
      using Predict.prems(4) unfolding stem_def by (auto simp: prev_symbol_def)
    thus ?case
      by blast
  next
    case (Complete x r\<^sub>x b\<^sub>x i j y r\<^sub>y b\<^sub>y k)
    have "k-1 < length inp"
      using Complete.prems(4) stem_def wf_Earley wf_item_def
      by (smt (verit, best) CollectD One_nat_def diff_is_0_eq' item.sel(4) le_numeral_extra(4) less_eq_Suc_le)
    hence "is_terminal cfg (inp!(k-1))"
      using Complete.prems(3) is_word_is_terminal by blast
    moreover have "is_nonterminal cfg (item_rule_head y)"
      using Complete.hyps(3,4) Complete.prems(2) wf_Earley wf_item_def
      by (metis item_rule_head_def prod.collapse rule_head_def rule_nonterminal_type)
    moreover have "prev_symbol (Item r\<^sub>x (b\<^sub>x + 1) i k) = next_symbol x"
      using Complete.hyps(1,6)
      by (auto simp: next_symbol_def prev_symbol_def is_complete_def item_rule_body_def split: if_splits)
    moreover have "prev_symbol (Item r\<^sub>x (b\<^sub>x + 1) i k) = Some (inp!(k-1))"
      using Complete.prems(4) stem_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    ultimately have False
      using Complete.hyps(6) Complete.prems(2) is_terminal_nonterminal by fastforce
    thus ?case
      by blast
  qed
qed

lemma Earley_stemk_sub_\<pi>k:
  assumes "k > 0" "wf_cfg cfg" "is_word cfg inp"
  assumes "\<forall>k' < k. bin (Earley cfg inp) k' \<subseteq> I"
  assumes "stem inp (Earley cfg inp) k \<subseteq> I"
  shows "stem inp (Earley cfg inp) (k+1) \<subseteq> bin (\<pi> k cfg inp I) (k+1)"
proof standard
  fix x
  assume *: "x \<in> stem inp (Earley cfg inp) (k+1)" 
  hence "x \<in> Earley cfg inp"
    using stem_def by blast
  thus "x \<in> bin (\<pi> k cfg inp I) (k+1)"
    using assms *
  proof (induction rule: Earley.induct)
    case (Init r)
    have "k = 0"
      using Init.prems(6) unfolding stem_def by simp
    hence False
      using Init.prems(1) by blast
    thus ?case
      by blast
  next
    case (Scan x r b i j a)
    have "j = k"
      using Scan.prems(6) stem_def by (metis (mono_tags, lifting) CollectD add_right_cancel item.sel(4))
    hence "x \<in> bin (\<pi> k cfg inp I) k"
      using Earley_bink_sub_\<pi>k Scan.prems(1,4,5) Scan.hyps(1,2) bin_def
      by (metis (mono_tags, lifting) CollectI item.sel(4) subsetD)
    hence "Item r (b + 1) i (j + 1) \<in> Scan k inp (\<pi> k cfg inp I)"
      unfolding Scan_def inc_item_def using Scan.hyps \<open>j = k\<close> by force
    hence "Item r (b + 1) i (j + 1) \<in> \<pi>_step k cfg inp (\<pi> k cfg inp I)"
      using Scan_\<pi>_step_mono by blast
    hence "Item r (b + 1) i (j + 1) \<in> \<pi> k cfg inp I"
      using \<pi>_idem \<pi>_step_\<pi>_mono by blast
    thus ?case
      using \<open>j = k\<close> bin_def by fastforce
  next
    case (Predict x r b i j r')
    have False
      using Predict.prems(6) unfolding stem_def by (auto simp: prev_symbol_def)
    thus ?case
      by blast
  next
    case (Complete x r\<^sub>x b\<^sub>x i j y r\<^sub>y b\<^sub>y l)
    have "l-1 < length inp"
      using Complete.prems(6) stem_def wf_Earley wf_item_def
      by (metis (mono_tags, lifting) CollectD add.right_neutral add_Suc_right add_diff_cancel_right' item.sel(4) less_eq_Suc_le plus_1_eq_Suc)
    hence "is_terminal cfg (inp!(l-1))"
      using Complete.prems(3) is_word_is_terminal by blast
    moreover have "is_nonterminal cfg (item_rule_head y)"
      using Complete.hyps(3,4) Complete.prems(2) wf_Earley wf_item_def
      by (metis item_rule_head_def prod.collapse rule_head_def rule_nonterminal_type)
    moreover have "prev_symbol (Item r\<^sub>x (b\<^sub>x + 1) i l) = next_symbol x"
      using Complete.hyps(1,6)
      by (auto simp: next_symbol_def prev_symbol_def is_complete_def item_rule_body_def split: if_splits)
    moreover have "prev_symbol (Item r\<^sub>x (b\<^sub>x + 1) i l) = Some (inp!(l-1))"
      using Complete.prems(6) stem_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    ultimately have False
      using Complete.hyps(6) Complete.prems(2) is_terminal_nonterminal by fastforce
    thus ?case
      by blast
  qed
qed

lemma Earley_bink_sub_\<I>:
  assumes "wf_cfg cfg" "is_word cfg inp" "k \<le> n"
  shows "bin (Earley cfg inp) k \<subseteq> \<I> n cfg inp"
  using assms
proof (induction n arbitrary: k)
  case 0
  thus ?case
    using Earley_bin0_sub_\<pi>0 bin_def by fastforce
next
  case (Suc n)
  show ?case
  proof (cases "k \<le> n")
    case True
    thus ?thesis
      using Suc \<pi>_mono by force
  next
    case False
    hence "k = n+1"
      using Suc.prems(3) by force
    have 0: "\<forall>k' < k. bin (Earley cfg inp) k' \<subseteq> \<I> n cfg inp"
      using Suc by simp
    moreover have "stem inp (Earley cfg inp) k \<subseteq> \<I> n cfg inp"
    proof cases
      assume "k = 1"
      hence "stem inp (Earley cfg inp) k \<subseteq> bin (\<pi> 0 cfg inp (Init cfg)) 1"
        using Earley_stem1_sub_\<pi>0 Suc.prems(1,2) by blast
      also have "... = bin (\<I> 0 cfg inp) 1"
        by simp
      finally show ?thesis
        using \<open>k = 1\<close> \<open>k = n+1\<close> bin_def by auto
    next
      assume "k \<noteq> 1"
      hence "0 < k-1"
        using \<open>k = n + 1\<close> by linarith
      moreover have "\<forall>k' < k-1. bin (Earley cfg inp) k' \<subseteq> \<I> n cfg inp"
        using Suc \<open>k = n + 1\<close> by auto
      moreover have "stem inp (Earley cfg inp) (k-1) \<subseteq> \<I> n cfg inp"
        using 0 bin_def stem_def False \<open>k = n + 1\<close> 
        by (smt (verit) Suc_eq_plus1 diff_Suc_1 linorder_not_less mem_Collect_eq subsetD subsetI)
      ultimately have "stem inp (Earley cfg inp) k \<subseteq> bin (\<pi> n cfg inp (\<I> n cfg inp)) k"
        by (metis Earley_stemk_sub_\<pi>k \<open>k = n + 1\<close> add_diff_cancel_right' assms(1) assms(2))
      hence "stem inp (Earley cfg inp) k \<subseteq> bin (\<I> n cfg inp) k"
        by (metis \<I>.elims \<pi>_idem)
      thus ?thesis
        using bin_def by blast
    qed
    ultimately have "bin (Earley cfg inp) k \<subseteq> bin (\<pi> k cfg inp (\<I> n cfg inp)) k"
      by (metis Earley_bink_sub_\<pi>k Suc_eq_plus1 \<open>k = n + 1\<close> less_Suc_eq_le zero_le)
    thus ?thesis
      by (metis (no_types, lifting) CollectD Collect_mono_iff Suc_eq_plus1 \<I>.simps(2) \<open>k = n + 1\<close> bin_def subsetI)
  qed
qed

lemma Earley_sub_\<II>:
  assumes "wf_cfg cfg" "is_word cfg inp"
  shows "Earley cfg inp \<subseteq> \<II> cfg inp"
proof -
  have "\<forall>k \<le> length inp. bin (Earley cfg inp) k \<subseteq> \<II> cfg inp"
    by (simp add: Earley_bink_sub_\<I> \<II>_def assms)
  thus ?thesis
    using wf_Earley wf_item_def bin_def by blast
qed

theorem Earley_eq_\<II>:
  assumes "wf_cfg cfg" "is_word cfg inp"
  shows "Earley cfg inp = \<II> cfg inp"
  by (simp add: Earley_sub_\<II> \<II>_sub_Earley assms subset_antisym)

end

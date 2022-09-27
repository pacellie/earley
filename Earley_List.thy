theory Earley_List
  imports 
    Earley_Set
begin

section \<open>Earley recognizer with traces\<close>

subsection \<open>List auxilaries\<close>

fun find_index' :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "find_index' _  _ [] = None"
| "find_index' i P (x#xs) = (if P x then Some i else find_index' (i+1) P xs)"

definition find_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "find_index = find_index' 0"

lemma find_index'_None_iff:
  "find_index' i P xs = None \<longleftrightarrow> (\<nexists>x. x \<in> set xs \<and> P x)"
  by (induction xs arbitrary: i) auto

lemma find_index_None_iff:
  "find_index P xs = None \<longleftrightarrow> (\<nexists>x. x \<in> set xs \<and> P x)"
  by (simp add: find_index'_None_iff find_index_def)

lemma find_index_None_iff_i:
  "find_index P xs = None \<longleftrightarrow> (\<nexists>i. i < length xs \<and> P (xs ! i))"
  by (metis find_index_None_iff in_set_conv_nth)

lemma find_index'_Some_iff:
  "(\<exists>n. find_index' i P xs = Some n) \<longleftrightarrow> (\<exists>x. x \<in> set xs \<and> P x)"
  by (induction xs arbitrary: i) auto

lemma find_index_Some_iff:
  "(\<exists>n. find_index P xs = Some n) \<longleftrightarrow> (\<exists>x. x \<in> set xs \<and> P x)"
  by (metis find_index_None_iff not_Some_eq)

lemma find_index'_index_size_ge:
  "find_index' i P xs = Some n \<Longrightarrow> n \<ge> i"
  by (induction xs arbitrary: i) (auto simp: Suc_leD split: if_splits)

lemma find_index'_index_size_gt:
  "find_index' i P (x#xs) = Some n \<Longrightarrow> \<not> P x \<Longrightarrow> n > i"
  by (cases xs) (auto split: if_splits, meson Suc_leD Suc_le_lessD find_index'_index_size_ge)

lemma find_index'_Some_length:
  "find_index' i P xs = Some n \<Longrightarrow> n - i < length xs"
  by (induction xs arbitrary: i) (auto split: if_splits, force)

lemma find_index'_Some_nth:
  "find_index' i P xs = Some n \<Longrightarrow> P (xs ! (n-i))"
proof (induction xs arbitrary: i)
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    thus ?thesis
      using Cons by simp
  next
    case False
    hence "0 < n - i"
      using find_index'_index_size_gt Cons.prems by fastforce
    thus ?thesis
      using nth_Cons_pos Cons False by simp
  qed
qed simp

lemma find_index'_Some_not_nth:
  "find_index' i P xs = Some n \<Longrightarrow> \<forall>m < (n-i). \<not> P (xs ! m)"
  by (induction xs arbitrary: i) (auto simp: nth_Cons' split: if_splits)

lemma find_index'_is_Some:
  "n \<ge> i \<Longrightarrow> n - i < length xs \<Longrightarrow> P (xs ! (n-i)) \<Longrightarrow> \<forall>m < (n-i). \<not> P (xs ! m) \<Longrightarrow> find_index' i P xs = Some n"
proof (induction xs arbitrary: i)
  case (Cons x xs)
  show ?case
  proof (cases "n = i")
    case True
    thus ?thesis
      using Cons by simp
  next
    case False
    hence *: "n > i"
      using Cons.prems(1) by simp
    moreover have "\<forall>m<n - (i+1). \<not> P (xs ! m)"
      using * Cons.prems(4) by (auto, metis Suc_diff_Suc not_less_eq nth_Cons_Suc)
    ultimately show ?thesis
      using Cons.IH Cons.prems(2,3,4) by (auto, metis nth_Cons_0 zero_less_diff)
  qed
qed simp

lemma find_index_Some_iff_i:
  "find_index P xs = Some n \<longleftrightarrow> n < length xs \<and> P (xs ! n) \<and> (\<forall>m < n. \<not> P (xs ! m))"
  unfolding find_index_def using find_index'_Some_length find_index'_Some_nth
  by (auto simp: find_index'_Some_not_nth find_index'_is_Some, fastforce+)

fun filter_with_index' :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index' _ _ [] = []"
| "filter_with_index' i P (x#xs) = (
    if P x then (x,i) # filter_with_index' (i+1) P xs
    else filter_with_index' (i+1) P xs)"

definition filter_with_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index P xs = filter_with_index' 0 P xs"

lemma filter_with_index'_cong_filter:
  "map fst (filter_with_index' i P xs) = filter P xs"
  by (induction xs arbitrary: i) auto

lemma filter_with_index_cong_filter:
  "map fst (filter_with_index P xs) = filter P xs"
  by (simp add: filter_with_index'_cong_filter filter_with_index_def)

lemma size_index_filter_with_index':
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> n \<ge> i"
  by (induction xs arbitrary: i) (auto simp: Suc_leD split: if_splits)

lemma filter_with_index'_nth:
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> xs ! (n-i) = x"
proof (induction xs arbitrary: i)
  case (Cons y xs)
  show ?case
  proof (cases "x = y")
    case True
    thus ?thesis
      using Cons by (auto simp: nth_Cons' split: if_splits)
  next
    case False
    hence "(x, n) \<in> set (filter_with_index' (i+1) P xs)"
      using Cons.prems by (cases xs) (auto split: if_splits)
    hence "n \<ge> i + 1" "xs ! (n - i - 1) = x"
      by (auto simp: size_index_filter_with_index' Cons.IH)
    thus ?thesis
      by simp
  qed
qed simp

lemma filter_with_index_nth:
  "(x, n) \<in> set (filter_with_index P xs) \<Longrightarrow> xs ! n = x"
  by (metis diff_zero filter_with_index'_nth filter_with_index_def)


subsection \<open>Bins\<close>

datatype pointer =
  Pre nat \<comment>\<open>pred index in current bin\<close>
  | PreRed nat nat nat \<comment>\<open>pred bin, pred index, red index in current bin\<close>

type_synonym pointers = "pointer list"

datatype 'a bin =
  Bin 
    (items : "'a item list")
    (pointers : "pointers list")

type_synonym 'a bins = "'a bin list"

definition bin_ptr :: "'a bin \<Rightarrow> ('a item \<times> pointers) set" where
  "bin_ptr b = set (zip (items b) (pointers b))"

definition bins :: "'a bins \<Rightarrow> 'a items" where
  "bins bs = \<Union> { set (items (bs ! k)) | k. k < length bs }"

definition bin_upto :: "'a bin \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bin_upto b i = { items b ! j | j. j < i \<and> j < length (items b) }"

definition bins_upto :: "'a bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a items" where
  "bins_upto bs k i = \<Union> { set (items (bs ! l)) | l. l < k } \<union> bin_upto (bs ! k) i"

definition distinct_ptrs :: "pointers list \<Rightarrow> bool" where
  "distinct_ptrs ptrs = (\<forall>ps \<in> set ptrs. distinct ps)"

definition wf_bin_items :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a item list \<Rightarrow> bool" where
  "wf_bin_items cfg inp k xs = (\<forall>x \<in> set xs. wf_item cfg inp x \<and> item_end x = k)"

definition wf_bin :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> 'a bin \<Rightarrow> bool" where
  "wf_bin cfg inp k b \<longleftrightarrow> 
    distinct (items b) \<and>
    wf_bin_items cfg inp k (items b) \<and>
    length (items b) = length (pointers b) \<and>
    distinct_ptrs (pointers b)"

definition wf_bins :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "wf_bins cfg inp bs \<longleftrightarrow> (\<forall>k < length bs. wf_bin cfg inp k (bs ! k))"

definition nonempty_derives :: "'a cfg \<Rightarrow> bool" where
  "nonempty_derives cfg = (\<forall>N. N \<in> set (\<NN> cfg) \<longrightarrow> \<not> derives cfg [N] [])"

definition bin_ptr_upd :: "nat \<Rightarrow> pointers \<Rightarrow> 'a bin \<Rightarrow>  'a bin" where
  "bin_ptr_upd i ptrs b = Bin (items b) ((pointers b)[i := filter (\<lambda>ptr. ptr \<notin> set (pointers b ! i)) ptrs @ (pointers b ! i)])"

definition bin_ins :: "'a item \<Rightarrow> pointers \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "bin_ins item ptrs b = Bin (items b @ [item]) (pointers b @ [ptrs])"

definition bin_upd :: "'a item \<times> pointers \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "bin_upd ip b = (
    case find_index (\<lambda>item. item = fst ip) (items b) of
      None \<Rightarrow> bin_ins (fst ip) (snd ip) b
    | Some i \<Rightarrow> bin_ptr_upd i (snd ip) b)"

fun bin_upds :: "('a item \<times> pointers) list \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "bin_upds [] b = b"
| "bin_upds (ip#ips) b = bin_upds ips (bin_upd ip b)"

definition bins_upd :: "'a bins \<Rightarrow> nat \<Rightarrow> ('a item \<times> pointers) list \<Rightarrow> 'a bins" where
  "bins_upd bs k ips = bs[k := bin_upds ips (bs!k)]"

definition subsumed_by :: "('a \<times> 'b list) set \<Rightarrow> ('a \<times> 'b list) set \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
  "subsumed_by A B = (\<forall>x \<in> A. \<exists>y \<in> B. fst x = fst y \<and> set (snd x) \<subseteq> set (snd y))"

lemma subsumed_by_mono:
  "A \<sqsubseteq> B \<Longrightarrow> B \<sqsubseteq> C \<Longrightarrow> A \<sqsubseteq> C"
  unfolding subsumed_by_def by (smt (verit, ccfv_SIG) dual_order.trans)

lemma length_bins_upd[simp]:
  "length (bins_upd bs k ips) = length bs"
  unfolding bins_upd_def bin_upd_def bin_ptr_upd_def bin_ins_def by simp

lemma length_items_bin_upd:
  "length (items (bin_upd ip b)) \<ge> length (items b)"
  unfolding bin_upd_def bin_ins_def bin_ptr_upd_def by (auto split: option.splits)

lemma length_items_pointers_bin_upd:
  "length (items b) = length (pointers b) \<Longrightarrow> length (items (bin_upd ip b)) = length (pointers (bin_upd ip b))"
  unfolding bin_upd_def bin_ins_def bin_ptr_upd_def by (auto split: option.splits)

lemma length_items_bin_upds:
  "length (items (bin_upds ips b)) \<ge> length (items b)"
  by (induction ips arbitrary: b) (auto, meson dual_order.trans length_items_bin_upd)

lemma length_items_nth_bin_bins_upd:
  "length (items (bins_upd bs k ips ! n)) \<ge> length (items (bs ! n))"
  unfolding bins_upd_def using length_items_bin_upds
  by (metis linorder_not_le list_update_beyond nth_list_update_eq nth_list_update_neq order_refl)

lemma length_pointers_bin_upd:
  "length (pointers (bin_upd ip b)) \<ge> length (pointers b)"
  unfolding bin_upd_def bin_ins_def bin_ptr_upd_def by (auto split: option.splits)

lemma length_pointers_bin_upds:
  "length (pointers (bin_upds ips b)) \<ge> length (pointers b)"
  by (induction ips arbitrary: b) (auto, meson dual_order.trans length_pointers_bin_upd)

lemma length_pointers_nth_bin_bins_upd:
  "length (pointers (bins_upd bs k ips ! n)) \<ge> length (pointers (bs ! n))"
  unfolding bins_upd_def using length_pointers_bin_upds
  by (metis linorder_not_le list_update_beyond nth_list_update_eq nth_list_update_neq order_refl)

lemma length_items_nth_bin_bins_upd_eq:
  "k \<noteq> n \<Longrightarrow> length (items (bins_upd bs k ips ! n)) = length (items (bs ! n))"
  unfolding bins_upd_def by simp

lemma nth_bins_upd:
  "k \<noteq> n \<Longrightarrow> bins_upd bs k ips ! n = bs ! n"
  unfolding bins_upd_def by simp

lemma items_mth_bin_upd:
  "m < length (items b) \<Longrightarrow> items (bin_upd ip b) ! m = items b ! m"
  unfolding bin_upd_def bin_ins_def bin_ptr_upd_def by (auto simp: nth_append split: option.splits)

lemma items_mth_bin_upds:
  "m < length (items b) \<Longrightarrow> items (bin_upds ips b) ! m = items b ! m"
  by (induction ips arbitrary: b) (auto simp: items_mth_bin_upd length_items_bin_upd order.strict_trans2)

lemma items_mth_bins_upd:
  "m < length (items (bs ! k)) \<Longrightarrow> items (bins_upd bs k ips ! k) ! m = items (bs ! k) ! m"
  unfolding bins_upd_def using items_mth_bin_upds by (metis linorder_not_less list_update_beyond nth_list_update_eq)

lemma bin_upto_eq_set_bin:
  "i \<ge> length (items b) \<Longrightarrow> bin_upto b i = set (items b)"
  unfolding bin_upto_def set_bin_def by (auto, metis in_set_conv_nth less_le_trans)

lemma bins_upto_empty:
  "bins_upto bs 0 0 = {}"
  unfolding bins_upto_def bin_upto_def by simp

lemma set_items_bin_ins:
  "set (items (bin_ins x ptrs b)) = set (items b) \<union> {x}"
  unfolding bin_ins_def by simp

lemma set_items_bin_ptr_upd:
  "set (items (bin_ptr_upd i ptrs b)) = set (items b)"
  unfolding bin_ptr_upd_def by simp

lemma set_items_bin_upd:
  "set (items (bin_upd ip b)) = set (items b) \<union> {fst ip}"
proof (cases "find_index (\<lambda>x. x = fst ip) (items b) = None")
  case True
  have "set (items (bin_ins (fst ip) (snd ip) b)) = set (items b) \<union> {fst ip}"
    using set_items_bin_ins by blast
  thus ?thesis
    unfolding bin_upd_def using True by simp
next
  case False
  then obtain i where i: "find_index (\<lambda>x. x = fst ip) (items b) = Some i"
    by blast
  have "set (items (bin_upd ip b)) = set (items b)"
    unfolding bin_upd_def using i set_items_bin_ptr_upd by simp
  moreover have "fst ip \<in> set (items b)"
    using set_bin_def False find_index_None_iff[of "\<lambda>x. x = fst ip"] by simp
  ultimately show ?thesis
    by blast
qed

lemma set_items_bin_upds:
  "set (items (bin_upds ips b)) = set (items b) \<union> set (map fst ips)"
  using set_items_bin_upd by (induction ips arbitrary: b) (auto, blast+)

lemma bins_bins_upd:
  assumes "k < length bs"
  shows "bins (bins_upd bs k ips) = bins bs \<union> set (map fst ips)"
proof -
  let ?bs = "bins_upd bs k ips"
  have "bins (bins_upd bs k ips) = \<Union> {set (items (?bs ! k)) |k. k < length ?bs}"
    unfolding bins_def by blast
  also have "... = \<Union> {set (items (bs ! l)) |l. l < length bs \<and> l \<noteq> k} \<union> set (items (?bs ! k))"
    unfolding bins_upd_def using assms by (auto, metis nth_list_update)
  also have "... = \<Union> {set (items (bs ! l)) |l. l < length bs \<and> l \<noteq> k} \<union> set (items (bs ! k)) \<union> set (map fst ips)"
    using set_items_bin_upds[of ips "bs!k"] by (simp add: assms bins_upd_def sup_assoc)
  also have "... = \<Union> {set (items (bs ! k)) |k. k < length bs} \<union> set (map fst ips)"
    using assms by blast
  also have "... = bins bs \<union> set (map fst ips)"
    unfolding bins_def by blast
  finally show ?thesis .
qed

lemma bin_ptr_bin_upd_not_in:
  assumes "fst ip \<notin> set (items b)" "length (items b) = length (pointers b)"
  shows "ip \<in> bin_ptr (bin_upd ip b)"
  using assms unfolding bin_ptr_def bin_upd_def bin_ins_def bin_ptr_upd_def
  by (auto split: option.splits, metis (mono_tags, lifting) find_index_Some_iff)+
                                                            
lemma kth_bin_sub_bins:
  "k < length bs \<Longrightarrow> set (items (bs ! k)) \<subseteq> bins bs"
  unfolding bins_def bins_upto_def bin_upto_def by blast+

lemma bin_upto_nth_id_bin_ins:
  "n < length (items b) \<Longrightarrow> bin_upto (bin_ins x ptrs b) n = bin_upto b n"
  unfolding bin_ins_def bin_upto_def by (auto simp: nth_append)

lemma bin_upto_nth_id_bin_ptr_upd:
  "n < length (items b) \<Longrightarrow> bin_upto (bin_ptr_upd i prts b) n = bin_upto b n"
  unfolding bin_ptr_upd_def bin_upto_def by auto

lemma bin_upto_nth_id_bin_upd:
  "n < length (items b) \<Longrightarrow> bin_upto (bin_upd ip b) n = bin_upto b n"
  unfolding bin_upd_def apply (auto split: option.splits)
  using bin_upto_nth_id_bin_ins bin_upto_nth_id_bin_ptr_upd by blast+

lemma bin_upto_nth_id_bin_upds:
  "n < length (items b) \<Longrightarrow> bin_upto (bin_upds ips b) n = bin_upto b n"
  using bin_upto_nth_id_bin_upd length_items_bin_upd
  apply (induction ips arbitrary: b) apply auto
  using order.strict_trans2 order.strict_trans1 by blast+

lemma bins_upto_kth_nth_id:
  assumes "l < length bs" "k \<le> l" "n < length (items (bs ! k))"
  shows "bins_upto (bins_upd bs l ips) k n = bins_upto bs k n"
proof -
  let ?bs = "bins_upd bs l ips"
  have "bins_upto ?bs k n = \<Union> {set (items (?bs ! l)) |l. l < k} \<union> bin_upto (?bs ! k) n"
    unfolding bins_upto_def by blast
  also have "... = \<Union> {set (items (bs ! l)) |l. l < k} \<union> bin_upto (?bs ! k) n"
    unfolding bins_upd_def using assms(1,2) by auto
  also have "... = \<Union> {set (items (bs ! l)) |l. l < k} \<union> bin_upto (bs ! k) n"
    unfolding bins_upd_def using assms(1,3) bin_upto_nth_id_bin_upds
    by (metis (no_types, lifting) nth_list_update)
  also have "... = bins_upto bs k n"
    unfolding bins_upto_def by blast
  finally show ?thesis .
qed

lemma bins_upto_sub_bins:
  "k < length bs \<Longrightarrow> bins_upto bs k n \<subseteq> bins bs"
  unfolding bins_def bins_upto_def bin_upto_def using less_trans by (auto, blast)

lemma bins_upto_Suc_Un:
  "n < length (items (bs ! k)) \<Longrightarrow> bins_upto bs k (n+1) = bins_upto bs k n \<union> { items (bs ! k) ! n }"
  unfolding bins_upto_def bin_upto_def using less_Suc_eq by auto

lemma bins_upto_Suc_eq:
  "n \<ge> length (items (bs ! k)) \<Longrightarrow> bins_upto bs k (n+1) = bins_upto bs k n"
  unfolding bins_upto_def bin_upto_def by (auto; metis dual_order.strict_trans1 items_def length_map)

lemma bins_bin_exists:
  "x \<in> bins bs \<Longrightarrow> \<exists>k < length bs. x \<in> set (items (bs ! k))"
  unfolding bins_def by blast

lemma distinct_bin_upd:
  "distinct (items b) \<Longrightarrow> distinct (items (bin_upd ip b))"
  unfolding bin_upd_def bin_ins_def bin_ptr_upd_def
  by (auto simp add: find_index_None_iff split: option.splits)

lemma distinct_bin_upds:
  "distinct (items b) \<Longrightarrow> distinct (map fst ips) \<Longrightarrow> distinct (items (bin_upds ips b))"
  by (induction ips arbitrary: b) (auto simp: distinct_bin_upd)

lemma distinct_bins_upd:
  "distinct (items (bs ! k)) \<Longrightarrow> distinct (map fst ips) \<Longrightarrow> distinct (items (bins_upd bs k ips ! k))"
  by (metis bins_upd_def distinct_bin_upds leI list_update_beyond nth_list_update_eq)

lemma wf_bins_kth_bin:
  "wf_bins cfg inp bs \<Longrightarrow> k < length bs \<Longrightarrow> x \<in> set (items (bs ! k)) \<Longrightarrow> wf_item cfg inp x \<and> item_end x = k"
  using set_bin_def wf_bin_def wf_bins_def wf_bin_items_def by blast

lemma wf_bin_bin_ins:
  assumes "wf_bin cfg inp k b" "wf_item cfg inp x \<and> item_end x = k" "x \<notin> set (items b)" "distinct_ptrs [ptrs]"
  shows "wf_bin cfg inp k (bin_ins x ptrs b)"
  unfolding bin_ins_def using assms by (auto simp: wf_bin_def wf_bin_items_def distinct_ptrs_def)

lemma wf_bin_bin_ptr_upd:
  assumes "wf_bin cfg inp k b" "wf_item cfg inp x \<and> item_end x = k" "x \<in> set (items b)" "distinct_ptrs [ptrs]"
  shows "wf_bin cfg inp k (bin_ptr_upd i ptrs b)"
proof -
  have "i < length (pointers b) \<Longrightarrow> distinct (filter (\<lambda>ptr. ptr \<notin> set (pointers b ! i)) ptrs @ pointers b ! i)"
    using distinct_append assms(1,4) by (auto simp: wf_bin_def distinct_ptrs_def)
  thus ?thesis
    unfolding bin_ptr_upd_def using assms set_update_subset_insert by (auto simp: wf_bin_def distinct_ptrs_def, fastforce)
qed

lemma wf_bin_bin_upd:
  assumes "wf_bin cfg inp k b" "wf_item cfg inp (fst ip) \<and> item_end (fst ip) = k" "distinct_ptrs [snd ip]"
  shows "wf_bin cfg inp k (bin_upd ip b)"
  unfolding bin_upd_def using assms
  apply (auto simp: find_index_None_iff wf_bin_bin_ins split: option.splits)
  by (metis (full_types) find_index_None_iff option.distinct(1) wf_bin_bin_ptr_upd)

lemma wf_bin_bin_upds:
  assumes "wf_bin cfg inp k b" "distinct (map fst ips)" "distinct_ptrs (map snd ips)"
  assumes "\<forall>x \<in> set (map fst ips). wf_item cfg inp x \<and> item_end x = k"
  shows "wf_bin cfg inp k (bin_upds ips b)"
  using assms by (induction ips arbitrary: b) (auto simp: wf_bin_bin_upd distinct_ptrs_def)

lemma wf_bins_bins_upd:
  assumes "wf_bins cfg inp bs" "distinct (map fst ips)" "distinct_ptrs (map snd ips)"
  assumes "\<forall>x \<in> set (map fst ips). wf_item cfg inp x \<and> item_end x = k"
  shows "wf_bins cfg inp (bins_upd bs k ips)"
  unfolding bins_upd_def using assms wf_bin_bin_upds wf_bins_def
  by (metis length_list_update nth_list_update_eq nth_list_update_neq)

lemma wf_bins_impl_wf_items:
  "wf_bins cfg inp bs \<Longrightarrow> wf_items cfg inp (bins bs)"
  unfolding wf_bins_def wf_bin_def wf_items_def wf_bin_items_def bins_def by auto

lemma set_pointers_bin_ins:
  "j < length (pointers b) \<Longrightarrow> set (pointers b ! j) \<subseteq> set (pointers (bin_ins x ptrs b) ! j)"
  unfolding bin_ins_def by (auto simp: nth_append)

lemma set_pointers_bin_ptr_upd:
  "i < length (pointers b) \<Longrightarrow> set (pointers b ! j) \<subseteq> set (pointers (bin_ptr_upd i ptrs b) ! j)"
  unfolding bin_ptr_upd_def by (auto simp: nth_list_update)

lemma set_pointers_bin_upd:
  "j < length (pointers b) \<Longrightarrow> set (pointers b ! j) \<subseteq> set (pointers (bin_upd ip b) ! j)"
  unfolding bin_upd_def using set_pointers_bin_ins set_pointers_bin_ptr_upd
  apply (auto split: option.splits, blast)
  by (smt (verit, best) set_pointers_bin_ptr_upd bin.sel(2) bin_ptr_upd_def in_mono nth_list_update_neq)

lemma set_pointer_bin_upds:
  "j < length (pointers b) \<Longrightarrow> set (pointers b ! j) \<subseteq> set (pointers (bin_upds ips b) ! j)"
  using set_pointers_bin_upd
  apply (induction ips arbitrary: b)
  apply (auto)
  using length_pointers_bin_upd order.strict_trans2 by blast

lemma set_pointers_bins_upd:
  "j < length (pointers (bs ! l)) \<Longrightarrow> set (pointers (bs ! l) ! j) \<subseteq> set (pointers (bins_upd bs k ips ! l) ! j)"
  unfolding bins_upd_def using set_pointer_bin_upds
  by (metis dual_order.refl linorder_not_less list_update_beyond nth_list_update_eq nth_list_update_neq)

lemma ex_subsumed_bin_ins:
  assumes "length (items b) = length (pointers b)"
  shows "\<exists>(y, ptrs') \<in> bin_ptr (bin_ins x ptrs b). x = y \<and> set ptrs \<subseteq> set ptrs'"
  unfolding bin_ins_def bin_ptr_def using assms by simp

lemma ex_subsumed_bin_ptr_upd:
  assumes "items b ! i = x" "i < length (items b)" "i < length (pointers b)"
  shows "\<exists>(y, ptrs') \<in> bin_ptr (bin_ptr_upd i ptrs b). x = y \<and> set ptrs \<subseteq> set ptrs'"
proof -
  have "(items (bin_ptr_upd i ptrs b) ! i, pointers (bin_ptr_upd i ptrs b) ! i) \<in> bin_ptr (bin_ptr_upd i ptrs b)"
    using assms(2,3) unfolding bin_ptr_def bin_ptr_upd_def using in_set_zip by fastforce
  moreover have "items (bin_ptr_upd i ptrs b) ! i = x"
    unfolding bin_ptr_upd_def using assms(1) by simp
  moreover have "set ptrs \<subseteq> set (pointers (bin_ptr_upd i ptrs b) ! i)"
    unfolding bin_ptr_upd_def using assms(3) by auto
  ultimately show ?thesis
    by blast
qed

lemma ex_subsumed_bin_upd:
  assumes "length (items b) = length (pointers b)" 
  shows "\<exists>(y, ptrs') \<in> bin_ptr (bin_upd ip b). fst ip = y \<and> set (snd ip) \<subseteq> set ptrs'"
  unfolding bin_upd_def by (auto simp: assms ex_subsumed_bin_ins ex_subsumed_bin_ptr_upd find_index_Some_iff_i split: option.splits)

lemma subsumed_bin_ins:
  assumes "length (items b) = length (pointers b)"
  shows "bin_ptr b \<sqsubseteq> bin_ptr (bin_ins (fst ip) (snd ip) b)"
  using assms unfolding bin_ins_def bin_ptr_def subsumed_by_def by auto

lemma subsumed_bin_ptr_upd:
  assumes "i < length (items b)" "i < length (pointers b)"
  shows "bin_ptr b \<sqsubseteq> bin_ptr (bin_ptr_upd i ptrs'' b)"
proof -
  {
    fix x
    assume *: "x \<in> bin_ptr b"
    obtain j where j: "fst x = items b ! j" "snd x = pointers b ! j" "j < length (items b)" "j < length (pointers b)"
      using * unfolding bin_ptr_def by (metis in_set_zip)
    have "fst x = items (bin_ptr_upd i ptrs'' b) ! j"
      unfolding bin_ptr_upd_def using j(1) by simp
    moreover have "set (snd x) \<subseteq> set (pointers (bin_ptr_upd i ptrs'' b) ! j)"
      unfolding bin_ptr_upd_def using j by (auto simp add: assms(2) nth_list_update)
    moreover have "(items (bin_ptr_upd i ptrs'' b) ! j, pointers (bin_ptr_upd i ptrs'' b) ! j) \<in> bin_ptr (bin_ptr_upd i ptrs'' b)"
      unfolding bin_ptr_def bin_ptr_upd_def using in_set_zip j(3,4) by (auto, fastforce)
    ultimately have "\<exists>y \<in> bin_ptr (bin_ptr_upd i ptrs'' b). fst x = fst y \<and> set (snd x) \<subseteq> set (snd y)"
      by (metis fst_conv snd_conv)
  }
  thus ?thesis
    unfolding subsumed_by_def by force
qed

lemma subsumed_bin_upd:
  assumes "length (items b) = length (pointers b)" 
  shows "bin_ptr b \<sqsubseteq> bin_ptr (bin_upd ip b)"
  unfolding bin_upd_def using subsumed_bin_ins subsumed_bin_ptr_upd apply (auto split: option.splits)
  apply (smt (verit, best) subsumed_bin_ins assms case_prod_conv)
  by (smt (verit, ccfv_threshold) subsumed_bin_ptr_upd assms case_prod_conv find_index_Some_iff_i)

lemma subsumed_bin_upds:
  assumes "length (items b) = length (pointers b)"
  shows "bin_ptr b \<sqsubseteq> bin_ptr (bin_upds ips b)"
  using assms
proof (induction ips arbitrary: b)
  case (Cons ip ips)
  have 0: "bin_ptr b \<sqsubseteq> bin_ptr (bin_upd ip b)"
    using subsumed_bin_upd[OF Cons.prems] by simp
  have "bin_ptr (bin_upd ip b) \<sqsubseteq> bin_ptr (bin_upds ips (bin_upd ip b))"
    using Cons by (meson length_items_pointers_bin_upd)
  hence 1: "bin_ptr (bin_upd ip b) \<sqsubseteq> bin_ptr (bin_upds (ip#ips) b)"
    by simp 
  show ?case
    using 0 1 subsumed_by_mono by blast
qed (auto simp: subsumed_by_def)

lemma subsumed_bin_upds_ips:
  assumes "length (items b) = length (pointers b)"
  shows "set ips \<sqsubseteq> bin_ptr (bin_upds ips b)"
  using assms
proof (induction ips arbitrary: b)
  case (Cons ip ips)
  have IH: "set ips \<sqsubseteq> bin_ptr (bin_upds (ip#ips) b)"
    by (simp add: Cons.IH Cons.prems length_items_pointers_bin_upd)
  obtain y where *: "y \<in> bin_ptr (bin_upd ip b)" "fst ip = fst y" "set (snd ip) \<subseteq> set (snd y)"
    using ex_subsumed_bin_upd Cons.prems by fastforce
  moreover have "bin_ptr (bin_upd ip b) \<sqsubseteq> bin_ptr (bin_upds ips (bin_upd ip b))"
    using subsumed_bin_upds Cons.prems length_items_pointers_bin_upd by blast
  ultimately have "\<exists>z \<in> bin_ptr (bin_upds ips (bin_upd ip b)). fst y = fst z \<and> set (snd y) \<subseteq> set (snd z)"
    unfolding subsumed_by_def by blast
  hence "\<exists>z \<in> bin_ptr (bin_upds ips (bin_upd ip b)). fst ip = fst z \<and> set (snd ip) \<subseteq> set (snd z)" 
    using * by auto
  thus ?case
    using IH by (simp add: subsumed_by_def)
qed (simp add: subsumed_by_def)

lemma subsumed_bins_upd_ips:
  assumes "length (items (bs!k)) = length (pointers (bs!k))" "k < length bs"
  shows "set ips \<sqsubseteq> bin_ptr (bins_upd bs k ips ! k)"
  by (simp add: subsumed_bin_upds_ips assms bins_upd_def)

lemma impossible_bin_ins:
  assumes "x \<notin> set (items b)" "\<exists>(y, ptrs') \<in> bin_ptr b. x = y \<and> set ptrs \<subseteq> set ptrs'"
  shows "False"
  using assms unfolding bin_ins_def bin_ptr_def by (auto, meson set_zip_leftD)

lemma bin_ptr_upd_eq:
  "set ptrs \<subseteq> set (pointers b ! i) \<Longrightarrow> bin_ptr_upd i ptrs b = b"
  unfolding bin_ptr_upd_def bin_ptr_def by (auto simp add: subsetD)

lemma bin_upd_eq:
  assumes "distinct (items b)" "\<exists>(y, ptrs) \<in> bin_ptr b. fst ip = y \<and> set (snd ip) \<subseteq> set ptrs"
  shows "bin_upd ip b = b"
proof (cases "find_index (\<lambda>x. x = fst ip) (items b) = None")
  case True
  hence "fst ip \<notin> set (items b)"
    by (simp add: find_index_None_iff)
  then show ?thesis
    using impossible_bin_ins assms(2) by blast
next
  case False
  then obtain i where i: "find_index (\<lambda>x. x = fst ip) (items b) = Some i"
    by blast
  hence "i < length (items b)" "items b ! i = fst ip"
    using find_index_Some_iff_i by fastforce+
  hence "\<nexists>j. j < length (items b) \<and> j \<noteq> i \<and> items b ! j = fst ip"
    using assms(1) by (metis nth_eq_iff_index_eq)
  hence "set (snd ip) \<subseteq> set (pointers b ! i)"
    using assms(2) unfolding bin_ptr_def by (metis (mono_tags, lifting) in_set_zip split_beta)
  thus ?thesis
    using i bin_ptr_upd_eq False by (auto simp: bin_upd_def)
qed

lemma bin_upds_eq:
  assumes "distinct (items b)" "set ips \<sqsubseteq> bin_ptr b"
  shows "bin_upds ips b = b"
  using assms
proof (induction ips arbitrary: b)
  case (Cons ip ips)
  have IH: "bin_upds ips b = b"
    using Cons by (simp add: subsumed_by_def)
  moreover have "\<exists>y \<in> bin_ptr b. fst ip = fst y \<and> set (snd ip) \<subseteq> set (snd y)"
    using Cons.prems(2) subsumed_by_def by (metis list.set_intros(1))
  ultimately have "bin_upd ip b = b"
    using Cons.prems(1) bin_upd_eq by (metis (mono_tags, lifting) case_prod_unfold)
  thus ?case
    using IH by simp
qed simp

lemma bins_upd_eq:
  assumes "distinct (items (bs!k))"
  shows "set ips \<sqsubseteq> bin_ptr (bs!k) \<Longrightarrow> bins_upd bs k ips = bs"
  unfolding bins_upd_def using bin_upds_eq assms by fastforce


subsection \<open>Main algorithm\<close>

definition Init_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "Init_it cfg inp = (
    let rs = filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg) in
    let b0 = map (\<lambda>r. (init_item r 0, [])) rs in
    let bs = replicate (length inp + 1) (Bin [] []) in
    bins_upd bs 0 b0)"

definition Scan_it :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a  \<Rightarrow> 'a item \<Rightarrow> nat \<Rightarrow> ('a item \<times> pointers) list" where
  "Scan_it k inp a x pre = (
    if inp!k = a then
      let x' = inc_item x (k+1) in
      [(x', [Pre pre])]
    else [])"

definition Predict_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a \<Rightarrow> ('a item \<times> pointers) list" where
  "Predict_it k cfg X = (
    let rs = filter (\<lambda>r. rule_head r = X) (\<RR> cfg) in
    map (\<lambda>r. (init_item r k, [])) rs)"

definition Complete_it :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> ('a item \<times> pointers) list" where
  "Complete_it k y bs red = (
    let orig = bs ! (item_origin y) in
    let is = filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items orig) in
    map (\<lambda>(x, pre). (inc_item x k, [PreRed (item_origin y) pre red])) is)"

partial_function (tailrec) \<pi>_it' :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a bins" where
  "\<pi>_it' k cfg inp bs i = (
    if i \<ge> length (items (bs ! k)) then bs
    else
      let x = items (bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow>
            if is_terminal cfg a then
              if k < length inp then bins_upd bs (k+1) (Scan_it k inp a x i)
              else bs
            else bins_upd bs k (Predict_it k cfg a)
        | None \<Rightarrow> bins_upd bs k (Complete_it k x bs i)
      in \<pi>_it' k cfg inp bs' (i+1))"

declare \<pi>_it'.simps[code]

definition \<pi>_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a bins" where
  "\<pi>_it k cfg inp bs = \<pi>_it' k cfg inp bs 0"

fun \<I>_it :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "\<I>_it 0 cfg inp = \<pi>_it 0 cfg inp (Init_it cfg inp)"
| "\<I>_it (Suc n) cfg inp = \<pi>_it (Suc n) cfg inp (\<I>_it n cfg inp)"

definition \<II>_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins" where
  "\<II>_it cfg inp = \<I>_it (length inp) cfg inp"


subsection \<open>Well-formed bins\<close>

lemma distinct_Scan_it:
  "distinct (map fst (Scan_it k inp a x pre))"
  unfolding Scan_it_def by simp

lemma distinct_Predict_it:
  "wf_cfg cfg \<Longrightarrow> distinct (map fst (Predict_it k cfg X))"
  unfolding Predict_it_def wf_cfg_defs by (auto simp: init_item_def rule_head_def distinct_map inj_on_def)

lemma inj_on_inc_item:
  "\<forall>x \<in> A. item_end x = l \<Longrightarrow> inj_on (\<lambda>x. inc_item x k) A"
  unfolding inj_on_def inc_item_def by (simp add: item.expand)
  
lemma distinct_Complete_it:
  assumes "wf_bins cfg inp bs" "item_origin y < length bs"
  shows "distinct (map fst (Complete_it k y bs red))"
proof -
  let ?orig = "bs ! (item_origin y)"
  let ?is = "filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"
  let ?is' = "map (\<lambda>(x, pre). (inc_item x k, [PreRed (item_origin y) pre red])) ?is"
  have wf: "wf_bin cfg inp (item_origin y) ?orig"
    using assms wf_bins_def by blast
  have 0: "\<forall>x \<in> set (map fst ?is). item_end x = (item_origin y)"
    using wf wf_bin_def wf_bin_items_def filter_is_subset filter_with_index_cong_filter by (metis in_mono)
  hence "distinct (items ?orig)"
    using wf unfolding wf_bin_def by blast
  hence "distinct (map fst ?is)"
    using filter_with_index_cong_filter distinct_filter by metis
  moreover have "map fst ?is' = map (\<lambda>x. inc_item x k) (map fst ?is)"
    by (induction ?is) auto
  moreover have "inj_on (\<lambda>x. inc_item x k) (set (map fst ?is))"
    using inj_on_inc_item 0 by blast
  ultimately have "distinct (map fst ?is')"
    using distinct_map by metis
  thus ?thesis
    unfolding Complete_it_def by simp
qed

lemma wf_bins_Scan_it':
  assumes "wf_bins cfg inp bs" "k < length bs" "x \<in> set (items (bs ! k))"
  assumes "k < length inp" "next_symbol x \<noteq> None" "y = inc_item x (k+1)"
  shows "wf_item cfg inp y \<and> item_end y = k+1"
  using assms wf_bins_kth_bin[OF assms(1-3)]
  unfolding wf_item_def inc_item_def next_symbol_def is_complete_def item_rule_body_def
  by (auto split: if_splits)

lemma wf_bins_Scan_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "x \<in> set (items (bs ! k))" "k < length inp" "next_symbol x \<noteq> None"
  shows "\<forall>y \<in> set (map fst (Scan_it k inp a x pre)). wf_item cfg inp y \<and> item_end y = (k+1)"
  using wf_bins_Scan_it'[OF assms] by (simp add: Scan_it_def)

lemma wf_bins_Predict_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "k \<le> length inp" "wf_cfg cfg"
  shows "\<forall>y \<in> set (map fst (Predict_it k cfg X)). wf_item cfg inp y \<and> item_end y = k"
  using assms by (auto simp: Predict_it_def wf_item_def wf_bins_def wf_bin_def init_item_def wf_cfg_defs)

lemma wf_item_inc_item:
  assumes "wf_item cfg inp x" "next_symbol x = Some a" "item_origin x \<le> k" "k \<le> length inp"
  shows "wf_item cfg inp (inc_item x k) \<and> item_end (inc_item x k) = k"
  using assms by (auto simp: wf_item_def inc_item_def item_rule_body_def next_symbol_def is_complete_def split: if_splits)

lemma wf_bins_Complete_it:
  assumes "wf_bins cfg inp bs" "k < length bs" "y \<in> set (items (bs ! k))"
  shows "\<forall>x \<in> set (map fst (Complete_it k y bs red)). wf_item cfg inp x \<and> item_end x = k"
proof -
  let ?orig = "bs ! (item_origin y)"
  let ?is = "filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"
  let ?is' = "map (\<lambda>(x, pre). (inc_item x k, [PreRed (item_origin y) pre red])) ?is"
  {
    fix x
    assume *: "x \<in> set (map fst ?is)"
    have "item_end x = item_origin y"
      using * assms wf_bins_kth_bin wf_item_def filter_with_index_cong_filter
      by (metis dual_order.strict_trans2 filter_is_subset subsetD)
    have "wf_item cfg inp x"
      using * assms wf_bins_kth_bin wf_item_def filter_with_index_cong_filter
      by (metis dual_order.strict_trans2 filter_is_subset subsetD)
    moreover have "next_symbol x = Some (item_rule_head y)"
      using * filter_set filter_with_index_cong_filter member_filter by metis
    moreover have "item_origin x \<le> k"
      using \<open>item_end x = item_origin y\<close> \<open>wf_item cfg inp x\<close> assms wf_bins_kth_bin wf_item_def
      by (metis dual_order.order_iff_strict dual_order.strict_trans1)
    moreover have "k \<le> length inp"
      using assms wf_bins_kth_bin wf_item_def by blast
    ultimately have "wf_item cfg inp (inc_item x k)" "item_end (inc_item x k) = k"
      by (simp_all add: wf_item_inc_item)
  }
  hence "\<forall>x \<in> set (map fst ?is'). wf_item cfg inp x \<and> item_end x = k"
    by (auto simp: fst_def)
  thus ?thesis
    unfolding Complete_it_def by presburger
qed

lemma distinct_ptrs_Scan_it:
  "distinct_ptrs (map snd (Scan_it k inp a x pre))"
  unfolding Scan_it_def distinct_ptrs_def by auto

lemma distinct_ptrs_Predict_it:
  "distinct_ptrs (map snd (Predict_it k cfg a))"
  unfolding Predict_it_def distinct_ptrs_def by auto

lemma distinct_ptrs_Complete_it:
  "distinct_ptrs (map snd (Complete_it k x bs red))"
  unfolding Complete_it_def distinct_ptrs_def by auto

lemma Ex_wf_bins:
  "\<exists>n bs inp cfg. n \<le> length inp \<and> length bs = Suc (length inp) \<and> wf_cfg cfg \<and> wf_bins cfg inp bs"
  apply (rule exI[where x="0"])
  apply (rule exI[where x="[Bin [] []]"])
  apply (rule exI[where x="[]"])
  apply (auto simp: wf_bins_def wf_bin_def wf_cfg_defs wf_bin_items_def distinct_ptrs_def split: prod.splits)
  by (metis cfg.sel distinct.simps(1) empty_iff empty_set inf_bot_right list.set_intros(1))

definition wellformed_bins :: "(nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins) set" where
  "wellformed_bins = { 
    (k, cfg, inp, bs) | k cfg inp bs.
      k \<le> length inp \<and>
      length bs = length inp + 1 \<and>
      wf_cfg cfg \<and>
      wf_bins cfg inp bs
  }"

typedef 'a wf_bins = "wellformed_bins::(nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins) set"
  morphisms from_wf_bins to_wf_bins
  using Ex_wf_bins by (auto simp: wellformed_bins_def)

lemma wellformed_bins_elim:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "k \<le> length inp \<and> k < length bs \<and> length bs = length inp + 1 \<and> wf_cfg cfg \<and> wf_bins cfg inp bs"
  using assms(1) from_wf_bins wellformed_bins_def by (smt (verit) Suc_eq_plus1 less_Suc_eq_le mem_Collect_eq prod.sel(1) snd_conv)

lemma wellformed_bins_intro:
  assumes "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
  shows "(k, cfg, inp, bs) \<in> wellformed_bins"
  by (simp add: assms wellformed_bins_def)

lemma wellformed_bins_Complete_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = None"
  shows "(k, cfg, inp, bins_upd bs k (Complete_it k x bs red)) \<in> wellformed_bins"
proof -
  have *: "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using wellformed_bins_elim assms(1) by metis+
  have x: "x \<in> set (items (bs ! k))"
    using assms(2,3) by simp
  have "item_origin x < length bs"
    using x wf_bins_kth_bin *(1,2,4) wf_item_def 
    by (metis One_nat_def add.right_neutral add_Suc_right dual_order.trans le_imp_less_Suc)
  hence "wf_bins cfg inp (bins_upd bs k (Complete_it k x bs red))"
    using *(1,2,4) Suc_eq_plus1 distinct_Complete_it distinct_ptrs_Complete_it le_imp_less_Suc wf_bins_Complete_it wf_bins_bins_upd x by metis
  thus ?thesis
    by (simp add: *(1-3) wellformed_bins_def)
qed

lemma wellformed_bins_Scan_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = Some a"
  assumes "is_terminal cfg a" "k < length inp"
  shows "(k, cfg, inp, bins_upd bs (k+1) (Scan_it k inp a x pre)) \<in> wellformed_bins"
proof -
  have *: "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using wellformed_bins_elim assms(1) by metis+
  have x: "x \<in> set (items(bs ! k))"
    using assms(2,3) by simp
  have "wf_bins cfg inp (bins_upd bs (k+1) (Scan_it k inp a x pre))"
    using * x assms(1,4,6) distinct_Scan_it distinct_ptrs_Scan_it wf_bins_Scan_it wf_bins_bins_upd wellformed_bins_elim
    by (metis option.discI)
  thus ?thesis
    by (simp add: *(1-3) wellformed_bins_def)
qed

lemma wellformed_bins_Predict_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = Some a" "\<not> is_terminal cfg a"
  shows "(k, cfg, inp, bins_upd bs k (Predict_it k cfg a)) \<in> wellformed_bins"
proof -
  have *: "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using wellformed_bins_elim assms(1) by metis+
  have x: "x \<in> set (items (bs ! k))"
    using assms(2,3) by simp
  hence "wf_bins cfg inp (bins_upd bs k (Predict_it k cfg a))"
    using * x assms(1,4) distinct_Predict_it distinct_ptrs_Predict_it wf_bins_Predict_it wf_bins_bins_upd wellformed_bins_elim by metis
  thus ?thesis
    by (simp add: *(1-3) wellformed_bins_def)
qed

fun earley_measure :: "nat \<times> 'a cfg \<times> 'a sentence \<times> 'a bins \<Rightarrow> nat \<Rightarrow> nat" where
  "earley_measure (k, cfg, inp, bs) i = card { x | x. wf_item cfg inp x \<and> item_end x = k } - i"

lemma \<pi>_it'_simps[simp]:
  "i \<ge> length (items (bs ! k)) \<Longrightarrow> \<pi>_it' k cfg inp bs i = bs"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = None \<Longrightarrow>
    \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (bins_upd bs k (Complete_it k x bs i)) (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    is_terminal cfg a \<Longrightarrow> k < length inp \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (bins_upd bs (k+1) (Scan_it k inp a x i)) (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    is_terminal cfg a \<Longrightarrow> \<not> k < length inp \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp bs (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    \<not> is_terminal cfg a \<Longrightarrow> \<pi>_it' k cfg inp bs i = \<pi>_it' k cfg inp (bins_upd bs k (Predict_it k cfg a)) (i+1)"
  by (subst \<pi>_it'.simps, simp)+

lemma \<pi>_it'_induct[case_names Base Complete Scan Pass Predict]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes base: "\<And>k cfg inp bs i. i \<ge> length (items (bs ! k)) \<Longrightarrow> P k cfg inp bs i"
  assumes complete: "\<And>k cfg inp bs i x. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = None \<Longrightarrow> P k cfg inp (bins_upd bs k (Complete_it k x bs i)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes scan: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal cfg a \<Longrightarrow> k < length inp \<Longrightarrow> 
            P k cfg inp (bins_upd bs (k+1) (Scan_it k inp a x i)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes pass: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> is_terminal cfg a \<Longrightarrow> \<not> k < length inp \<Longrightarrow>
            P k cfg inp bs (i+1) \<Longrightarrow> P k cfg inp bs i"
  assumes predict: "\<And>k cfg inp bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> \<not> is_terminal cfg a \<Longrightarrow> 
            P k cfg inp (bins_upd bs k (Predict_it k cfg a)) (i+1) \<Longrightarrow> P k cfg inp bs i"
  shows "P k cfg inp bs i"
  using assms(1)
proof (induction n\<equiv>"earley_measure (k, cfg, inp, bs) i" arbitrary: bs i rule: nat_less_induct)
  case 1
  have wf: "k \<le> length inp" "length bs = length inp + 1" "wf_cfg cfg" "wf_bins cfg inp bs"
    using "1.prems" wellformed_bins_elim by metis+
  hence k: "k < length bs"
    by simp
  have fin: "finite { x | x. wf_item cfg inp x \<and> item_end x = k }"
    using finiteness_UNIV_wf_item by fastforce
  show ?case
  proof cases
    assume "i \<ge> length (items (bs ! k))"
    then show ?thesis
      by (simp add: base)
  next
    assume a1: "\<not> i \<ge> length (items (bs ! k))"
    let ?x = "items (bs ! k) ! i"
    have x: "?x \<in> set (items (bs ! k))"
      using a1 by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "bins_upd bs k (Complete_it k ?x bs i)"
      have "item_origin ?x < length bs"
        using wf(4) k wf_bins_kth_bin wf_item_def x by (metis order_le_less_trans)
      hence wf_bins': "wf_bins cfg inp ?bs'"
        using wf_bins_Complete_it distinct_Complete_it distinct_ptrs_Complete_it wf(4) wf_bins_bins_upd k x by metis
      hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
        using wf(1,2,3) wellformed_bins_intro by fastforce
      have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
        using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
      have "i < length (items (?bs' ! k))"
        using a1 by (meson leI length_items_nth_bin_bins_upd order.trans)
      also have "... = card (set (items (?bs' ! k)))"
        using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def by (metis k length_bins_upd)
      also have "... \<le> card {x |x. wf_item cfg inp x \<and> item_end x = k}"
        using card_mono fin sub by blast
      finally have "card {x |x. wf_item cfg inp x \<and> item_end x = k} > i"
        by blast
      hence "earley_measure (k, cfg, inp, ?bs') (Suc i) < earley_measure (k, cfg, inp, bs) i"
        by simp
      thus ?thesis
        using 1 a1 a2 complete wf' by simp
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
          let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a ?x i)"
          have wf_bins': "wf_bins cfg inp ?bs'"
            using wf_bins_Scan_it distinct_Scan_it distinct_ptrs_Scan_it wf(1,4) wf_bins_bins_upd a2 a4 k x by metis
          hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
            using wf(1,2,3) wellformed_bins_intro by fastforce
          have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
            using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
          have "i < length (items (?bs' ! k))"
            using a1 by (meson leI length_items_nth_bin_bins_upd order.trans)
          also have "... = card (set (items (?bs' ! k)))"
            using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
            by (metis Suc_eq_plus1 le_imp_less_Suc length_bins_upd)
          also have "... \<le> card {x |x. wf_item cfg inp x \<and> item_end x = k}"
            using card_mono fin sub by blast
          finally have "card {x |x. wf_item cfg inp x \<and> item_end x = k} > i"
            by blast
          hence "earley_measure (k, cfg, inp, ?bs') (Suc i) < earley_measure (k, cfg, inp, bs) i"
            by simp
          thus ?thesis
            using 1 a1 a_def a3 a4 scan wf' by simp
        next
          assume a4: "\<not> k < length inp"
          have sub: "set (items (bs ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
            using wf(1,2,4) unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
          have "i < length (items (bs ! k))"
            using a1 by simp
          also have "... = card (set (items (bs ! k)))"
            using wf(1,2,4) distinct_card wf_bins_def wf_bin_def by (metis Suc_eq_plus1 le_imp_less_Suc)
          also have "... \<le> card {x |x. wf_item cfg inp x \<and> item_end x = k}"
            using card_mono fin sub by blast
          finally have "card {x |x. wf_item cfg inp x \<and> item_end x = k} > i"
            by blast
          hence "earley_measure (k, cfg, inp, bs) (Suc i) < earley_measure (k, cfg, inp, bs) i"
            by simp
          thus ?thesis
            using 1 a1 a3 a4 a_def pass by simp
        qed
      next
        assume a3: "\<not> is_terminal cfg a"
        let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
        have wf_bins': "wf_bins cfg inp ?bs'"
          using wf_bins_Predict_it distinct_Predict_it distinct_ptrs_Predict_it wf(1,3,4) wf_bins_bins_upd k x by metis
        hence wf': "(k, cfg, inp, ?bs') \<in> wellformed_bins"
          using wf(1,2,3) wellformed_bins_intro by fastforce
        have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item cfg inp x \<and> item_end x = k }"
          using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
        have "i < length (items (?bs' ! k))"
          using a1 by (meson leI length_items_nth_bin_bins_upd order.trans)
        also have "... = card (set (items (?bs' ! k)))"
          using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
          by (metis Suc_eq_plus1 le_imp_less_Suc length_bins_upd)
        also have "... \<le> card {x |x. wf_item cfg inp x \<and> item_end x = k}"
          using card_mono fin sub by blast
        finally have "card {x |x. wf_item cfg inp x \<and> item_end x = k} > i"
          by blast
        hence "earley_measure (k, cfg, inp, ?bs') (Suc i) < earley_measure (k, cfg, inp, bs) i"
          by simp
        thus ?thesis
          using 1 a1 a_def a3 a_def predict wf' by simp
      qed
    qed
  qed
qed

lemma wellformed_bins_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "(k, cfg, inp, \<pi>_it' k cfg inp bs i) \<in> wellformed_bins"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems wellformed_bins_Complete_it by blast
  thus ?case
    using Complete.IH Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems wellformed_bins_Scan_it by metis
  thus ?case
    using Scan.IH Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems wellformed_bins_Predict_it by metis
  thus ?case
    using Predict.IH Predict.hyps by simp
qed simp_all

lemma wellformed_bins_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "(k, cfg, inp, \<pi>_it k cfg inp bs) \<in> wellformed_bins"
  using assms by (simp add: \<pi>_it_def wellformed_bins_\<pi>_it')

lemma length_bins_\<pi>_it'[simp]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (\<pi>_it' k cfg inp bs i) = length bs"
  by (metis assms wellformed_bins_\<pi>_it' wellformed_bins_elim)

lemma length_bins_\<pi>_it[simp]:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (\<pi>_it k cfg inp bs) = length bs"
  using assms unfolding \<pi>_it_def by simp

lemma length_nth_bin_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "length (items (\<pi>_it' k cfg inp bs i ! l)) \<ge> length (items (bs ! l))"
  using length_items_nth_bin_bins_upd order_trans
  by (induction i rule: \<pi>_it'_induct[OF assms]) (auto, blast+)

lemma wf_bins_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "wf_bins cfg inp (\<pi>_it' k cfg inp bs i)"
  using assms wellformed_bins_\<pi>_it' wellformed_bins_elim by blast

lemma wf_bins_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "wf_bins cfg inp (\<pi>_it k cfg inp bs)"
  using assms \<pi>_it_def wf_bins_\<pi>_it' by metis

lemma kth_\<pi>_it'_bins_ptr_sub:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "j < length (pointers (bs ! l))"
  shows "set (pointers (bs ! l) ! j) \<subseteq> set (pointers (\<pi>_it' k cfg inp bs i ! l) ! j)"
  using assms(2)
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "set (pointers (bs ! l) ! j) \<subseteq> set (pointers (?bs' ! l) ! j)"
    using set_pointers_bins_upd Complete.prems by blast
  also have "set (pointers (?bs' ! l) ! j) \<subseteq> set (pointers (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j)"
    using Complete.IH Complete.prems length_pointers_nth_bin_bins_upd dual_order.strict_trans1 by blast
  finally show ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "set (pointers (bs ! l) ! j) \<subseteq> set (pointers (?bs' ! l) ! j)"
    using set_pointers_bins_upd Scan.prems by blast
  also have "set (pointers (?bs' ! l) ! j) \<subseteq> set (pointers (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j)"
    using Scan.IH Scan.prems length_pointers_nth_bin_bins_upd dual_order.strict_trans1 by blast
  finally show ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "set (pointers (bs ! l) ! j) \<subseteq> set (pointers (?bs' ! l) ! j)"
    using set_pointers_bins_upd Predict.prems by blast
  also have "set (pointers (?bs' ! l) ! j) \<subseteq> set (pointers (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j)"
    using Predict.IH Predict.prems length_pointers_nth_bin_bins_upd dual_order.strict_trans1 by blast
  finally show ?case
    using Predict.hyps by simp
qed simp_all

lemma kth_\<pi>_it'_bins:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  assumes "j < length (items (bs ! l))"
  shows "items (\<pi>_it' k cfg inp bs i ! l) ! j = items (bs ! l) ! j"
  using assms(2)
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "items (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Complete.IH Complete.prems length_items_nth_bin_bins_upd order.strict_trans2 by blast
  also have "... = items (bs ! l) ! j"
    using nth_bins_upd Complete.prems items_mth_bins_upd by metis
  finally show ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "items (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Scan.IH Scan.prems length_items_nth_bin_bins_upd order.strict_trans2 by blast
  also have "... = items (bs ! l) ! j"
    using items_mth_bins_upd nth_bins_upd Scan.prems by metis
  finally show ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "items (\<pi>_it' k cfg inp ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Predict.IH Predict.prems length_items_nth_bin_bins_upd order.strict_trans2 by blast
  also have "... = items (bs ! l) ! j"
    using items_mth_bins_upd nth_bins_upd Predict.prems by metis
  finally show ?case
    using Predict.hyps by simp
qed simp_all

lemma \<pi>_it'_kth_subsumed_by:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" "l < length bs"
  shows "bin_ptr (bs ! l) \<sqsubseteq> bin_ptr (\<pi>_it' k cfg inp bs i ! l)"
proof -
  have "wf_bins cfg inp bs"
    using assms wellformed_bins_elim by blast
  hence l: "length (items (bs ! l)) = length (pointers (bs ! l))"
    unfolding wf_bins_def wf_bin_def using assms(2) by blast
  {
    fix x
    assume *: "x \<in> bin_ptr (bs ! l)"
    obtain j where j: "fst x = items (bs ! l) ! j" "snd x = pointers (bs ! l) ! j" "j < length (items (bs ! l))"
      using * in_set_zip unfolding bin_ptr_def by metis
    let ?y = "items (\<pi>_it' k cfg inp bs i ! l) ! j"
    let ?ptrs' = "pointers (\<pi>_it' k cfg inp bs i ! l) ! j"
    have "j < length (pointers (bs ! l))"
      using j(3) l by auto
    hence "fst x = ?y" "set (snd x) \<subseteq> set ?ptrs'"
      using assms(1) j kth_\<pi>_it'_bins kth_\<pi>_it'_bins_ptr_sub by metis+
    moreover have "(?y, ?ptrs') \<in> bin_ptr (\<pi>_it' k cfg inp bs i ! l)"
      unfolding bin_ptr_def using l assms \<open>j < length (pointers (bs ! l))\<close> length_bins_\<pi>_it'
        length_nth_bin_\<pi>_it' wf_bin_def wf_bins_\<pi>_it' wf_bins_def
      by (smt (verit, ccfv_SIG) in_set_zip dual_order.strict_trans1 fst_conv snd_conv)
    ultimately have "\<exists>(y, ptrs') \<in> bin_ptr (\<pi>_it' k cfg inp bs i ! l). fst x = y \<and> set (snd x) \<subseteq> set ptrs'"
      by blast
  }
  thus ?thesis
    by (simp add: case_prod_beta subsumed_by_def)
qed

lemma nth_bin_sub_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "set (items (bs ! l)) \<subseteq> set (items (\<pi>_it' k cfg inp bs i ! l))"
proof standard
  fix x
  assume "x \<in> set (items (bs ! l))"
  then obtain j where *: "j < length (items (bs ! l))" "items (bs ! l) ! j = x"
    using in_set_conv_nth by metis
  have "x = items (\<pi>_it' k cfg inp bs i ! l) ! j"
    using kth_\<pi>_it'_bins assms * by metis
  moreover have "j < length (items (\<pi>_it' k cfg inp bs i ! l))"
    using assms *(1) length_nth_bin_\<pi>_it' less_le_trans by blast
  ultimately show "x \<in> set (items (\<pi>_it' k cfg inp bs i ! l))"
    by simp
qed

lemma nth_\<pi>_it'_eq:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "l < k \<Longrightarrow> \<pi>_it' k cfg inp bs i ! l = bs ! l"
  by (induction i rule: \<pi>_it'_induct[OF assms]) (auto simp: bins_upd_def nth_bins_upd)

lemma set_items_\<pi>_it'_eq:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins" 
  shows "l < k \<Longrightarrow> set (items (\<pi>_it' k cfg inp bs i ! l)) = set (items (bs ! l))"
  by (simp add: assms nth_\<pi>_it'_eq)

lemma bins_upto_k0_\<pi>_it'_eq:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "bins_upto (\<pi>_it k cfg inp bs) k 0 = bins_upto bs k 0"
  unfolding bins_upto_def bin_upto_def \<pi>_it_def using set_items_\<pi>_it'_eq assms nth_\<pi>_it'_eq by fastforce

lemma wellformed_bins_Init_it:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, Init_it cfg inp) \<in> wellformed_bins"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg)"
  let ?b0 = "map (\<lambda>r. (init_item r 0, [])) ?rs"
  let ?bs = "replicate (length inp + 1) (Bin [] [])"
  have "distinct (map fst ?b0)"
    using assms unfolding wf_bin_def wf_item_def wf_cfg_def distinct_rules_def
    by (auto simp: init_item_def distinct_map inj_on_def)
  moreover have "\<forall>x\<in>set (map fst ?b0). wf_item cfg inp x \<and> item_end x = 0"
    using assms unfolding wf_bin_def wf_item_def by (auto simp: init_item_def)
  moreover have "wf_bins cfg inp ?bs"
    unfolding wf_bins_def wf_bin_def wf_bin_items_def distinct_ptrs_def using less_Suc_eq_0_disj by fastforce
  moreover have "distinct_ptrs (map snd ?b0)"
    by (auto simp: distinct_ptrs_def)
  ultimately show ?thesis
    using wf_bins_bins_upd assms length_bins_upd length_replicate wellformed_bins_intro
    unfolding wf_bin_def Init_it_def by metis
qed

lemma length_bins_Init_it[simp]:
  "length (Init_it cfg inp) = length inp + 1"
  by (simp add: Init_it_def)

lemma wf_bins_Init_it:
  assumes "wf_cfg cfg"
  shows "wf_bins cfg inp (Init_it cfg inp)"
  using assms wellformed_bins_Init_it wellformed_bins_elim by blast

lemma wellformed_bins_\<I>_it[simp]:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "(k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
  using assms
proof (induction k)
  case 0
  have "(k, cfg, inp, Init_it cfg inp) \<in> wellformed_bins"
    using assms wellformed_bins_Init_it by blast
  thus ?case
    by (simp add: assms(2) wellformed_bins_Init_it wellformed_bins_\<pi>_it)
next
  case (Suc k)
  have "(Suc k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
    using Suc.IH Suc.prems(1) Suc_leD assms(2) wellformed_bins_elim wellformed_bins_intro by metis
  thus ?case
    by (simp add: wellformed_bins_\<pi>_it)
qed

lemma length_\<I>_it[simp]:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "length (\<I>_it k cfg inp) = length (Init_it cfg inp)"
  using assms wellformed_bins_\<I>_it wellformed_bins_elim by fastforce

lemma wf_bins_\<I>_it[simp]:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "wf_bins cfg inp (\<I>_it k cfg inp)"
  using assms wellformed_bins_\<I>_it wellformed_bins_elim by fastforce

lemma wellformed_bins_\<II>_it:
  "k \<le> length inp \<Longrightarrow> wf_cfg cfg \<Longrightarrow> (k, cfg, inp, \<II>_it cfg inp) \<in> wellformed_bins"
  by (simp add: \<II>_it_def wellformed_bins_intro)

lemma wf_bins_\<II>_it:
  "wf_cfg cfg \<Longrightarrow> wf_bins cfg inp (\<II>_it cfg inp)"
  by (simp add: \<II>_it_def)


subsection \<open>List to set\<close>

lemma Init_it_eq_Init:
  "bins (Init_it cfg inp) = Init cfg"
proof -
  let ?rs = "filter (\<lambda>r. rule_head r = \<SS> cfg) (\<RR> cfg)"
  let ?b0 = "map (\<lambda>r. init_item r 0) ?rs"
  let ?bs = "replicate (length inp + 1) (Bin [] [])"
  have "bins ?bs = {}"
    unfolding bins_def bins_upto_def set_bin_def bin_upto_def
    by (auto simp del: replicate_Suc)
  hence "bins (Init_it cfg inp) = set ?b0"
    by (auto simp: Init_it_def bins_bins_upd)
  thus ?thesis
    unfolding Init_def rule_head_def by auto
qed

lemma Scan_it_sub_Scan:
  assumes "wf_bins cfg inp bs" "bins bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs" "k < length inp"
  assumes "next_symbol x = Some a"
  shows "set (map fst (Scan_it k inp a x pre)) \<subseteq> Scan k inp I"
proof standard
  fix y
  assume *: "y \<in> set (map fst (Scan_it k inp a x pre))"
  have "x \<in> bin I k"
    using kth_bin_sub_bins assms(1-4) set_bin_def wf_bin_def wf_bins_def wf_bin_items_def bin_def by fast
  {
    assume #: "k < length inp" "inp!k = a"
    hence "y = inc_item x (k+1)"
      using * unfolding Scan_it_def by simp
    hence "y \<in> Scan k inp I"
      using \<open>x \<in> bin I k\<close> # assms(6) unfolding Scan_def by blast
  }
  thus "y \<in> Scan k inp I"
    using * assms(5) unfolding Scan_it_def by fastforce
qed

lemma Predict_it_sub_Predict:
  assumes "wf_bins cfg inp bs" "bins bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol x = Some X"
  shows "set (map fst (Predict_it k cfg X)) \<subseteq> Predict k cfg I"
proof standard
  fix y
  assume *: "y \<in> set (map fst (Predict_it k cfg X))"
  have "x \<in> bin I k"
    using kth_bin_sub_bins assms(1-4) set_bin_def wf_bin_def wf_bins_def bin_def wf_bin_items_def by fast
  let ?rs = "filter (\<lambda>r. rule_head r = X) (\<RR> cfg)"
  let ?xs = "map (\<lambda>r. init_item r k) ?rs"
  have "y \<in> set ?xs"
    using * unfolding Predict_it_def by simp
  then obtain r where "y = init_item r k" "rule_head r = X" "r \<in> set (\<RR> cfg)" "next_symbol x = Some (rule_head r)"
    using assms(5) by auto
  thus "y \<in> Predict k cfg I"
    unfolding Predict_def using \<open>x \<in> bin I k\<close> by blast
qed

lemma Complete_it_sub_Complete:
  assumes "wf_bins cfg inp bs" "bins bs \<subseteq> I" "y \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol y = None"
  shows "set (map fst (Complete_it k y bs red)) \<subseteq> Complete k I"
  thm Complete_it_def
proof standard
  fix x
  assume *: "x \<in> set (map fst (Complete_it k y bs red))"
  have "y \<in> bin I k"
    using kth_bin_sub_bins assms set_bin_def wf_bin_def wf_bins_def bin_def wf_bin_items_def by fast
  let ?orig = "bs ! item_origin y"
  let ?xs = "filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head y)) (items ?orig)"
  let ?xs' = "map (\<lambda>(x, pre). (inc_item x k, [PreRed (item_origin y) pre red])) ?xs"
  have 0: "item_origin y < length bs"
    using wf_bins_def wf_bin_def wf_item_def wf_bin_items_def assms(1,3,4)
    by (metis Orderings.preorder_class.dual_order.strict_trans1 leD not_le_imp_less)
  {
    fix z
    assume *: "z \<in> set (map fst ?xs)"
    have "next_symbol z = Some (item_rule_head y)"
      using * by (simp add: filter_with_index_cong_filter)
    moreover have "z \<in> bin I (item_origin y)"
      using 0 * assms(1,2) bin_def kth_bin_sub_bins wf_bins_kth_bin filter_with_index_cong_filter
      by (metis (mono_tags, lifting) filter_is_subset in_mono mem_Collect_eq)
    ultimately have "next_symbol z = Some (item_rule_head y)" "z \<in> bin I (item_origin y)"
      by simp_all
  }
  hence 1: "\<forall>z \<in> set (map fst ?xs). next_symbol z = Some (item_rule_head y) \<and> z \<in> bin I (item_origin y)"
    by blast
  obtain z where z: "x = inc_item z k" "z \<in> set (map fst ?xs)"
    using * unfolding Complete_it_def by (auto simp: rev_image_eqI)
  moreover have "next_symbol z = Some (item_rule_head y)" "z \<in> bin I (item_origin y)"
    using 1 z by blast+
  ultimately show "x \<in> Complete k I"
    using \<open>y \<in> bin I k\<close> assms(5) unfolding Complete_def next_symbol_def by (auto split: if_splits)
qed

lemma \<pi>_it'_sub_\<pi>:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "bins bs \<subseteq> I"
  shows "bins (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp I"
  using assms
proof (induction i arbitrary: I rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Base k cfg inp bs i)
  thus ?case
    using \<pi>_mono by fastforce
next
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by force
  hence "bins ?bs' \<subseteq> I \<union> Complete k I"
    using Complete_it_sub_Complete Complete.hyps(3) Complete.prems(1,2) bins_bins_upd wellformed_bins_elim by blast
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  ultimately have "bins (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp (I \<union> Complete k I)"
    using Complete.IH Complete.hyps by simp
  thus ?case
    using Complete_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by force
  hence "bins ?bs' \<subseteq> I \<union> Scan k inp I"
    using Scan_it_sub_Scan Scan.hyps(3,5) Scan.prems bins_bins_upd wellformed_bins_elim
    by (metis add_mono1 sup_mono)
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  ultimately have "bins (\<pi>_it' k cfg inp bs i) \<subseteq> \<pi> k cfg inp (I \<union> Scan k inp I)"
    using Scan.IH Scan.hyps by simp
  thus ?case
    using Scan_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
next
  case (Pass k cfg inp bs i x a)
  thus ?case
    by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by force
  hence "bins ?bs' \<subseteq> I \<union> Predict k cfg I"
    using Predict_it_sub_Predict Predict.hyps(3) Predict.prems bins_bins_upd wellformed_bins_elim
    by (metis sup_mono)
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  ultimately have "bins (\<pi>_it' k cfg inp bs i)  \<subseteq> \<pi> k cfg inp (I \<union> Predict k cfg I)"
    using Predict.IH Predict.hyps by simp
  thus ?case
    using Predict_\<pi>_mono \<pi>_mono \<pi>_sub_mono \<pi>_idem by (metis le_supI order_trans)
qed

lemma \<pi>_it_sub_\<pi>:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "bins bs \<subseteq> I"
  shows "bins (\<pi>_it k cfg inp bs) \<subseteq> \<pi> k cfg inp I"
  using assms \<pi>_it'_sub_\<pi> \<pi>_it_def by metis

lemma \<I>_it_sub_\<I>:
  assumes "k \<le> length inp" "wf_cfg cfg"
  shows "bins (\<I>_it k cfg inp) \<subseteq> \<I> k cfg inp"
  using assms
proof (induction k)
  case 0
  have "(k, cfg, inp, Init_it cfg inp) \<in> wellformed_bins"
    using assms(1) assms(2) wellformed_bins_Init_it by blast
  thus ?case
    by (simp add: Init_it_eq_Init \<pi>_it_sub_\<pi> assms(2) wellformed_bins_Init_it)
next
  case (Suc k)
  have "(Suc k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
    by (simp add: Suc.prems(1) Suc_leD assms(2) wellformed_bins_intro)
  thus ?case
    by (simp add: Suc.IH Suc.prems(1) Suc_leD \<pi>_it_sub_\<pi> assms(2))
qed

lemma \<II>_it_sub_\<II>:
  "wf_cfg cfg \<Longrightarrow> bins (\<II>_it cfg inp) \<subseteq> \<II> cfg inp"
  using \<I>_it_sub_\<I> \<II>_def \<II>_it_def by (metis dual_order.refl)


subsection \<open>Soundness\<close>

lemma sound_Scan_it:
  assumes "wf_bins cfg inp bs" "bins bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs" "k < length inp"
  assumes "next_symbol x = Some a" "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (map fst (Scan_it k inp a x i)))"
  using sound_Scan Scan_it_sub_Scan assms by (smt (verit, best) sound_items_def subsetD)

lemma sound_Predict_it:
  assumes "wf_bins cfg inp bs" "bins bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol x = Some X" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (map fst (Predict_it k cfg X)))"
  using sound_Predict Predict_it_sub_Predict sound_items_def assms by (smt (verit, ccfv_SIG) in_mono)

lemma sound_Complete_it:
  assumes "wf_bins cfg inp bs" "bins bs \<subseteq> I" "y \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol y = None" "wf_items cfg inp I" "sound_items cfg inp I"
  shows "sound_items cfg inp (set (map fst (Complete_it k y bs i)))"
  using sound_Complete Complete_it_sub_Complete sound_items_def assms by (metis (no_types, lifting) subsetD)

lemma sound_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins bs)"
  shows "sound_items cfg inp (bins (\<pi>_it' k cfg inp bs i))"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by force
  hence "sound_items cfg inp (set (map fst (Complete_it k x bs i)))"
    using sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  ultimately have "sound_items cfg inp (bins (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Complete.IH Complete.prems(2) length_bins_upd bins_bins_upd sound_items_def wellformed_bins_elim
    Suc_eq_plus1 Un_iff le_imp_less_Suc by metis
  thus ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by force
  hence "sound_items cfg inp (set (map fst (Scan_it k inp a x i)))"
    using sound_Scan_it \<pi>_mono Scan.hyps(3,5) Scan.prems(1,2) bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  ultimately have "sound_items cfg inp (bins (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Scan.IH sound_items_def Scan.hyps(5) Scan.prems(2) length_bins_upd bins_bins_upd wellformed_bins_elim
    by (metis UnE add_less_cancel_right )
  thus ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by force
  hence "sound_items cfg inp (set (map fst (Predict_it k cfg a)))"
    using sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems bins_bin_exists wellformed_bins_elim
          sound_\<pi> wf_bins_kth_bin wf_items_def by metis
  moreover have "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  ultimately have "sound_items cfg inp (bins (\<pi>_it' k cfg inp ?bs' (i + 1)))"
    using Predict.IH sound_items_def Predict.prems(2) length_bins_upd bins_bins_upd wellformed_bins_elim
    by (metis Suc_eq_plus1 UnE le_imp_less_Suc)
  thus ?case
    using Predict.hyps by simp
qed simp_all

lemma sound_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins bs)"
  shows "sound_items cfg inp (bins (\<pi>_it k cfg inp bs))"
  using sound_\<pi>_it' assms \<pi>_it_def by metis


subsection \<open>Set to list\<close>

lemma bin_bins_upto_bins_eq:
  assumes "wf_bins cfg inp bs" "k < length bs" "i \<ge> length (items (bs ! k))" "l \<le> k"
  shows "bin (bins_upto bs k i) l = bin (bins bs) l"
  unfolding bins_upto_def bins_def bin_def using assms nat_less_le
  by (auto simp: nth_list_update bin_upto_eq_set_bin wf_bins_kth_bin, metis less_trans, blast)

lemma impossible_complete_item:
  assumes "wf_cfg cfg" "wf_item cfg inp x" "sound_item cfg inp x"
  assumes "is_complete x"  "item_origin x = k" "item_end x = k" "nonempty_derives cfg"
  shows False
proof -
  have "derives cfg [item_rule_head x] []"
    using assms(3-6) by (simp add: slice_empty is_complete_def sound_item_def item_\<beta>_def )
  moreover have "is_nonterminal cfg (item_rule_head x)"
    using assms(1,2) unfolding wf_item_def item_rule_head_def rule_head_def 
    by (metis prod.collapse rule_nonterminal_type)
  ultimately show ?thesis
    using assms(7) nonempty_derives_def is_nonterminal_def by metis
qed

lemma Complete_Un_eq_terminal:
  assumes "next_symbol z = Some a" "is_terminal cfg a" "wf_items cfg inp I" "wf_item cfg inp z" "wf_cfg cfg"
  shows "Complete k (I \<union> {z}) = Complete k I"
proof (rule ccontr)
  assume "Complete k (I \<union> {z}) \<noteq> Complete k I"
  hence "Complete k I \<subset> Complete k (I \<union> {z})"
    using Complete_sub_mono by blast
  then obtain w x y  where *:
    "w \<in> Complete k (I \<union> {z})" "w \<notin> Complete k I" "w = inc_item x k"
    "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by fast
  show False
  proof (cases "x = z")
    case True
    have "is_nonterminal cfg (item_rule_head y)"
      using *(5,6) assms(1,3-5)
      apply (auto simp: wf_defs bin_def item_rule_head_def rule_head_def next_symbol_def)
      by (metis prod.exhaust_sel rule_nonterminal_type)
    thus ?thesis
      using True *(7) assms(1,2,5) is_terminal_nonterminal by fastforce
  next
    case False
    thus ?thesis
      using * assms(1) by (auto simp: next_symbol_def Complete_def bin_def)
  qed
qed

lemma Complete_Un_eq_nonterminal:
  assumes "next_symbol z = Some a" "is_nonterminal cfg a" "sound_items cfg inp I" "item_end z = k"
  assumes "wf_items cfg inp I" "wf_item cfg inp z" "wf_cfg cfg" "nonempty_derives cfg"
  shows "Complete k (I \<union> {z}) = Complete k I"
proof (rule ccontr)
  assume "Complete k (I \<union> {z}) \<noteq> Complete k I"
  hence "Complete k I \<subset> Complete k (I \<union> {z})"
    using Complete_sub_mono by blast
  then obtain w x y where *:
    "w \<in> Complete k (I \<union> {z})" "w \<notin> Complete k I" "w = inc_item x k"
    "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by fast
  consider (A) "x = z" | (B) "y = z" | "\<not> (x = z \<or> y = z)"
    by blast
  thus False
  proof cases
    case A
    have "item_origin y = k"
      using *(4) A assms(4) by (auto simp: bin_def)
    moreover have "item_end y = k"
      using *(5) bin_def by blast
    moreover have "sound_item cfg inp y"
      using *(5,6) assms(1,3) by (auto simp: bin_def next_symbol_def sound_items_def)
    moreover have "wf_item cfg inp y"
      using *(5) assms(5,6) wf_items_def by (auto simp: bin_def)
    ultimately show ?thesis
      using impossible_complete_item *(6) assms(7,8) by blast
  next
    case B
    thus ?thesis
      using *(6) assms(1) by (auto simp: next_symbol_def)
  next
    case 3
    thus ?thesis
      using *(2-7) Complete_def by (auto simp: bin_def; blast)
  qed
qed

lemma wf_item_in_kth_bin:
  "wf_bins cfg inp bs \<Longrightarrow> x \<in> bins bs \<Longrightarrow> item_end x = k \<Longrightarrow> x \<in> set (items (bs ! k))"
  using bins_bin_exists wf_bins_kth_bin wf_bins_def by blast

lemma Complete_bins_upto_eq_bins:
  assumes "wf_bins cfg inp bs" "k < length bs" "i \<ge> length (items (bs ! k))"
  shows "Complete k (bins_upto bs k i) = Complete k (bins bs)"
proof -
  have "\<And>l. l \<le> k \<Longrightarrow> bin (bins_upto bs k i) l = bin (bins bs) l"
    using bin_bins_upto_bins_eq[OF assms] by blast
  moreover have "wf_items cfg inp (bins bs)"
    using assms(1) wf_bins_impl_wf_items by metis
  ultimately show ?thesis
    unfolding Complete_def bin_def wf_items_def wf_item_def by auto
qed

lemma Complete_sub_bins_Un_Complete_it:
  assumes "Complete k I \<subseteq> bins bs" "I \<subseteq> bins bs" "is_complete z" "wf_bins cfg inp bs" "wf_item cfg inp z"
  shows "Complete k (I \<union> {z}) \<subseteq> bins bs \<union> set (map fst (Complete_it k z bs red))"
proof standard
  fix w
  assume "w \<in> Complete k (I \<union> {z})"
  then obtain x y where *:
    "w = inc_item x k" "x \<in> bin (I \<union> {z}) (item_origin y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (item_rule_head y)"
    unfolding Complete_def by blast
  consider (A) "x = z" | (B) "y = z" | "\<not> (x = z \<or> y = z)"
    by blast
  thus "w \<in> bins bs \<union> set (map fst (Complete_it k z bs red))"
  proof cases
    case A
    thus ?thesis
      using *(5) assms(3) by (auto simp: next_symbol_def)
  next
    case B
    let ?orig = "bs ! item_origin z"
    let ?is = "filter_with_index (\<lambda>x. next_symbol x = Some (item_rule_head z)) (items ?orig)"
    have "x \<in> bin I (item_origin y)"
      using B *(2) *(5) assms(3) by (auto simp: next_symbol_def bin_def)
    moreover have "bin I (item_origin z) \<subseteq> set (items (bs ! item_origin z))"
      using wf_item_in_kth_bin assms(2,4) bin_def by blast
    ultimately have "x \<in> set (map fst ?is)"
      using *(5) B set_bin_def by (simp add: filter_with_index_cong_filter in_mono)
    thus ?thesis
      unfolding Complete_it_def *(1) by (auto simp: fst_def rev_image_eqI)
  next
    case 3
    thus ?thesis
      using * assms(1) Complete_def by (auto simp: bin_def; blast)
  qed
qed

lemma Complete_it_eq_item_origin:
  "bs ! item_origin y = bs' ! item_origin y \<Longrightarrow> Complete_it k y bs red = Complete_it k y bs' red"
  by (auto simp: Complete_it_def)

lemma kth_bin_bins_upto_empty:
  assumes "wf_bins cfg inp bs" "k < length bs"
  shows "bin (bins_upto bs k 0) k = {}"
proof -
  {
    fix x
    assume "x \<in> bins_upto bs k 0"
    then obtain l where "x \<in> set (items (bs ! l))" "l < k"
      unfolding bins_upto_def bin_upto_def by blast
    hence "item_end x = l"
      using wf_bins_kth_bin assms by fastforce
    hence "item_end x < k"
      using \<open>l < k\<close> by blast
  }
  thus ?thesis
    by (auto simp: bin_def)
qed

lemma \<pi>_it'_mono:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  shows "bins bs \<subseteq> bins (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  hence "bins bs \<subseteq> bins ?bs'"
    using length_bins_upd bins_bins_upd wellformed_bins_elim by (metis Un_upper1)
  also have "... \<subseteq> bins (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using wf Complete.IH by blast
  finally show ?case
    using Complete.hyps by simp
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  hence "bins bs \<subseteq> bins ?bs'"
    using Scan.hyps(5) length_bins_upd bins_bins_upd wellformed_bins_elim
    by (metis add_mono1 sup_ge1)
  also have "... \<subseteq> bins (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using wf Scan.IH by blast
  finally show ?case
    using Scan.hyps by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  hence "bins bs \<subseteq> bins ?bs'"
    using length_bins_upd bins_bins_upd wellformed_bins_elim by (metis sup_ge1)
  also have "... \<subseteq> bins (\<pi>_it' k cfg inp ?bs' (i + 1))"
    using wf Predict.IH by blast
  finally show ?case
    using Predict.hyps by simp
qed simp_all

lemma \<pi>_step_sub_\<pi>_it':
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_upto bs k i) \<subseteq> bins bs"
  assumes "sound_items cfg inp (bins bs)" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi>_step k cfg inp (bins bs) \<subseteq> bins (\<pi>_it' k cfg inp bs i)"
  using assms
proof (induction i rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Base k cfg inp bs i)
  have "bin (bins bs) k = bin (bins_upto bs k i) k"
    using Base.hyps Base.prems(1) bin_bins_upto_bins_eq wellformed_bins_elim by blast
  thus ?case
    using Scan_bin_absorb Predict_bin_absorb Complete_bins_upto_eq_bins wellformed_bins_elim
      Base.hyps Base.prems(1,2,3,5) \<pi>_step_def Complete_\<pi>_step_mono Predict_\<pi>_step_mono Scan_\<pi>_step_mono \<pi>_it'_mono
    by (metis (no_types, lifting) Un_assoc sup.orderE)
next
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by auto
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  have sound: "sound_items cfg inp (set (map fst (Complete_it k x bs i)))"
    using x sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  have "Scan k inp (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Scan k inp (bins_upto ?bs' k (i + 1)) = Scan k inp (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Complete.hyps(1) bins_upto_Suc_Un length_items_nth_bin_bins_upd by (metis less_le_trans not_le_imp_less)
    also have "... = Scan k inp (bins_upto bs k i \<union> {x})"
      using Complete.hyps(1,2) Complete.prems(1) items_mth_bins_upd bins_upto_kth_nth_id wellformed_bins_elim
      by (metis dual_order.refl not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> Scan k inp {x}"
      using Complete.prems(2,3) Scan_Un Scan_\<pi>_step_mono by fastforce
    also have "... = bins bs"
      using Complete.hyps(3) by (auto simp: Scan_def bin_def)
    finally show ?thesis
      using Complete.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  moreover have "Predict k cfg (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Predict k cfg (bins_upto ?bs' k (i + 1)) = Predict k cfg (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Complete.hyps(1) bins_upto_Suc_Un length_items_nth_bin_bins_upd by (metis less_le_trans not_le_imp_less)
    also have "... = Predict k cfg (bins_upto bs k i \<union> {x})"
      using Complete.hyps(1,2) Complete.prems(1) items_mth_bins_upd bins_upto_kth_nth_id wellformed_bins_elim
      by (metis eq_imp_le linorder_le_less_linear)
    also have "... \<subseteq> bins bs \<union> Predict k cfg {x}"
      using Complete.prems(2,3) Predict_Un Predict_\<pi>_step_mono by blast
    also have "... = bins bs"
      using Complete.hyps(3) by (auto simp: Predict_def bin_def)
    finally show ?thesis
      using Complete.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  moreover have "Complete k (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Complete k (bins_upto ?bs' k (i + 1)) = Complete k (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un length_items_nth_bin_bins_upd Complete.hyps(1) by (metis less_le_trans not_le_imp_less)
    also have "... = Complete k (bins_upto bs k i \<union> {x})"
      using items_mth_bins_upd Complete.hyps(1,2) bins_upto_kth_nth_id Complete.prems(1) wellformed_bins_elim
      by (metis leI le_refl)
    also have "... \<subseteq> bins bs \<union> set (map fst (Complete_it k x bs i))"
      using Complete_sub_bins_Un_Complete_it Complete.hyps(3) Complete.prems(1,2,3) next_symbol_def
        bins_upto_sub_bins wf_bins_kth_bin x Complete_\<pi>_step_mono wellformed_bins_elim
      by (smt (verit, best) option.distinct(1) subset_trans)
    finally show ?thesis
      using Complete.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  ultimately have "\<pi>_step k cfg inp (bins ?bs') \<subseteq> bins (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Complete.IH Complete.prems sound wf \<pi>_step_def bins_upto_sub_bins
          wellformed_bins_elim bins_bins_upd sound_items_def
    by (metis UnE sup.boundedI)
  thus ?case
    using Complete.hyps Complete.prems(1) \<pi>_it'_simps(2) \<pi>_step_sub_mono bins_bins_upd wellformed_bins_elim
    by (smt (verit, best) sup.coboundedI2 sup.orderE sup_ge1)
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have x: "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by auto
  hence sound: "sound_items cfg inp (set (map fst (Scan_it k inp a x i)))"
    using sound_Scan_it \<pi>_mono Scan.hyps(3,5) Scan.prems(1,2,3) bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  have "Scan k inp (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Scan k inp (bins_upto ?bs' k (i + 1)) = Scan k inp (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un Scan.hyps(1) nth_bins_upd
      by (metis Groups.monoid_add_class.add.right_neutral One_nat_def add_Suc_right lessI less_not_refl not_le_imp_less)
    also have "... = Scan k inp (bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(1,2) nth_bins_upd bins_upto_kth_nth_id wellformed_bins_elim
      by (metis Suc_eq_plus1 add_less_cancel_right le_add1 lessI less_not_refl not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> Scan k inp {x}"
      using Scan.prems(2,3) Scan_Un Scan_\<pi>_step_mono by fastforce
    finally have *: "Scan k inp (bins_upto ?bs' k (i + 1)) \<subseteq> bins bs \<union> Scan k inp {x}" .
    show ?thesis
    proof cases
      assume a1: "inp!k = a"
      hence "Scan k inp {x} = {inc_item x (k+1)}"
        using Scan.hyps(1-3,5) Scan.prems(1,2) wellformed_bins_elim apply (auto simp: Scan_def bin_def)
        using wf_bins_kth_bin x by blast
      hence "Scan k inp (bins_upto ?bs' k (i + 1)) \<subseteq> bins bs \<union> {inc_item x (k+1)}"
        using * by blast
      also have "... = bins bs \<union> set (map fst (Scan_it k inp a x i))"
        using Scan_it_def a1 Scan.hyps(5)
        by (metis (no_types, lifting) empty_set fst_conv list.simps(15) list.simps(8) list.simps(9))
      also have "... = bins ?bs'"
        using Scan.hyps(5) Scan.prems(1) wellformed_bins_elim bins_bins_upd by (metis add_mono1)
      finally show ?thesis .
    next
      assume a1: "\<not> inp!k = a"
      hence "Scan k inp {x} = {}"
        using Scan.hyps(3) by (auto simp: Scan_def bin_def)
      hence "Scan k inp (bins_upto ?bs' k (i + 1)) \<subseteq> bins bs"
        using * by blast
      also have "... \<subseteq> bins ?bs'"
        using Scan.hyps(5) Scan.prems(1) wellformed_bins_elim bins_bins_upd
        by (metis Un_left_absorb add_strict_right_mono subset_Un_eq)
      finally show ?thesis .
    qed
  qed
  moreover have "Predict k cfg (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Predict k cfg (bins_upto ?bs' k (i + 1)) = Predict k cfg (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un Scan.hyps(1) nth_bins_upd by (metis Suc_eq_plus1 lessI less_not_refl not_le_imp_less)
    also have "... = Predict k cfg (bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(1,2) nth_bins_upd bins_upto_kth_nth_id wellformed_bins_elim
      by (metis Suc_eq_plus1 add_less_cancel_right le_add1 lessI less_not_refl not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> Predict k cfg {x}"
      using Scan.prems(2,3) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = bins bs"
      using Scan.hyps(3,4) Scan.prems(1) is_terminal_nonterminal wellformed_bins_elim
      by (auto simp: Predict_def bin_def rule_head_def, fastforce) 
    finally show ?thesis
      using Scan.hyps(5) Scan.prems(1) by (simp add: bins_bins_upd sup.coboundedI1 wellformed_bins_elim)
  qed
  moreover have "Complete k (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Complete k (bins_upto ?bs' k (i + 1)) = Complete k (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un Scan.hyps(1) nth_bins_upd by (metis Suc_eq_plus1 lessI less_not_refl not_le_imp_less)
    also have "... = Complete k (bins_upto bs k i \<union> {x})"
      using Scan.hyps(1,2,5) Scan.prems(1,2) nth_bins_upd bins_upto_kth_nth_id wellformed_bins_elim
      by (metis Suc_eq_plus1 add_less_cancel_right le_add1 lessI less_not_refl not_le_imp_less)
    also have "... = Complete k (bins_upto bs k i)"
      using Complete_Un_eq_terminal Scan.hyps(3,4) Scan.prems bins_upto_sub_bins subset_iff
            wf_bins_impl_wf_items wf_bins_kth_bin wf_items_def x wellformed_bins_elim
      by (smt (verit, ccfv_threshold))
    finally show ?thesis
      using Scan.hyps(5) Scan.prems(1,2,3) Complete_\<pi>_step_mono by (auto simp: bins_bins_upd wellformed_bins_elim, blast)
  qed
  ultimately have "\<pi>_step k cfg inp (bins ?bs') \<subseteq> bins (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Scan.IH Scan.prems Scan.hyps(5) sound wf \<pi>_step_def bins_upto_sub_bins wellformed_bins_elim
          bins_bins_upd sound_items_def by (metis UnE add_mono1 le_supI)
  thus ?case
    using \<pi>_step_sub_mono \<pi>_it'_simps(3) Scan.hyps Scan.prems(1) wellformed_bins_elim bins_bins_upd
    by (smt (verit, ccfv_SIG) add_mono1 sup.cobounded1 sup.coboundedI2 sup.orderE)
next
  case (Pass k cfg inp bs i x a)
  have x: "x \<in> set (items (bs ! k))"
    using Pass.hyps(1,2) by auto
  have "Scan k inp (bins_upto bs k (i + 1)) \<subseteq> bins bs"
    using Scan_def Pass.hyps(5) by auto
  moreover have "Predict k cfg (bins_upto bs k (i + 1)) \<subseteq> bins bs"
  proof -
    have "Predict k cfg (bins_upto bs k (i + 1)) = Predict k cfg (bins_upto bs k i \<union> {items (bs ! k) ! i})"
      using bins_upto_Suc_Un Pass.hyps(1) by (metis leI)
    also have "... = Predict k cfg (bins_upto bs k i \<union> {x})"
      using Pass.hyps(1,2,5) nth_bins_upd bins_upto_kth_nth_id by simp
    also have "... \<subseteq> bins bs \<union> Predict k cfg {x}"
      using Pass.prems(2) Predict_Un Predict_\<pi>_step_mono by blast
    also have "... = bins bs"
      using Pass.hyps(3,4) Pass.prems(1) is_terminal_nonterminal wellformed_bins_elim 
      by (auto simp: Predict_def bin_def rule_head_def, fastforce)
    finally show ?thesis
      using bins_bins_upd Pass.hyps(5) Pass.prems(3) by auto
  qed
  moreover have "Complete k (bins_upto bs k (i + 1)) \<subseteq> bins bs"
  proof -
    have "Complete k (bins_upto bs k (i + 1)) = Complete k (bins_upto bs k i \<union> {x})"
      using bins_upto_Suc_Un Pass.hyps(1,2) by (metis linorder_not_less)
    also have "... = Complete k (bins_upto bs k i)"
      using Complete_Un_eq_terminal Pass.hyps Pass.prems bins_upto_sub_bins subset_iff 
            wf_bins_impl_wf_items wf_items_def wf_bins_kth_bin x wellformed_bins_elim by (smt (verit, best))
    finally show ?thesis
      using Pass.prems(1,2) Complete_\<pi>_step_mono wellformed_bins_elim by blast
  qed
  ultimately have "\<pi>_step k cfg inp (bins bs) \<subseteq> bins (\<pi>_it' k cfg inp bs (i+1))"
    using Pass.IH Pass.prems \<pi>_step_def bins_upto_sub_bins wellformed_bins_elim
    by (metis le_sup_iff)
  thus ?case
    using bins_bins_upd Pass.hyps Pass.prems by simp
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have "k \<ge> length inp \<or> \<not> inp!k = a"
    using Predict.hyps(4) Predict.prems(4) is_word_is_terminal leI by blast
  have x: "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by auto
  hence sound: "sound_items cfg inp (set (map fst (Predict_it k cfg a)))"
    using sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems bins_bin_exists wellformed_bins_elim
          sound_\<pi> wf_bins_kth_bin wf_items_def by metis
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  have len: "i < length (items (?bs' ! k))"
    using length_items_nth_bin_bins_upd Predict.hyps(1) by (metis leI order_less_le_trans)
  have "item_rule x \<in> set (\<RR> cfg)"
    using Predict.prems(1) wf_bins_kth_bin x wf_item_def wellformed_bins_elim by blast
  hence "\<forall>s \<in> set (item_rule_body x). s \<in> set (\<NN> cfg) \<union> set (\<TT> cfg)"
    using Predict.prems(1) wellformed_bins_elim by (auto simp: wf_cfg_defs item_rule_body_def rule_body_def; fastforce)
  hence "is_terminal cfg a \<or> is_nonterminal cfg a"
    using Predict.hyps(3) by (auto simp: next_symbol_def is_complete_def is_nonterminal_def is_terminal_def split: if_splits)
  hence nonterm: "is_nonterminal cfg a"
    using Predict.hyps(4) by blast
  have "Scan k inp (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Scan k inp (bins_upto ?bs' k (i + 1)) = Scan k inp (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Predict.hyps(1) bins_upto_Suc_Un length_items_nth_bin_bins_upd by (metis less_le_trans not_le_imp_less)
    also have "... = Scan k inp (bins_upto bs k i \<union> {x})"
      using Predict.hyps(1,2) Predict.prems(1) items_mth_bins_upd bins_upto_kth_nth_id wellformed_bins_elim
      by (metis less_not_refl not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> Scan k inp {x}"
      using Predict.prems(2,3) Scan_Un Scan_\<pi>_step_mono by fastforce
    also have "... = bins bs"
      using Predict.hyps(3) \<open>length inp \<le> k \<or> inp ! k \<noteq> a\<close> by (auto simp: Scan_def bin_def)
    finally show ?thesis
      using Predict.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  moreover have "Predict k cfg (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Predict k cfg (bins_upto ?bs' k (i + 1)) = Predict k cfg (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Predict.hyps(1) bins_upto_Suc_Un length_items_nth_bin_bins_upd by (metis less_le_trans not_le_imp_less)
    also have "... = Predict k cfg (bins_upto bs k i \<union> {x})"
      using Predict.hyps(1,2) Predict.prems(1) items_mth_bins_upd bins_upto_kth_nth_id wellformed_bins_elim
      by (metis leI less_or_eq_imp_le)
    also have "... \<subseteq> bins bs \<union> Predict k cfg {x}"
      using Predict.prems(2,3) Predict_Un Predict_\<pi>_step_mono by fastforce
    also have "... = bins bs \<union> set (map fst (Predict_it k cfg a))"
      using Predict.hyps Predict.prems(1-3) wellformed_bins_elim apply (auto simp: Predict_def Predict_it_def bin_def)
      using wf_bins_kth_bin x by blast
    finally show ?thesis
      using Predict.prems(1) wellformed_bins_elim bins_bins_upd by blast
  qed
  moreover have "Complete k (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Complete k (bins_upto ?bs' k (i + 1)) = Complete k (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un len by force
    also have "... = Complete k (bins_upto bs k i \<union> {x})"
      using items_mth_bins_upd Predict.hyps(1,2) Predict.prems(1) bins_upto_kth_nth_id wellformed_bins_elim
      by (metis leI nle_le)
    also have "... = Complete k (bins_upto bs k i)"
      using Complete_Un_eq_nonterminal[OF Predict.hyps(3) nonterm] Predict.prems bins_upto_sub_bins 
            sound_items_def subset_eq wf_bins_kth_bin x wf_bins_impl_wf_items wf_items_def wellformed_bins_elim
      by metis
    finally show ?thesis
      using bins_bins_upd Predict.prems(1,2,3) Complete_\<pi>_step_mono wellformed_bins_elim
      by (metis Un_upper1 dual_order.trans)
  qed
  ultimately have "\<pi>_step k cfg inp (bins ?bs') \<subseteq> bins (\<pi>_it' k cfg inp ?bs' (i+1))"
    using Predict.IH Predict.prems sound wf \<pi>_step_def bins_upto_sub_bins 
          bins_bins_upd sound_items_def wellformed_bins_elim by (metis UnE le_supI)
  thus ?case
    using \<pi>_step_sub_mono \<pi>_it'_simps(5) Predict.hyps Predict.prems(1) wellformed_bins_elim
    by (smt (verit, ccfv_SIG) bins_bins_upd sup.coboundedI2 sup.orderE sup_ge1)
qed

lemma \<pi>_step_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_upto bs k 0) \<subseteq> bins bs"
  assumes "sound_items cfg inp (bins bs)" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi>_step k cfg inp (bins bs) \<subseteq> bins (\<pi>_it k cfg inp bs)"
  using assms \<pi>_step_sub_\<pi>_it' \<pi>_it_def by metis

lemma \<pi>_it'_idem:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "i \<le> j" "sound_items cfg inp (bins bs)" "nonempty_derives cfg"
  shows "\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j = \<pi>_it' k cfg inp bs i"
  using assms
proof (induction i arbitrary: j rule: \<pi>_it'_induct[OF assms(1), case_names Base Complete Scan Pass Predict])
  case (Complete k cfg inp bs i x)
  let ?bs' = "bins_upd bs k (Complete_it k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete.hyps(1,2) by auto
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Complete.hyps Complete.prems(1) wellformed_bins_Complete_it by blast
  have "sound_items cfg inp (set (map fst (Complete_it k x bs i)))"
    using x sound_Complete_it \<pi>_mono Complete.hyps(3) Complete.prems bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  hence sound: "sound_items cfg inp (bins ?bs')"
    by (metis Complete.prems(1) Complete.prems(3) UnE bins_bins_upd sound_items_def wellformed_bins_elim)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using wf sound Complete \<pi>_it'_simps(2) by metis
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Complete.prems(2) by simp
    have "\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j"
      using \<pi>_it'_simps(2) Complete.hyps(1-3) by simp
    also have "... = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_\<pi>_it' length_items_nth_bin_bins_upd order_trans wf by blast
      hence 0: "\<not> length (items (?bs'' ! k)) \<le> j"
        using \<open>i = j\<close> Complete.hyps(1) by linarith
      have "x = items (?bs' ! k) ! j"
        using \<open>i = j\<close> items_mth_bins_upd Complete.hyps(1,2) by (metis not_le_imp_less)
      hence 1: "x = items (?bs'' ! k) ! j"
        using \<open>i = j\<close> kth_\<pi>_it'_bins Complete.hyps Complete.prems(1) \<pi>_it'_simps(2) leI by metis
      have "\<pi>_it' k cfg inp ?bs'' j = \<pi>_it' k cfg inp (bins_upd ?bs'' k (Complete_it k x ?bs'' i)) (j+1)"
        using \<pi>_it'_simps(2) 0 1 Complete.hyps(1,3) Complete.prems(2) \<open>i = j\<close> by blast
      moreover have "bins_upd ?bs'' k (Complete_it k x ?bs'' i) = ?bs''"
      proof -
        have "k < length bs"
          using Complete.prems(1) wellformed_bins_elim by blast
        have 0: "set (Complete_it k x bs i) = set (Complete_it k x ?bs'' i)"
        proof (cases "item_origin x = k")
          case True
          thus ?thesis
            using impossible_complete_item kth_bin_sub_bins Complete.hyps(3) Complete.prems wellformed_bins_elim
              wf_bins_kth_bin x sound_items_def next_symbol_def by (metis option.distinct(1) subsetD)
        next
          case False
          hence "item_origin x < k"
            using x Complete.prems(1) wf_bins_kth_bin wf_item_def nat_less_le by (metis wellformed_bins_elim)
          hence "bs ! item_origin x = ?bs'' ! item_origin x"
            using False nth_bins_upd nth_\<pi>_it'_eq wf by metis
          thus ?thesis
            using Complete_it_eq_item_origin by metis
        qed
        have "set (Complete_it k x bs i) \<sqsubseteq> bin_ptr (?bs' ! k)"
          using subsumed_bins_upd_ips Complete.prems(1) \<open>k < length bs\<close> wellformed_bins_elim wf_bin_def wf_bins_def by fast
        hence 1: "set (Complete_it k x ?bs'' i) \<sqsubseteq> bin_ptr (?bs' ! k)"
          using 0 by simp
        have 2: "bin_ptr (?bs' ! k) \<sqsubseteq> bin_ptr (?bs'' ! k)"
          by (simp add: \<open>k < length bs\<close> \<pi>_it'_kth_subsumed_by wf)
        have 3: "set (Complete_it k x ?bs'' i) \<sqsubseteq> bin_ptr (?bs'' ! k)"
          using 1 2 subsumed_by_mono by blast
        moreover have "distinct (items (?bs'' ! k))"
          using \<open>k < length bs\<close> length_bins_\<pi>_it' length_bins_upd wf wf_bin_def wf_bins_\<pi>_it' wf_bins_def by metis
        ultimately show ?thesis
          using bins_upd_eq by blast
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k cfg inp ?bs' (i + 1)"
      using Complete.IH[OF wf _ sound Complete.prems(4)] \<open>i = j\<close> by blast
    finally show ?thesis
      using Complete.hyps by simp
  qed
next
  case (Scan k cfg inp bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan_it k inp a x i)"
  have x: "x \<in> set (items (bs ! k))"
    using Scan.hyps(1,2) by auto
  hence "sound_items cfg inp (set (map fst (Scan_it k inp a x i)))"
    using sound_Scan_it \<pi>_mono Scan.hyps(3,5) Scan.prems(1,2,3) bins_bin_exists 
          sound_\<pi> wf_\<pi> wf_bins_kth_bin wf_items_def wellformed_bins_elim by metis
  hence sound: "sound_items cfg inp (bins ?bs')"
    using Scan.hyps(5) Scan.prems(1,3) bins_bins_upd sound_items_def wellformed_bins_elim
    by (metis UnE add_less_cancel_right)
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Scan.hyps Scan.prems(1) wellformed_bins_Scan_it by metis
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using sound Scan by (metis \<pi>_it'_simps(3) wellformed_bins_Scan_it)
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Scan.prems(2) by auto
    have "\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j"
      using Scan.hyps by simp
    also have "... = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_\<pi>_it' length_items_nth_bin_bins_upd order_trans Scan.hyps Scan.prems(1) \<pi>_it'_simps(3)
        by (smt (verit, ccfv_SIG))
      hence "\<pi>_it' k cfg inp ?bs'' j = \<pi>_it' k cfg inp (bins_upd ?bs'' (k+1) (Scan_it k inp a x i)) (j+1)"
        using \<open>i = j\<close> kth_\<pi>_it'_bins nth_bins_upd \<pi>_it'_simps(3) Scan.hyps Scan.prems(1) by (smt (verit, best) leI le_trans)
      moreover have "bins_upd ?bs'' (k+1) (Scan_it k inp a x i) = ?bs''"
      proof -
        have "length (items (bs ! (k+1))) = length (pointers (bs ! (k+1)))"
          by (metis Scan.hyps(5) Scan.prems(1) add_less_cancel_right wellformed_bins_elim wf_bin_def wf_bins_def)
        moreover have "k+1 < length bs" "k < length bs" "k+1 < length ?bs'"
          using Scan.hyps(5) Scan.prems wellformed_bins_elim by fastforce+
        ultimately have 1: "set (Scan_it k inp a x i) \<sqsubseteq> bin_ptr (?bs' ! (k+1))"
          using subsumed_bins_upd_ips by blast
        moreover have 2: "bin_ptr (?bs' ! (k+1)) \<sqsubseteq> bin_ptr (?bs'' ! (k+1))"
          using wf \<pi>_it'_kth_subsumed_by[OF wf \<open>k+1 < length ?bs'\<close>] by simp
        ultimately have "set (Scan_it k inp a x i) \<sqsubseteq> bin_ptr (?bs'' ! (k+1))"
          using subsumed_by_mono by blast
        moreover have "distinct (items (?bs'' ! (k+1)))"
          using \<open>k+1 < length bs\<close> length_bins_\<pi>_it' length_bins_upd local.wf wf_bin_def wf_bins_\<pi>_it' wf_bins_def by metis
        ultimately show ?thesis
          using bins_upd_eq by blast
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k cfg inp ?bs' (i + 1)"
      using \<open>i = j\<close> Scan.IH Scan.prems Scan.hyps sound wellformed_bins_Scan_it by fast
    finally show ?thesis
      using Scan.hyps by simp
  qed
next
  case (Pass k cfg inp bs i x a)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using Pass by (metis \<pi>_it'_simps(4))
  next
    assume "\<not> i+1 \<le> j"
    show ?thesis
      using Pass \<pi>_it'_simps(1,4) kth_\<pi>_it'_bins by (metis Suc_eq_plus1 Suc_leI antisym_conv2 not_le_imp_less)
  qed
next
  case (Predict k cfg inp bs i x a)
  let ?bs' = "bins_upd bs k (Predict_it k cfg a)"
  have x: "x \<in> set (items (bs ! k))"
    using Predict.hyps(1,2) by auto
  hence "sound_items cfg inp (set (map fst (Predict_it k cfg a)))"
    using sound_Predict_it \<pi>_mono Predict.hyps(3) Predict.prems bins_bin_exists wellformed_bins_elim
          sound_\<pi> wf_bins_kth_bin wf_items_def by metis
  hence sound: "sound_items cfg inp (bins ?bs')"
    using Predict.prems(1,3) UnE bins_bins_upd sound_items_def wellformed_bins_elim by metis
  have wf: "(k, cfg, inp, ?bs') \<in> wellformed_bins"
    using Predict.hyps Predict.prems(1) wellformed_bins_Predict_it by metis
  have len: "i < length (items (?bs' ! k))"
    using length_items_nth_bin_bins_upd Predict.hyps(1) Orderings.preorder_class.dual_order.strict_trans1 linorder_not_less by blast
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using sound wf Predict by (metis \<pi>_it'_simps(5))
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Predict.prems(2) by auto
    have "\<pi>_it' k cfg inp (\<pi>_it' k cfg inp bs i) j = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) j"
      using Predict.hyps by simp
    also have "... = \<pi>_it' k cfg inp (\<pi>_it' k cfg inp ?bs' (i+1)) (j+1)"
    proof -
      let ?bs'' = "\<pi>_it' k cfg inp ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_\<pi>_it' length_items_nth_bin_bins_upd order_trans wf by blast
      hence "\<pi>_it' k cfg inp ?bs'' j = \<pi>_it' k cfg inp (bins_upd ?bs'' k (Predict_it k cfg a)) (j+1)"
        using \<open>i = j\<close> kth_\<pi>_it'_bins nth_bins_upd \<pi>_it'_simps(5) Predict.hyps Predict.prems(1) length_bins_\<pi>_it'
          wf_bins_\<pi>_it' wf_bins_kth_bin wf_item_def x by (smt (verit, ccfv_SIG) linorder_not_le order.trans)
      moreover have "bins_upd ?bs'' k (Predict_it k cfg a) = ?bs''"
      proof -
        have "length (items (bs ! k)) = length (pointers (bs ! k))" "k < length bs"
          using wellformed_bins_elim[OF Predict.prems(1)] wf_bins_def wf_bin_def by blast+
        hence 1: "set (Predict_it k cfg a) \<sqsubseteq> bin_ptr (?bs' ! k)"
          using subsumed_bins_upd_ips by fast
        moreover have 2: "bin_ptr (?bs' ! k) \<sqsubseteq> bin_ptr (?bs'' ! k)"
          by (simp add: \<open>k < length bs\<close> \<pi>_it'_kth_subsumed_by wf)
        ultimately have "set (Predict_it k cfg a) \<sqsubseteq> bin_ptr (?bs'' ! k)"
          using subsumed_by_mono by blast
        moreover have "distinct (items (?bs'' ! k))"
          using \<open>k < length bs\<close> length_bins_\<pi>_it' length_bins_upd local.wf wf_bin_def wf_bins_\<pi>_it' wf_bins_def by metis
        ultimately show ?thesis
          using bins_upd_eq by blast
      qed
      ultimately show ?thesis
        by presburger
    qed
    also have "... = \<pi>_it' k cfg inp ?bs' (i + 1)"
      using \<open>i = j\<close> Predict.IH Predict.prems sound wf by (metis order_refl)
    finally show ?thesis
      using Predict.hyps by simp
  qed
qed simp

lemma \<pi>_it_idem:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "sound_items cfg inp (bins bs)" "nonempty_derives cfg"
  shows "\<pi>_it k cfg inp (\<pi>_it k cfg inp bs) = \<pi>_it k cfg inp bs"
  using assms \<pi>_it'_idem \<pi>_it_def le0 by metis

lemma funpower_\<pi>_step_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_upto bs k 0) \<subseteq> bins bs" "sound_items cfg inp (bins bs)"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "funpower (\<pi>_step k cfg inp) n (bins bs) \<subseteq> bins (\<pi>_it k cfg inp bs)"
  using assms
proof (induction n)
  case 0
  thus ?case
    by (simp add: \<pi>_it'_mono \<pi>_it_def)
next
  case (Suc n)
  have 0: "\<pi>_step k cfg inp (bins_upto (\<pi>_it k cfg inp bs) k 0) \<subseteq> bins (\<pi>_it k cfg inp bs)"
    using \<pi>_it'_mono bins_upto_k0_\<pi>_it'_eq \<pi>_it_def order_trans by (metis (no_types, lifting) assms(1,2))
  have "funpower (\<pi>_step k cfg inp) (Suc n) (bins bs) \<subseteq> (\<pi>_step k cfg inp) (bins (\<pi>_it k cfg inp bs))"
    using \<pi>_step_sub_mono Suc by (metis funpower.simps(2))
  also have "... \<subseteq> bins (\<pi>_it k cfg inp (\<pi>_it k cfg inp bs))"
    using \<pi>_step_sub_\<pi>_it Suc.prems wf_bins_\<pi>_it sound_\<pi>_it 0 wellformed_bins_\<pi>_it by blast
  also have "... \<subseteq> bins (\<pi>_it k cfg inp bs)"
    using \<pi>_it_idem Suc.prems by fastforce
  finally show ?case .
qed

lemma \<pi>_sub_\<pi>_it:
  assumes "(k, cfg, inp, bs) \<in> wellformed_bins"
  assumes "\<pi>_step k cfg inp (bins_upto bs k 0) \<subseteq> bins bs" "sound_items cfg inp (bins bs)"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "\<pi> k cfg inp (bins bs) \<subseteq> bins (\<pi>_it k cfg inp bs)"
  using assms funpower_\<pi>_step_sub_\<pi>_it \<pi>_def elem_limit_simp by fastforce

lemma \<I>_sub_\<I>_it:
  assumes "k \<le> length inp" "wf_cfg cfg"
  assumes "is_word cfg inp" "nonempty_derives cfg"
  shows "\<I> k cfg inp \<subseteq> bins (\<I>_it k cfg inp)"
  using assms
proof (induction k)
  case 0
  hence "\<pi> 0 cfg inp (Init cfg) \<subseteq> bins (\<pi>_it 0 cfg inp (Init_it cfg inp))"
    using \<pi>_sub_\<pi>_it Init_it_eq_Init length_bins_Init_it Init_it_eq_Init sound_Init bins_upto_empty
          \<pi>_step_empty bins_upto_sub_bins wellformed_bins_Init_it wellformed_bins_elim by metis
  thus ?case
    by simp
next
  case (Suc k)
  have wf: "(Suc k, cfg, inp, \<I>_it k cfg inp) \<in> wellformed_bins"
    by (simp add: Suc.prems(1) Suc_leD assms(2) wellformed_bins_intro)
  have sub: "\<pi>_step (Suc k) cfg inp (bins_upto (\<I>_it k cfg inp) (Suc k) 0) \<subseteq> bins (\<I>_it k cfg inp)"
  proof -
    have "bin (bins_upto (\<I>_it k cfg inp) (Suc k) 0) (Suc k) = {}"
      using kth_bin_bins_upto_empty wf Suc.prems wellformed_bins_elim by blast
    hence "\<pi>_step (Suc k) cfg inp (bins_upto (\<I>_it k cfg inp) (Suc k) 0) = bins_upto (\<I>_it k cfg inp) (Suc k) 0"
      unfolding \<pi>_step_def Scan_def Complete_def Predict_def bin_def by blast
    also have "... \<subseteq> bins (\<I>_it k cfg inp)"
      using wf Suc.prems bins_upto_sub_bins wellformed_bins_elim by blast
    finally show ?thesis .
  qed
  have sound: "sound_items cfg inp (bins (\<I>_it k cfg inp))"
    using Suc sound_\<I> \<I>_it_sub_\<I> by (metis Suc_leD subset_antisym)
  have "\<I> (Suc k) cfg inp \<subseteq> \<pi> (Suc k) cfg inp (bins (\<I>_it k cfg inp))"
    using Suc \<pi>_sub_mono by simp
  also have "... \<subseteq> bins (\<pi>_it (Suc k) cfg inp (\<I>_it k cfg inp))"
    using \<pi>_sub_\<pi>_it wf sub sound Suc.prems by fastforce
  finally show ?case
    by simp
qed

lemma \<II>_sub_\<II>_it:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "\<II> cfg inp \<subseteq> bins (\<II>_it cfg inp)"
  using assms \<I>_sub_\<I>_it \<II>_def \<II>_it_def by (metis le_refl)


subsection \<open>Correctness\<close>

definition earley_recognized_it :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> bool" where
  "earley_recognized_it cfg inp = (\<exists>x \<in> set (items ((\<II>_it cfg inp) ! length inp)). is_finished cfg inp x)"

theorem earley_recognized_it_iff_earley_recognized:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "earley_recognized_it cfg inp \<longleftrightarrow> earley_recognized cfg inp"
proof -
  have "earley_recognized_it cfg inp = (\<exists>x \<in> set (items ((\<II>_it cfg inp) ! length inp)). is_finished cfg inp x)"
    unfolding earley_recognized_it_def by blast
  also have "... = (\<exists>x \<in> bins (\<II>_it cfg inp). is_finished cfg inp x)"
    using is_finished_def kth_bin_sub_bins \<II>_it_def length_bins_Init_it wf_bins_\<II>_it
      wf_item_in_kth_bin set_bin_def length_\<I>_it assms(1)
    by (smt (verit) le_eq_less_or_eq subset_code(1) wellformed_bins_\<I>_it wellformed_bins_elim)
  also have "... = (\<exists>x \<in> \<II> cfg inp. is_finished cfg inp x)"
    using assms \<II>_it_sub_\<II> \<II>_sub_\<II>_it by blast
  also have "... = earley_recognized cfg inp"
    unfolding earley_recognized_def by blast
  finally show ?thesis .
qed

corollary correctness_list:
  assumes "wf_cfg cfg" "is_word cfg inp" "nonempty_derives cfg"
  shows "earley_recognized_it cfg inp \<longleftrightarrow> derives cfg [\<SS> cfg] inp"
  using assms correctness_set earley_recognized_it_iff_earley_recognized by blast


section \<open>Earley parse tree\<close>

subsection \<open>Main definitions\<close>

datatype 'a dtree =
  Leaf 'a
  | Node 'a "'a dtree list"

fun yield_dtree :: "'a dtree \<Rightarrow> 'a sentence" where
  "yield_dtree (Leaf a) = [a]"
| "yield_dtree (Node _ ts) = concat (map yield_dtree ts)"

fun root_dtree :: "'a dtree \<Rightarrow> 'a" where
  "root_dtree (Leaf a) = a"
| "root_dtree (Node N _) = N"

\<comment>\<open>Implies: derives cfg [root_dtree t] (yield_dtree t)\<close>
fun wf_dtree :: "'a cfg \<Rightarrow> 'a dtree \<Rightarrow> bool" where
  "wf_dtree cfg (Leaf a) \<longleftrightarrow> is_terminal cfg a \<or> is_nonterminal cfg a"
| "wf_dtree cfg (Node N ts) \<longleftrightarrow>
    (\<exists>r \<in> set (\<RR> cfg). r = (N, map root_dtree ts)) \<and>
    (\<forall>t \<in> set ts. wf_dtree cfg t)"

\<comment>\<open>Implied by wf_dtree\<close>
definition sound_dtree :: "'a cfg \<Rightarrow> 'a dtree \<Rightarrow> bool" where
  "sound_dtree cfg t = derives cfg [root_dtree t] (yield_dtree t)"

\<comment>\<open>Refine to prefix of yield depending on item_dot and Leafs default to true.\<close>
definition inp_dtree :: "'a sentence \<Rightarrow> 'a item \<Rightarrow> 'a dtree \<Rightarrow> bool" where
  "inp_dtree inp x t \<longleftrightarrow> yield_dtree t = slice (item_origin x) (item_end x) inp"

function build_dtree' :: "'a bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a dtree" where
  "build_dtree' bs k i = (
    let kb = bs ! k in
    let x = items kb ! i in (
    case pointers kb ! i of
      [] \<Rightarrow> Node (item_rule_head x) (map Leaf (item_rule_body x)) \<comment>\<open>start building sub-tree\<close>
    | (Pre pre) # _ \<Rightarrow> build_dtree' bs (k-1) pre \<comment>\<open>traverse terminal in the input\<close>
    | (PreRed k' pre red) # _ \<Rightarrow> ( \<comment>\<open>update non-terminal with complete sub-tree\<close>
      case build_dtree' bs k' pre of
        Node N ts \<Rightarrow> Node N (ts[item_dot x - 1 := build_dtree' bs k red])
      | _ \<Rightarrow> undefined \<comment>\<open>impossible case\<close>)))"
  by pat_completeness auto
termination sorry

declare build_dtree'.simps [simp del]

definition build_dtree :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a dtree option" where
  "build_dtree cfg inp bs = (
    let k = length bs - 1 in
    case find_index (\<lambda>x. is_finished cfg inp x) (items (bs!k)) of
      Some i \<Rightarrow> Some (build_dtree' bs k i)
    | None \<Rightarrow> None
  )"


subsection \<open>Lemmas about valid bin pointers\<close>

definition mono_ptrs :: "'a bins \<Rightarrow> bool" where
  "mono_ptrs bs = (\<forall>k < length bs. \<forall>i < length (pointers (bs!k)).
    (\<forall>pre. Pre pre \<in> set (pointers (bs!k) ! i) \<longrightarrow>
      pre < length (pointers (bs!(k-1)))) \<and>
    (\<forall>k' pre red. PreRed k' pre red \<in> set (pointers (bs!k) ! i) \<longrightarrow> 
      k' < k \<and> pre < length (pointers (bs!k')) \<and> red < i)
  )"


subsection \<open>Main lemmas\<close>

lemma ex_Node_build_tree':
  "\<exists>N ts. build_dtree' bs k i = Node N ts"
  apply (induction bs k i rule: build_dtree'.induct)
  apply (subst build_dtree'.simps)
  apply (auto simp: Let_def split: list.splits dtree.splits pointer.splits)
  apply (metis dtree.distinct(1))
  done

lemma nex_Leaf_build_tree':
  "\<nexists>a. build_dtree' bs k i = Leaf a"
  using ex_Node_build_tree' by (metis dtree.distinct(1))

lemma Derivation_imp_ex_wf_yield:
  "Derivation cfg [a] D \<alpha> \<Longrightarrow> is_symbol cfg a \<Longrightarrow> \<exists>t. root_dtree t = a \<and> yield_dtree t = \<alpha> \<and> wf_dtree cfg t"
  sorry

lemma wf_tree_imp_ex_Derivation:
  "wf_dtree cfg t \<Longrightarrow> \<exists>D. Derivation cfg [root_dtree t] D (yield_dtree t)"
  sorry

lemma derives_imp_ex_wf_yield:
  "wf_cfg cfg \<Longrightarrow> derives cfg [\<SS> cfg] \<alpha> \<Longrightarrow> \<exists>t. root_dtree t = \<SS> \<and> yield_dtree t = \<alpha> \<and> wf_dtree cfg t"
  sorry

lemma wf_tree_imp_ex_derives:
  "wf_dtree cfg t \<Longrightarrow> derives cfg [root_dtree t] (yield_dtree t)"
  sorry

lemma wf_dtree_build_dtree':
  "wf_bins cfg inp bs \<Longrightarrow> wf_dtree cfg (build_dtree' bs k i)"
  sorry

lemma inp_dtree_build_dtree':
  "inp_dtree inp (items (bs!k) ! i) (build_dtree' bs k i)"
  sorry

lemma sound_dtree_build_tree':
  "sound_dtree cfg (build_dtree' bs k i)"
  sorry

lemma sound_dtree_build_tree:
  "build_dtree cfg inp bs = Some t \<Longrightarrow> sound_dtree cfg t"
  sorry


section \<open>Earley parse forest\<close>


end

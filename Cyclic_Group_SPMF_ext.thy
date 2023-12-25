theory Cyclic_Group_SPMF_ext

imports CryptHOL.Cyclic_Group_SPMF

begin

subsection \<open>sample uniform set\<close>

definition sample_uniform_set :: "nat \<Rightarrow> nat \<Rightarrow> nat set spmf"
  where "sample_uniform_set k n = spmf_of_set {x. x \<subseteq> {..<n} \<and> card x = k}"

lemma spmf_sample_uniform: "spmf (sample_uniform_set k n) x 
  = indicator {x. x \<subseteq> {..<n} \<and> card x = k} x / (n choose k)"
  by (simp add: n_subsets sample_uniform_set_def spmf_of_set)

lemma weight_sample_uniform_set: "weight_spmf (sample_uniform_set k n) = of_bool (k\<le>n)"
  apply (auto simp add: sample_uniform_set_def weight_spmf_of_set split: if_splits)
   apply (metis card_lessThan card_mono finite_lessThan)
  using card_lessThan by blast

lemma weight_sample_uniform_set_k_0 [simp]: "weight_spmf (sample_uniform_set 0 n) = 1"
  by (auto simp add: weight_sample_uniform_set)

lemma weight_sample_uniform_set_n_0 [simp]: "weight_spmf (sample_uniform_set k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_uniform_set)

lemma weight_sample_uniform_set_k_le_n [simp]: "k\<le>n \<Longrightarrow> weight_spmf (sample_uniform_set k n) = 1"
  by (auto simp add: weight_sample_uniform_set indicator_def gr0_conv_Suc)

lemma lossless_sample_uniform_set [simp]: "lossless_spmf (sample_uniform_set k n) \<longleftrightarrow> k \<le> n"
  by (auto simp add: lossless_spmf_def weight_sample_uniform_set intro: ccontr)

lemma set_spmf_sample_uniform_set [simp]: "set_spmf (sample_uniform_set k n) = {x. x \<subseteq> {..<n} \<and> card x = k}"
  by(simp add: sample_uniform_set_def)


subsection \<open>sample uniform list\<close>

definition sample_uniform_list :: "nat \<Rightarrow> nat \<Rightarrow> nat list spmf"
  where "sample_uniform_list k n = spmf_of_set {x. set x \<subseteq> {..<n} \<and> length x = k}"

lemma spmf_sample_uniform_list: "spmf (sample_uniform_list k n) x 
  = indicator {x. set x \<subseteq> {..<n} \<and> length x = k} x / (n^k)"
  by (simp add: card_lists_length_eq sample_uniform_list_def spmf_of_set)

lemma weight_sample_uniform_list: "weight_spmf (sample_uniform_list k n) = of_bool (k=0 \<or> 0<n)"
proof -
  have "0 < n \<longrightarrow> (\<exists>x. set x \<subseteq> {..<n} \<and> length x = k)"
  proof
    assume zero_l_n: "0 < n"
    show "\<exists>x. set x \<subseteq> {..<n} \<and> length x = k"
    proof 
      let ?x = "replicate k 0"
      show "set ?x \<subseteq> {..<n} \<and> length ?x = k"
        using zero_l_n by fastforce
    qed
  qed
  then show ?thesis 
    by (simp add: finite_lists_length_eq sample_uniform_list_def weight_spmf_of_set)
qed
  
lemma weight_sample_uniform_list_k_0 [simp]: "weight_spmf (sample_uniform_list 0 n) = 1"
  by (auto simp add: weight_sample_uniform_list)

lemma weight_sample_uniform_list_n_0 [simp]: "weight_spmf (sample_uniform_list k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_uniform_list)

lemma weight_sample_uniform_list_k_le_n [simp]: "k<n \<Longrightarrow> weight_spmf (sample_uniform_list k n) = 1"
  by (auto simp add: weight_sample_uniform_list less_iff_Suc_add)

lemma lossless_sample_uniform_list [simp]: "lossless_spmf (sample_uniform_list k n) \<longleftrightarrow> (k=0 \<or> 0<n)"
  by (auto simp add: lossless_spmf_def weight_sample_uniform_list intro: ccontr)

lemma set_spmf_sample_uniform_list [simp]: "set_spmf (sample_uniform_list k n) = {x. set x \<subseteq> {..<n} \<and> length x = k}"
  by (simp add: finite_lists_length_eq sample_uniform_list_def)

subsection \<open>sample distinct uniform list\<close>  

definition sample_distinct_uniform_list :: "nat \<Rightarrow> nat \<Rightarrow> nat list spmf"
  where "sample_distinct_uniform_list k n 
          = spmf_of_set {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}}" 
  
lemma spmf_sample_distinct_uniform_list: 
"spmf (sample_distinct_uniform_list k n) x
  = indicator {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} x / real (\<Prod>{n - k + 1..n})"
proof -
  have "spmf (sample_distinct_uniform_list k n) x 
  = indicat_real {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} x /
    real (card {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}})"
    unfolding sample_distinct_uniform_list_def spmf_of_set ..
  also have "\<dots> = indicat_real {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} x /
    real (\<Prod>{card {..<n} - k + 1..card {..<n}})"
  proof (cases "k \<le> card {..<n}")
    case True
    then show ?thesis
      using card_lists_distinct_length_eq[of "{..<n}" k]
      by fastforce
  next
    case False
    then have "{xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} = {}"
      by (smt (verit, del_insts) card_mono distinct_card empty_Collect_eq finite_lessThan)
    then show ?thesis
      by fastforce
  qed
  also have "\<dots> = indicator {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} x 
                  / real (\<Prod>{n - k + 1..n})"
    by simp
  finally show ?thesis .
qed

lemma weight_sample_distinct_uniform_list: "weight_spmf (sample_distinct_uniform_list k n) = of_bool (k\<le>n)"
  apply (auto simp add: sample_distinct_uniform_list_def weight_spmf_of_set split: split_indicator)
   apply (metis atLeast0LessThan distinct_card subset_eq_atLeast0_lessThan_card)
  apply (metis atLeast0LessThan card_atLeastLessThan diff_zero distinct_card distinct_upt lessThan_subset_iff set_upt)
  done

lemma weight_sample_distinct_uniform_list_k_0 [simp]: "weight_spmf (sample_distinct_uniform_list 0 n) = 1"
  by (auto simp add: weight_sample_distinct_uniform_list)

lemma weight_sample_distinct_uniform_list_n_0 [simp]: "weight_spmf (sample_distinct_uniform_list k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_distinct_uniform_list)

lemma weight_sample_distinct_uniform_list_k_le_n [simp]: "k<n \<Longrightarrow> weight_spmf (sample_distinct_uniform_list k n) = 1"
  by (auto simp add: weight_sample_distinct_uniform_list less_iff_Suc_add)

lemma lossless_sample_distinct_uniform_list [simp]: "lossless_spmf (sample_distinct_uniform_list k n) \<longleftrightarrow> k\<le>n"
  by (auto simp add: lossless_spmf_def weight_sample_distinct_uniform_list intro: ccontr)

lemma set_spmf_sample_distinct_uniform_list [simp]: "set_spmf (sample_distinct_uniform_list k n) 
  = {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}}"
  by (simp add: finite_lists_distinct_length_eq sample_distinct_uniform_list_def)

subsection \<open>sample distinct cooridinates\<close>

fun pair_lists :: "(nat list \<times> nat list) \<Rightarrow> (nat * nat) list" where 
  "pair_lists ([],[]) = []" |
  "pair_lists ((x#xs), (y#ys)) = (x,y)#pair_lists (xs,ys)"

definition sample_distinct_coordinates_uniform :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times>nat) list spmf"
  where "sample_distinct_coordinates_uniform k n 
          = map_spmf pair_lists (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"





end
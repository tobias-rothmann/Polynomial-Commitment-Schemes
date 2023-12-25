theory Cyclic_Group_SPMF_ext

imports CryptHOL.Cyclic_Group_SPMF

begin


definition sample_k_uniform :: "nat \<Rightarrow> nat \<Rightarrow> nat set spmf"
  where "sample_k_uniform k n = spmf_of_set {x. x \<subseteq> {..<n} \<and> card x = k}"

lemma spmf_sample_uniform: "spmf (sample_k_uniform k n) x 
  = indicator {x. x \<subseteq> {..<n} \<and> card x = k} x / (n choose k)"
  by (simp add: n_subsets sample_k_uniform_def spmf_of_set)

lemma weight_sample_k_uniform: "weight_spmf (sample_k_uniform k n) = of_bool (k\<le>n)"
  apply (auto simp add: sample_k_uniform_def weight_spmf_of_set split: if_splits)
   apply (metis card_lessThan card_mono finite_lessThan)
  using card_lessThan by blast

lemma weight_sample_k_uniform_k_0 [simp]: "weight_spmf (sample_k_uniform 0 n) = 1"
  by (auto simp add: weight_sample_k_uniform)

lemma weight_sample_k_uniform_n_0 [simp]: "weight_spmf (sample_k_uniform k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_k_uniform)

lemma weight_sample_k_uniform_k_le_n [simp]: "k\<le>n \<Longrightarrow> weight_spmf (sample_k_uniform k n) = 1"
  by (auto simp add: weight_sample_k_uniform indicator_def gr0_conv_Suc)

lemma lossless_sample_k_uniform [simp]: "lossless_spmf (sample_k_uniform k n) \<longleftrightarrow> k \<le> n"
  by (auto simp add: lossless_spmf_def weight_sample_k_uniform intro: ccontr)

lemma set_spmf_sample_k_uniform [simp]: "set_spmf (sample_k_uniform k n) = {x. x \<subseteq> {..<n} \<and> card x = k}"
  by(simp add: sample_k_uniform_def)


subsection \<open>sample uniform list\<close>

definition sample_list_uniform :: "nat \<Rightarrow> nat \<Rightarrow> nat list spmf"
  where "sample_list_uniform k n = spmf_of_set {x. set x \<subseteq> {..<n} \<and> length x = k}"

lemma spmf_sample_list_uniform: "spmf (sample_list_uniform k n) x 
  = indicator {x. set x \<subseteq> {..<n} \<and> length x = k} x / (n^k)"
  by (simp add: card_lists_length_eq sample_list_uniform_def spmf_of_set)

lemma weight_sample_list_uniform: "weight_spmf (sample_list_uniform k n) = of_bool (k=0 \<or> 0<n)"
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
    by (simp add: finite_lists_length_eq sample_list_uniform_def weight_spmf_of_set)
qed
  
lemma weight_sample_list_uniform_k_0 [simp]: "weight_spmf (sample_list_uniform 0 n) = 1"
  by (auto simp add: weight_sample_list_uniform)

lemma weight_sample_list_uniform_n_0 [simp]: "weight_spmf (sample_list_uniform k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_list_uniform)

lemma weight_sample_list_uniform_k_le_n [simp]: "k<n \<Longrightarrow> weight_spmf (sample_list_uniform k n) = 1"
  by (auto simp add: weight_sample_list_uniform less_iff_Suc_add)

lemma lossless_sample_list_uniform [simp]: "lossless_spmf (sample_list_uniform k n) \<longleftrightarrow> (k=0 \<or> 0<n)"
  by (auto simp add: lossless_spmf_def weight_sample_list_uniform intro: ccontr)

lemma set_spmf_sample_list_uniform [simp]: "set_spmf (sample_list_uniform k n) = {x. set x \<subseteq> {..<n} \<and> length x = k}"
  by (simp add: finite_lists_length_eq sample_list_uniform_def)

subsection \<open>sample distinct uniform list\<close>  

definition sample_distinct_list_uniform :: "nat \<Rightarrow> nat \<Rightarrow> nat list spmf"
  where "sample_distinct_list_uniform k n 
          = spmf_of_set {x. set x \<subseteq> {..<n} \<and> distinct x \<and> length x = k}"

fun pair_lists :: "(nat list \<times> nat list) \<Rightarrow> (nat * nat) list" where 
  "pair_lists ([],[]) = []" |
  "pair_lists ((x#xs), (y#ys)) = (x,y)#pair_lists (xs,ys)"

definition sample_pair_list_uniform :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times>nat) list spmf"
  where "sample_pair_list_uniform k n 
          = map_spmf pair_lists (pair_spmf (sample_list_uniform k n) (sample_list_uniform k n))"

  



end
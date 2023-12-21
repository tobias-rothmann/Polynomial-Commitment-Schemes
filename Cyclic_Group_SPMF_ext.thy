theory Cyclic_Group_SPMF_ext

imports CryptHOL.Cyclic_Group_SPMF

begin


definition sample_k_uniform :: "nat \<Rightarrow> nat \<Rightarrow> nat set spmf"
  where "sample_k_uniform k n = spmf_of_set {x. x \<subseteq> {..<n} \<and> card x = k}"

lemma spmf_sample_uniform: "spmf (sample_k_uniform k n) x 
  = indicator {x. x \<subseteq> {..<n} \<and> card x = k} x / (n choose k)"
  by (simp add: n_subsets sample_k_uniform_def spmf_of_set)

lemma "card {..<n} = n"
  by simp

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

end
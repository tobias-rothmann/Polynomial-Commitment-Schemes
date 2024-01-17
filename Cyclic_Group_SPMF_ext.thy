theory Cyclic_Group_SPMF_ext

imports CryptHOL.Cyclic_Group_SPMF

begin

subsection \<open>sample uniform set\<close>

definition sample_uniform_set :: "nat \<Rightarrow> nat \<Rightarrow> nat set spmf"
  where "sample_uniform_set k n = spmf_of_set {x. x \<subseteq> {..<n} \<and> card x = k}"

lemma spmf_sample_uniform_set: "spmf (sample_uniform_set k n) x 
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

text \<open>function to reverse the list pairing, used in the spmf proof.\<close>
fun unpair_lists :: "(nat * nat) list \<Rightarrow> (nat list \<times> nat list)" where
  "unpair_lists [] = ([],[])" |
  "unpair_lists ((x,y)#xs) = (x#fst (unpair_lists xs), y#snd (unpair_lists xs))"

definition sample_distinct_coordinates_uniform :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list spmf"
  where "sample_distinct_coordinates_uniform k n 
          = map_spmf pair_lists (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"

lemma unpair_pair_set: "unpair_lists ` pair_lists `
        set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n)) 
      = set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
proof -
  have simplif: "set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n)) 
    =  {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}"
    unfolding  set_pair_spmf set_spmf_sample_distinct_uniform_list set_spmf_sample_uniform_list ..
  have "(unpair_lists \<circ>
    pair_lists)`
    ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times>
     {x. set x \<subseteq> {..<n} \<and> length x = k}) =
    id ` ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k})"
  proof(rule image_cong)
    fix x 
    assume asm: " x \<in> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times>
             {x. set x \<subseteq> {..<n} \<and> length x = k}"
    then have "unpair_lists (pair_lists x) = id x"
      by (induction "x" arbitrary: k rule: pair_lists.induct)simp+
    then show "(unpair_lists \<circ> pair_lists) x = id x" 
      by fastforce
  qed simp
  then show ?thesis
    by (simp add: image_comp simplif)
qed

lemma spmf_sample_distinct_coordinates_uniform: 
  "spmf (sample_distinct_coordinates_uniform k n) pairs 
 = indicator ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}) (unpair_lists pairs) 
   / (real (\<Prod>{n - k + 1..n}) * (n^k))"
proof -
   have unfold_pairing: "pair_lists (unpair_lists pairs) = pairs"
     by (induction pairs rule: unpair_lists.induct) simp+
   have "spmf (sample_distinct_coordinates_uniform k n) pairs =  spmf
     (map_spmf pair_lists
       ( pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n) )
     )
    (pair_lists (unpair_lists pairs))"
     unfolding sample_distinct_coordinates_uniform_def unfold_pairing ..
   also have "\<dots> = indicator ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}) (unpair_lists pairs) 
   / (real (\<Prod>{n - k + 1..n}) * (n^k))"
   proof (cases "(pair_lists (unpair_lists pairs)) \<notin> pair_lists ` set_spmf ( pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n) )")
     case True
     then show ?thesis
       by (auto simp add: image_eqI spmf_map_outside  indicator_def)
   next
     case False
     have "spmf
           (map_spmf pair_lists
             (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n)))
           (pair_lists (unpair_lists pairs)) 
         = spmf ( pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n) ) 
              (unpair_lists pairs)"
     proof (rule spmf_map_inj)
       show "inj_on pair_lists (set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n)))"
       proof 
          fix x y
          assume "x \<in> set_spmf
                  (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
          then have x_in_pair_set: 
            "x \<in> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}"
            by simp
          then have unpair_x: "unpair_lists (pair_lists x) = x"
            by (induction x arbitrary: k rule: pair_lists.induct) auto
          assume "y \<in> set_spmf
                   (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
           then have y_in_pair_set: 
            "y \<in> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}"
             by simp
           then have unpair_y: "unpair_lists (pair_lists y) = y"
            by (induction y arbitrary: k rule: pair_lists.induct) auto
           assume pair_lists_eq: "pair_lists x = pair_lists y"
           then show "x=y" using unpair_x unpair_y by argo
       qed

       from False have "pair_lists (unpair_lists pairs) \<in> pair_lists `
        set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
         by blast
       then have "unpair_lists (pair_lists (unpair_lists pairs)) \<in> unpair_lists ` pair_lists `
          set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
         by fast
       then show " (unpair_lists pairs) \<in>
          set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
         using unpair_pair_set unfold_pairing by simp
     qed
     also have "\<dots> = (spmf (sample_distinct_uniform_list k n) (fst (unpair_lists pairs) )) * (spmf (sample_uniform_list k n) (snd (unpair_lists pairs)))"
       by (metis spmf_pair surjective_pairing)
     also have "\<dots> = indicator {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} (fst (unpair_lists pairs)) / real (\<Prod>{n - k + 1..n})
      * indicator {x. set x \<subseteq> {..<n} \<and> length x = k} (snd (unpair_lists pairs)) / (n^k)"
      by (simp add: spmf_sample_distinct_uniform_list spmf_sample_uniform_list)
    also have "\<dots> = indicator ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}) (unpair_lists pairs) 
          / (real (\<Prod>{n - k + 1..n}) * (n^k))"
      by (smt (verit) div_by_1 divide_divide_eq_left indicator_simps(1) indicator_simps(2) mem_Sigma_iff mult_eq_0_iff nonzero_mult_div_cancel_left prod.collapse times_divide_eq_left)
    finally  show ?thesis
      by fastforce 
   qed
   finally show ?thesis .
 qed

lemma weight_sample_distinct_coordinates_uniform_list: "weight_spmf (sample_distinct_coordinates_uniform k n) = of_bool (k\<le>n \<and> (k=0 \<or> 0<n))"
  by (auto simp add: sample_distinct_coordinates_uniform_def weight_spmf_of_set lossless_weight_spmfD weight_sample_distinct_uniform_list split: split_indicator)

lemma weight_sample_distinct_coordinates_uniform_list_k_0 [simp]: "weight_spmf (sample_distinct_coordinates_uniform 0 n) = 1"
  by (auto simp add: weight_sample_distinct_coordinates_uniform_list)

lemma weight_sample_distinct_coordinates_uniform_list_n_0 [simp]: "weight_spmf (sample_distinct_coordinates_uniform k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_distinct_coordinates_uniform_list)

lemma weight_sample_distinct_coordinates_uniform_list_k_le_n [simp]: "k<n \<Longrightarrow> weight_spmf (sample_distinct_coordinates_uniform k n) = 1"
  by (auto simp add: weight_sample_distinct_coordinates_uniform_list less_iff_Suc_add)

lemma lossless_sample_sample_distinct_coordinates_uniform_list [simp]: "lossless_spmf (sample_distinct_coordinates_uniform k n) \<longleftrightarrow> k\<le>n"
  by (auto simp add: lossless_spmf_def weight_sample_distinct_coordinates_uniform_list intro: ccontr)

lemma set_spmf_sample_distinct_coordinates_uniform_list [simp]: 
  "set_spmf (sample_distinct_coordinates_uniform k n) 
  = pair_lists `
    ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times>
     {xs. set xs \<subseteq> {..<n} \<and> length xs = k})"
  by (simp add: sample_distinct_coordinates_uniform_def)

end
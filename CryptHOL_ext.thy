theory CryptHOL_ext

imports CryptHOL.Cyclic_Group_SPMF "HOL-Computational_Algebra.Polynomial" 
  Berlekamp_Zassenhaus.Finite_Field

begin

(* TODO add cyclic group content in here as well *)

text \<open>Here we collect a handful of lemmas about CryptHOL games, that we use in our proofs.\<close>

lemma ennreal_spmf: "ennreal (spmf game1 True) \<le> ennreal (spmf game2 True) \<Longrightarrow> 
  spmf game1 True \<le> spmf game2 True"
  by (simp add: ennreal_le_iff)

lemma unpack_bind_spmf: "X = X' \<Longrightarrow> bind_spmf X Y = bind_spmf X' Y"
  by simp

lemma unpack_bind_spmf': "Y = Y' \<Longrightarrow> bind_spmf X Y = bind_spmf X Y'"
  by simp

lemma unpack_bind_spmf_fun: "X = X' \<Longrightarrow> bind_spmf X (\<lambda>y. f y) = bind_spmf X' (\<lambda>y. f y)"
  by (fact CryptHOL_ext.unpack_bind_spmf)

lemma unpack_try_spmf: "X = X' \<Longrightarrow> TRY X ELSE Y = TRY X' ELSE Y"
  by simp

lemma unpack_try_spmf': "Y = Y' \<Longrightarrow> TRY X ELSE Y = TRY X ELSE Y'"
  by simp

lemma spmf_eqI': "X = X' \<Longrightarrow> spmf X Y = spmf X' Y"
  by simp

subsection \<open>SPMF True\<close>

lemma return_spmf_assert: "TRY return_spmf X ELSE return_spmf False = 
  TRY bind_spmf (assert_spmf X) (\<lambda>_. return_spmf True) ELSE return_spmf False"
  by (simp add: try_bind_assert_spmf)

lemma bind_spmf_independent_return_spmf: 
  "lossless_spmf x \<Longrightarrow> bind_spmf x (\<lambda>x. return_spmf y) = return_spmf y"
  by (simp add: bind_eq_return_spmf)
  
lemma bind_spmf_le:
  "(\<And>x. spmf (f x) True \<le> spmf (f' x) True) \<Longrightarrow> spmf (bind_spmf p f) True \<le> spmf (bind_spmf p f') True"
  apply (simp add: spmf_bind integral_measure_spmf)
    apply (rule integral_mono)
      apply (rule integrableI_bounded)
       apply simp
      apply (smt (verit, del_insts) ennreal_less_top ennreal_spmf_bind infinity_ennreal_def nn_integral_cong pmf_nonneg real_norm_def)
     apply (rule integrableI_bounded)
      apply simp
     apply (smt (verit, del_insts) ennreal_less_top ennreal_spmf_bind infinity_ennreal_def nn_integral_cong pmf_nonneg real_norm_def)
    apply simp
  done
(*
lemma bind_spmf_le': 
  "(spmf p True \<le> spmf (p') True) \<Longrightarrow> spmf (bind_spmf p f) True \<le> spmf (bind_spmf p' f) True"
  sorry*)

lemma try_spmf_eq:
  assumes "spmf x True = spmf x' True"
  shows "spmf (TRY x ELSE return_spmf False) True = spmf (TRY x' ELSE return_spmf False) True"
  apply (simp add: spmf_try_spmf)
  apply (rule assms)
  done
  
lemma try_spmf_le:
  assumes "spmf x True \<le> spmf x' True"
  shows "spmf (TRY x ELSE return_spmf False) True \<le> spmf (TRY x' ELSE return_spmf False) True"
  apply (rule ennreal_spmf)
  apply (simp add: spmf_try_spmf)
  apply (rule assms)
  done

lemma try_spmf_true_else_false_le: "spmf (TRY X ELSE return_spmf False) True \<le> spmf X True"   
  by (simp add: spmf_try_spmf)

lemma del_assert: "spmf (bind_spmf (assert_spmf X) (\<lambda>_ . Y)) True \<le> spmf Y True"
  apply (rule ennreal_spmf)
  apply (simp add: spmf_try_spmf ennreal_spmf_bind)
  apply (simp add: mult_left_le measure_spmf.emeasure_space_le_1)
  done

lemma assert_ret_unit: "bind_spmf (assert_spmf x) (\<lambda>x . y) = bind_spmf (assert_spmf x) (\<lambda>_ . y)"
  by presburger

lemma assert_based_eq: 
  assumes "x \<Longrightarrow> y = y'"
  shows "bind_spmf (assert_spmf x) (\<lambda>_ . y)
  = bind_spmf (assert_spmf x) (\<lambda>_ . y')"
  by (auto simp add: assms assert_spmf_def)

lemma assert_commute: "bind_spmf X (\<lambda>x. bind_spmf (assert_spmf Y) (\<lambda>_. Z x)) 
  = bind_spmf (assert_spmf Y) (\<lambda>_. bind_spmf X (\<lambda>x. Z x))"
  by (rule bind_commute_spmf)

thm assert_commute[symmetric]

lemma assert_collapse: "bind_spmf (assert_spmf X) (\<lambda>_. bind_spmf (assert_spmf Y) (\<lambda>_. Z)) = 
   bind_spmf (assert_spmf (X \<and> Y)) (\<lambda>_. Z)"
  by (smt (verit) assert_spmf_simps(1,2) return_None_bind_spmf return_bind_spmf)

lemma assert_cong: " X = Y \<Longrightarrow> rel_spmf (=) (assert_spmf X) (assert_spmf Y)"
  by (simp add: spmf_rel_eq)

lemma rel_spmf_bind_assert_reflI: "(Z \<Longrightarrow> rel_spmf P X Y) \<Longrightarrow> 
  rel_spmf P (bind_spmf (assert_spmf Z) (\<lambda>_. X)) (bind_spmf (assert_spmf Z) (\<lambda>_. Y))"
  using rel_spmf_bind_reflI by fastforce


end
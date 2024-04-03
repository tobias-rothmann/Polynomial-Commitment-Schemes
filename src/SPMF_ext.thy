theory SPMF_ext

imports CryptHOL.Cyclic_Group_SPMF "HOL-Computational_Algebra.Polynomial" 
  Berlekamp_Zassenhaus.Finite_Field

begin

lemma assert_anding[symmetric]: "TRY do {
          _ :: unit \<leftarrow> assert_spmf (a);
            _ :: unit \<leftarrow> assert_spmf (b);
            return_spmf True
        } ELSE return_spmf False 
    = TRY do {
          _ :: unit \<leftarrow> assert_spmf (a \<and> b);
          return_spmf True
      } ELSE return_spmf False"
  by (simp add: try_bind_assert_spmf) 

lemma 
  spmf_reduction_2samples: 
  "spmf (TRY do {x \<leftarrow> X::'x spmf;
                 y \<leftarrow> (Y::'x \<Rightarrow> 'y spmf) x;
                 _::unit \<leftarrow> assert_spmf ((f::'x \<Rightarrow> 'y \<Rightarrow> bool) x y \<and> (q::'x\<Rightarrow>'y\<Rightarrow>bool) x y);
                 return_spmf True} ELSE return_spmf False) True 
 \<le> spmf (TRY do {x \<leftarrow> X::'x spmf;
                 y \<leftarrow> (Y::'x \<Rightarrow> 'y spmf) x;
                 _::unit \<leftarrow> assert_spmf ((f::'x \<Rightarrow> 'y \<Rightarrow> bool) x y);
                 return_spmf True} ELSE return_spmf False) True"
        (is "spmf (TRY ?game1 ELSE return_spmf False) True \<le> spmf (TRY ?game2 ELSE return_spmf False) True")
proof -
  have "ennreal (spmf ?game1 True) \<le> ennreal (spmf ?game2 True)"
    apply (simp add: ennreal_spmf_bind)
    apply (rule nn_integral_mono)+
    apply (simp add: assert_spmf_def)
    done
  then show ?thesis
    by (simp add: spmf_try_spmf)
qed

lemma 
  spmf_reduction_3samples: 
  "spmf (TRY do {x \<leftarrow> X::'x spmf;
                 y \<leftarrow> (Y::'x \<Rightarrow> 'y spmf) x;
                 z \<leftarrow> (Z::'x\<Rightarrow>'y\<Rightarrow>'z spmf) x y;
                 _::unit \<leftarrow> assert_spmf ((f::'x \<Rightarrow> 'y \<Rightarrow> 'z \<Rightarrow> bool) x y z \<and> (q::'x\<Rightarrow>'y\<Rightarrow>'z\<Rightarrow>bool) x y z);
                 return_spmf ((A::'x \<Rightarrow>'y\<Rightarrow>'z \<Rightarrow> bool) x y z)} ELSE return_spmf False) True 
 \<le>spmf (TRY do {x \<leftarrow> X::'x spmf;
                 y \<leftarrow> (Y::'x \<Rightarrow> 'y spmf) x;
                 z \<leftarrow> (Z::'x\<Rightarrow>'y\<Rightarrow>'z spmf) x y;
                 _::unit \<leftarrow> assert_spmf ((f::'x \<Rightarrow> 'y \<Rightarrow> 'z \<Rightarrow> bool) x y z);
                 return_spmf ((A::'x \<Rightarrow>'y\<Rightarrow>'z \<Rightarrow> bool) x y z)} ELSE return_spmf False) True "
        (is "spmf (TRY ?game1 ELSE return_spmf False) True \<le> spmf (TRY ?game2 ELSE return_spmf False) True")
proof -
  have "ennreal (spmf ?game1 True) \<le> ennreal (spmf ?game2 True)"
    apply (simp add: ennreal_spmf_bind)
    apply (rule nn_integral_mono)+
    apply (simp add: assert_spmf_def)
    done
  then show ?thesis
    by (simp add: spmf_try_spmf)
qed

lemma 
  spmf_del_assert_3samples: 
  "spmf (TRY do {x \<leftarrow> X::'x spmf;
                 y \<leftarrow> (Y::'x \<Rightarrow> 'y spmf) x;
                 z \<leftarrow> (Z::'x\<Rightarrow>'y\<Rightarrow>'z spmf) x y;
                 _::unit \<leftarrow> assert_spmf ((f::'x \<Rightarrow> 'y \<Rightarrow> 'z \<Rightarrow> bool) x y z);
                 return_spmf ((A::'x \<Rightarrow>'y\<Rightarrow>'z \<Rightarrow> bool) x y z)} ELSE return_spmf False) True 
 \<le>spmf (TRY do {x \<leftarrow> X::'x spmf;
                 y \<leftarrow> (Y::'x \<Rightarrow> 'y spmf) x;
                 z \<leftarrow> (Z::'x\<Rightarrow>'y\<Rightarrow>'z spmf) x y;
                 return_spmf ((A::'x \<Rightarrow>'y\<Rightarrow>'z \<Rightarrow> bool) x y z)} ELSE return_spmf False) True "
        (is "spmf (TRY ?game1 ELSE return_spmf False) True \<le> spmf (TRY ?game2 ELSE return_spmf False) True")
proof -
  have "ennreal (spmf ?game1 True) \<le> ennreal (spmf ?game2 True)"
    apply (simp add: ennreal_spmf_bind)
    apply (rule nn_integral_mono)+
    apply (simp add: assert_spmf_def measure_spmf.emeasure_eq_measure)
    done
  then show ?thesis
    by (simp add: spmf_try_spmf)
qed

end
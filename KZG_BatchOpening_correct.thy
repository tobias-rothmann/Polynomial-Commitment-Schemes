theory KZG_BatchOpening_correct

imports KZG_BatchOpening_Def KZG_correct
begin

locale KZG_BatchOpening_correct = KZG_BatchOpening_def + KZG_correct
begin

text \<open>We show that the game played an honest comitter and honest verfier has guranteed success, 
i.e. success probability 1.\<close>

text \<open>We define the honestly played game as invoking the KZG functions in a commit and 
batch evaluate process.\<close>
definition BatchEval_game:: "'e polynomial \<Rightarrow> 'e eval_position set \<Rightarrow> bool spmf"
  where "BatchEval_game \<phi> B = 
    do{
    (\<alpha>,PK) \<leftarrow> Setup;
    let C = Commit PK \<phi>;
    let (B', r_x, w_B) = CreateWitnessBatch PK \<phi> B;
    return_spmf (VerifyEvalBatch PK C B' r_x w_B)
    }"

text \<open>We show the pairing check performed by VerifyEvalVBatch by values (e.g. with g^\<phi>(\<alpha>) instead 
of the commitment C). This enables us to prove that a the pairing check holds for e.g. a correctly 
computed commitment.\<close>
lemma eq_on_e_Batch: "(e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>\<^sub>B B \<phi>) \<alpha>) 
  \<otimes>\<^bsub>G\<^sub>T\<^esub> (e \<^bold>g (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (r B \<phi>) \<alpha>)) 
  = e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly \<phi> \<alpha>) \<^bold>g)"
proof -
  have "(poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>) * ( poly (\<psi>\<^sub>B B \<phi>) \<alpha>) + poly (r B \<phi>) \<alpha> = poly \<phi> \<alpha>"
    by (metis (no_types, lifting) \<psi>\<^sub>B.simps add.commute add_diff_cancel_right' div_poly_eq_0_iff minus_mod_eq_mult_div mod_div_mult_eq nonzero_mult_div_cancel_left poly_hom.hom_add poly_mult r.elims)
  then show ?thesis 
    using e_bilinear e_linear_in_fst e_linear_in_snd by fastforce
qed

text \<open>Finally we show the success probability of the honestly played game is 1 on valid inputs.\<close>
theorem Eval_Commit_correct:  
  assumes "degree \<phi> \<le> max_deg"
  and "card B < max_deg"
  shows "spmf (BatchEval_game \<phi> B) True = 1"
proof -
   text \<open>show that g^(\<psi>B(\<alpha>)) is correctly computed using a correct public key PK\<close>
   have g_pow_\<psi>B: "\<forall>x. g_pow_PK_Prod
                   (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int x) ^ t) [0..<max_deg + 1])
                   (\<psi>\<^sub>B B \<phi>) =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>\<^sub>B B \<phi>) (of_int_mod_ring (int x))"
     using deg_\<psi>\<^sub>B g_pow_PK_Prod_correct le_trans assms(1) by blast 
   text \<open>show that g^(r(\<alpha>)) is correctly computed using a correct public key PK\<close>
   have g_pow_rB: "\<forall>x. g_pow_PK_Prod
                   (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int x) ^ t) [0..<max_deg + 1])
                   (r B \<phi>) =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (r B \<phi>) (of_int_mod_ring (int x))"
     using deg_r g_pow_PK_Prod_correct le_trans assms(1) by blast
   text \<open>show that g^(\<Prod>i\<in>B.(\<alpha>-i)) is correctly computed using a correct public key PK\<close>
   have g_ow_Prod: "\<forall>x. g_pow_PK_Prod
                   (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int x) ^ t) [0..<max_deg + 1])
                   (\<Prod>i\<in>B. [:- i, 1:]) =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly  (\<Prod>i\<in>B. [:- i, 1:]) (of_int_mod_ring (int x))"
     using deg_Prod g_pow_PK_Prod_correct le_trans assms(2) less_imp_le_nat by presburger

  text \<open>unfold Setup to gain access to the definiton of the public key PK. This step is necessary 
  to be able to use the conversions showed above\<close>
  have "spmf (BatchEval_game \<phi> B) True = 
    spmf (do{
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    let C = Commit PK \<phi>;
    let (B', r_x, w_B) = CreateWitnessBatch PK \<phi> B;
    return_spmf (VerifyEvalBatch PK C B' r_x w_B)
    }) True"
    unfolding BatchEval_game_def Setup_def Let_def
    by force
  text \<open>transform the computation from the functions into values.\<close>
  also have "\<dots> = spmf (do{
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    return_spmf (
    e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (\<Prod>i\<in>B. [:- i, 1:]) (of_int_mod_ring (int x))) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>\<^sub>B B \<phi>) (of_int_mod_ring (int x))) 
  \<otimes>\<^bsub>G\<^sub>T\<^esub> (e \<^bold>g (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (r B \<phi>) (of_int_mod_ring (int x)))) 
  = e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly \<phi> (of_int_mod_ring (int x))) \<^bold>g)
    }) True"
    unfolding CreateWitnessBatch_def VerifyEvalBatch_def Commit_def Let_def split_def
    g_pow_PK_Prod_correct[OF assms(1)]
    using g_pow_\<psi>B g_pow_rB g_ow_Prod
    by force
  text \<open>Use the pairing equality by value showed in 'eq_on_e_Batch' to conclude that the game simply 
  returns True i.e. has a success probability of 1.\<close>
  also have "\<dots> = spmf (do{
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    return_spmf (True
  )}) True"
    using eq_on_e_Batch deg_Prod by algebra
  also have "\<dots> = spmf (scale_spmf (weight_spmf (sample_uniform (Coset.order G\<^sub>p))) (return_spmf True)) True"
    using bind_spmf_const[of "sample_uniform (Coset.order G\<^sub>p)" "return_spmf True"] by presburger
  also have "\<dots> = 1"
    using weight_sample_uniform_gt_0 CARD_G\<^sub>p p_gr_two by simp
  finally show ?thesis .
qed


end

end
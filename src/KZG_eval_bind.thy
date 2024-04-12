theory KZG_eval_bind

imports KZG_correct "tSDH_assumption"

begin

locale bind_game_def = KZG_correct
begin

section \<open>Definitions for the evaluation binding game, mirroring the KZG evaluation commit phase\<close>

text \<open>We define the evaluation binding game, the reduction to the t-SDH assumption as well as any 
functions needed to construct them in this locale. This file contains another locale below which 
contains the proof.\<close>

text \<open>valid_msg ensures that the supplied witness w_i is a group element of Gp. 
Sadly cyclic groups are not constructed by type, which is why this check is necessary. 
A element of type 'a is not necessarily a group element of Gp.\<close>
definition valid_msg :: "'e eval_value \<Rightarrow> 'a eval_witness \<Rightarrow> bool" where 
  "valid_msg \<phi>_i w_i = (w_i \<in> carrier G\<^sub>p)"
                    
subsection \<open>Game definition\<close>

type_synonym ('a', 'e')  adversary = 
  "'a' pk \<Rightarrow> 
 ('a' commit \<times> 'e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness \<times> 'e' eval_value \<times> 'a' eval_witness) spmf"

text \<open>This is the formalized evaluation binding game\<close>
definition bind_game :: "('a, 'e) adversary \<Rightarrow> bool spmf"
  where "bind_game \<A> = TRY do {
  PK \<leftarrow> KeyGen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i); 
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEval PK C i \<phi>'_i w'_i;
  return_spmf (b \<and> b')} ELSE return_spmf False"

text \<open>The advantage of the adversary over the evaluation binding game is the probabillity that it 
wins.\<close>
definition bind_advantage :: "('a, 'e) adversary \<Rightarrow> real"
  where "bind_advantage \<A> \<equiv> spmf (bind_game \<A>) True"
                                                        
subsection \<open>t-SDH game\<close> 

text \<open>We instantiate the t-SDH game for the group Gp\<close>
sublocale t_SDH_G\<^sub>p: t_SDH G\<^sub>p max_deg "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding t_SDH_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

subsection \<open>Defining a reduction adversary from evaluation binding to t-SDH\<close>

text \<open>The reduction function takes a adversary for the evaluation binding game and returns an 
adversary for the t-SDH game. Specifically, the reduction uses the evaluation binding adversary to 
construct a winning strategy for the t-SDH game (i.e. to win it every time).
Essentially, it uses the fact that the values supplied by the adversary already break the t-SDH 
assumption.\<close>
fun bind_reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e) t_SDH.adversary"                     
where
  "bind_reduction \<A> PK = do {
  (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval PK C i \<phi>_of_i w_i 
                            \<and> VerifyEval PK C i \<phi>'_of_i w'_i
                            ); 
  return_spmf (-i::'e mod_ring, (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)) )}"
end

text \<open>This locale captures the proof for the definitions provided earlier\<close>
locale bind_game_proof = bind_game_def
begin

subsubsection \<open>helping lemmas\<close>

text \<open>An alternative but equivalent game for the evaluation binding game. 
This alternative game capsulates the 
event that the Adversary wins in the assert_spmf statement.
It's a closely adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def\<close>
lemma bind_game_alt_def:
  "bind_game \<A> = TRY do {
  PK \<leftarrow> KeyGen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEval PK C i \<phi>'_i w'_i;
  _ :: unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do {
      PK \<leftarrow> KeyGen;
      TRY do {
        (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
          TRY return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> VerifyEval PK C i \<phi>'_i w'_i) ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding split_def bind_game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      PK \<leftarrow> KeyGen;
      TRY do {
        (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (VerifyEval PK C i \<phi>_i w_i \<and> VerifyEval PK C i \<phi>'_i w'_i);
            return_spmf True
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"   
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = ?rhs"
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  finally show ?thesis .
qed

text \<open>merging assert statements together\<close>
lemma assert_anding: "TRY do {
          _ :: unit \<leftarrow> assert_spmf (a);
            _ :: unit \<leftarrow> assert_spmf (b);
            return_spmf True
        } ELSE return_spmf False 
    = TRY do {
          _ :: unit \<leftarrow> assert_spmf (a \<and> b);
          return_spmf True
      } ELSE return_spmf False"
  by (simp add: try_bind_assert_spmf) 

text \<open>show that VerifyEval on two evaluations, \<phi>_of_i and \<phi>'_of_i, for the same point i, implies 
that the t-SDH is broken.
This lemma captures that the adversaries messages already break the t-SDH assumption.\<close>
lemma two_eval_verify_imp_tSDH_break: 
  assumes "\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
        \<and> w_i \<in> carrier G\<^sub>p \<and>  w'_i \<in> carrier G\<^sub>p
        \<and> VerifyEval ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<alpha>)^t)) [0..<max_deg+1])) C i \<phi>_of_i w_i 
        \<and> VerifyEval ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<alpha>)^t)) [0..<max_deg+1])) C i \<phi>'_of_i w'_i"
  shows "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha> + (-i))) 
                              = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i))"
proof -
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<alpha>)^t)) [0..<max_deg+1])"
  obtain \<psi>\<^sub>i where \<psi>\<^sub>i: "w_i = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<psi>\<^sub>i"
    by (metis G\<^sub>p.generatorE assms g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)
  obtain \<psi>\<^sub>i' where \<psi>\<^sub>i': "w'_i = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<psi>\<^sub>i'"
    by (metis G\<^sub>p.generatorE assms g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)

  text \<open>the proof is essentially rearranging equations, an outline can be found in the 
  evaluation binding proof section in the thesis paper.\<close> 
  have "e w_i ((\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i)
      = e w'_i ((\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>'_of_i)"
    using assms unfolding VerifyEval_def
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 d_pos le_imp_less_Suc less_eq_Suc_le nth_map_upt power_one_right verit_minus_simplify(2))
  then have "e w_i (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>-i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i)
      = e w'_i (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>-i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>'_of_i)"
    using mod_ring_pow_mult_inv_G\<^sub>p by presburger
  then have "e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<psi>\<^sub>i) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>-i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i)
      = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<psi>\<^sub>i') (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>-i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>'_of_i)"
    using \<psi>\<^sub>i \<psi>\<^sub>i' by fast
  then have "(e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> (\<psi>\<^sub>i * (\<alpha>-i) + \<phi>_of_i)
      = (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> (\<psi>\<^sub>i' * (\<alpha>-i) + \<phi>'_of_i)"
    using e_bilinear by force
  then have "\<psi>\<^sub>i * (\<alpha>-i) + \<phi>_of_i = \<psi>\<^sub>i' * (\<alpha>-i) + \<phi>'_of_i"
    using pow_on_eq_card_GT_carrier_ext'
    by blast
  then have "(\<psi>\<^sub>i - \<psi>\<^sub>i') * (\<alpha>-i) = \<phi>'_of_i - \<phi>_of_i"
    by (simp add: algebra_simps)
  then have "(\<psi>\<^sub>i - \<psi>\<^sub>i')/(\<phi>'_of_i - \<phi>_of_i) = 1/(\<alpha>-i)"
    by (metis \<psi>\<^sub>i \<psi>\<^sub>i' assms divide_divide_eq_left divide_self_if eq_iff_diff_eq_0)
  moreover have "(w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<psi>\<^sub>i - \<psi>\<^sub>i')/(\<phi>'_of_i - \<phi>_of_i))"
  proof -
    have "(w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)) 
        = ((\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<psi>\<^sub>i) \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<psi>\<^sub>i')) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i))"
      using \<psi>\<^sub>i \<psi>\<^sub>i' by fast
    also have "\<dots> = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<psi>\<^sub>i - \<psi>\<^sub>i')) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i))"
      using mod_ring_pow_mult_inv_G\<^sub>p by presburger
    also have "\<dots> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<psi>\<^sub>i - \<psi>\<^sub>i')/(\<phi>'_of_i - \<phi>_of_i))"
      by (metis mod_ring_pow_pow_G\<^sub>p times_divide_eq_right verit_prod_simplify(2))
    finally show ?thesis .
  qed
  ultimately show ?thesis by fastforce
qed

subsubsection \<open>literal helping lemmas\<close>

text \<open>CryptHOL has some difficulties with simplifying, thus we need to use literal helping lemmas, 
that state the equalities we want to exchange literally.\<close>

lemma add_witness_neq_if_eval_neq: "\<phi>_i \<noteq> \<phi>'_i
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg \<phi>'_i w'_i
                            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>_i w_i 
                            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>'_i w'_i 
                        \<longleftrightarrow>                                       
                            \<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg \<phi>'_i w'_i
                            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>_i w_i 
                            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>'_i w'_i"
proof 
  assume asm: "\<phi>_i \<noteq> \<phi>'_i
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg \<phi>'_i w'_i
            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>_i w_i 
            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>'_i w'_i "
  have "w_i \<noteq> w'_i"
  proof -
    obtain w_i_pow where w_i_pow: "w_i = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> w_i_pow" 
      using asm 
      unfolding valid_msg_def
      by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)
    obtain w'_i_pow where w'_i_pow: "w'_i = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> w'_i_pow" 
      using asm 
      unfolding valid_msg_def
      by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)

      from asm
      have "e w_i ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) ! 1 \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i 
          =e w'_i ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) ! 1 \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>'_i " unfolding VerifyEval_def by force
      then have "e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> w_i_pow) ((\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i 
          =e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> w'_i_pow) ((\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>'_i"
        using PK_i w_i_pow w'_i_pow
        using add.commute add_diff_cancel_right' d_pos landau_product_preprocess(52) length_upt less_diff_conv nth_map nth_upt power_one_right
        by auto
      then have "e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (w_i_pow * (\<alpha> - i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i 
          =e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (w'_i_pow * (\<alpha> - i))
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>'_i"
        by (metis G\<^sub>p.generator_closed e_bilinear mod_ring_pow_mult_inv_G\<^sub>p)
      then have "e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (w_i_pow * (\<alpha> - i) + \<phi>_i)
          =e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (w'_i_pow * (\<alpha> - i) + \<phi>'_i)"
        by fastforce
      then have "w_i_pow * (\<alpha> - i) + \<phi>_i = w'_i_pow * (\<alpha> - i) + \<phi>'_i"
        by simp
      then have "w_i_pow \<noteq> w'_i_pow" using asm by force
      
      then show ?thesis 
        using w_i_pow w'_i_pow pow_on_eq_card by presburger
    qed
  then show "\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
          \<and> valid_msg \<phi>_i w_i 
          \<and> valid_msg \<phi>'_i w'_i
          \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>_i w_i 
          \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>'_i w'_i"
    using asm by fast
qed fast

lemma helping_1: "\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<alpha>)^t)) [0..<max_deg+1])) C i \<phi>_of_i w_i 
                            \<and> VerifyEval ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])) C i \<phi>'_of_i w'_i
                            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha> + (-i))) 
                              = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)) 
\<longleftrightarrow> 
                  \<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])) C i \<phi>_of_i w_i 
                            \<and> VerifyEval ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])) C i \<phi>'_of_i w'_i"
  using two_eval_verify_imp_tSDH_break unfolding valid_msg_def by meson

subsection \<open>KZG eval bind game to reduction game - equivalence theorem\<close>

text \<open>We show that the binding game is equivalent to the t-SDH game with the reduction adversary
(with added asserts)\<close>

theorem eval_bind_game_eq_t_SDH_strong_red:
  shows "bind_game \<A> = t_SDH_G\<^sub>p.game (bind_reduction \<A>)"
proof -
  note [simp] = Let_def split_def

  text \<open>abbreviations for the mod_ring version of sample uniform nat 
  and the public key\<close>
  let ?\<alpha> = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>)^t)) [0..<max_deg+1])"

  have "t_SDH_G\<^sub>p.game (bind_reduction \<A>) = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i 
                            \<and> valid_msg \<phi>_of_i w_i 
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>'_of_i w'_i);
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False"
    by (force simp add: t_SDH_G\<^sub>p.game_alt_def[of "(bind_reduction \<A>)"])
  text \<open>Add the fact that witnesses have to be unequal if evaluations are unequal for a easier 
        proof.\<close>
  also have "\<dots> =  TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i
                            \<and> valid_msg \<phi>_of_i w_i 
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>'_of_i w'_i);
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False"
    using add_witness_neq_if_eval_neq by presburger
  text \<open>Goal is to erase the second assert statement, such that we just end up with the 
  evaluation_game. To do that, we first merge the two asserts and show that the first assert's 
  statement implies the second one's statement, hence we can leave the second assert's statement 
  out and are left with only the first assert statement.\<close>
  also have "\<dots> = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>'_of_i w'_i);
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False 
  } ELSE return_spmf False 
  } ELSE return_spmf False "
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>'_of_i w'_i
                            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) 
                              = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False 
  } ELSE return_spmf False 
  } ELSE return_spmf False "  
    using assert_anding by presburger
 also have "\<dots> = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>'_of_i w'_i
                            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) 
                              = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False"  
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  text \<open>We use the equivalence to erase the assert-term that t-SDH is broken, as it is not 
  contained in the evaluation binding game.\<close>
  also have "\<dots> = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>'_of_i w'_i);
    return_spmf True 
  } ELSE return_spmf False"  
   using helping_1 by algebra 
 text \<open>remove additional assert-term about the witnesses inequality\<close>
 also have "\<dots> = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> VerifyEval (?PK \<alpha>) C i \<phi>'_of_i w'_i);
    return_spmf True 
  } ELSE return_spmf False"  
   using add_witness_neq_if_eval_neq by algebra
  text \<open>form the KeyGen function from the uniformly sampled alpha\<close>
  also have "\<dots> = TRY do { 
    PK \<leftarrow> KeyGen;
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval PK C i \<phi>_of_i w_i 
                            \<and> VerifyEval PK C i \<phi>'_of_i w'_i);
    return_spmf True 
  } ELSE return_spmf False"
    unfolding KeyGen_def Setup_def by simp
  text \<open>split the accumulated assert, to obtain the sequence in the evaluation binding game\<close>
  also have "\<dots> = TRY do {
  PK \<leftarrow> KeyGen;
  TRY do {
    (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
      TRY do {
      _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i  
                                \<and> valid_msg \<phi>_i w_i 
                                \<and> valid_msg \<phi>'_i w'_i
                                \<and> VerifyEval PK C i \<phi>_i w_i 
                                \<and> VerifyEval PK C i \<phi>'_i w'_i);  
      return_spmf True
      } ELSE return_spmf False 
    } ELSE return_spmf False 
  } ELSE return_spmf False"
  unfolding split_def Let_def
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also  have "\<dots> = TRY do {
  PK \<leftarrow> KeyGen;
    TRY do {
    (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
      TRY do {
      _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
      _ :: unit \<leftarrow> assert_spmf (VerifyEval PK C i \<phi>_i w_i \<and> VerifyEval PK C i \<phi>'_i w'_i);  
      return_spmf True
      } ELSE return_spmf False 
    } ELSE return_spmf False 
  } ELSE return_spmf False"  
    using assert_anding by presburger
  also  have "\<dots> = TRY do {
  PK \<leftarrow> KeyGen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
  _ :: unit \<leftarrow> assert_spmf (VerifyEval PK C i \<phi>_i w_i \<and> VerifyEval PK C i \<phi>'_i w'_i);  
  return_spmf True} ELSE return_spmf False"
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots>=bind_game \<A>"
     using bind_game_alt_def by presburger
  finally show ?thesis unfolding bind_game_def t_SDH_G\<^sub>p.game_def ..
qed

text \<open>Finally conclude that for every efficient adversary the advantage of winning the 
evaluation binding game is less than or equal to breaking the t-SDH assumption.\<close>
theorem evaluation_binding: "bind_advantage \<A> = t_SDH_G\<^sub>p.advantage (bind_reduction \<A>)"
  unfolding bind_advantage_def t_SDH_G\<^sub>p.advantage_def
  using eval_bind_game_eq_t_SDH_strong_red by presburger
  
end

end
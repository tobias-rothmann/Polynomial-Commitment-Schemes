theory KZG_BatchOpening_binding

imports KZG_eval_bind KZG_BatchOpening_correct tBSDH_assumption SPMF_ext
begin

locale bind_game_def = KZG_BatchOpening_correct
begin

section \<open>Definitions for the evaluation binding game for the batched KZG\<close>

text \<open>We define the evaluation binding game, the reduction to the t-BSDH assumption as well as any 
functions needed to construct them in this locale. This file contains another locale below which 
contains the proof.\<close>

text \<open>valid_msg ensures that the supplied witness w_i is a group element of Gp. 
Sadly cyclic groups are not constructed by type, which is why this check is necessary. 
A element of type 'a is not necessarily a group element of Gp.\<close>
definition valid_msg :: "'e eval_value \<Rightarrow> 'a eval_witness \<Rightarrow> bool" where 
  "valid_msg \<phi>_i w_i = (w_i \<in> carrier G\<^sub>p)"

text \<open>valid_batch_msg similarly to valid_msg ensures that the supplied witness w_B is a group 
element of Gp. Furthermore, it ensures that the degree of r(x) is less than |B|, which is a 
prerequisist for r(x) to be valid as r(x) is the remainder of a divison by \<Prod>i\<in>B.(x-i). 
Additionally, it checks that B is not revealing more points than max_deg.\<close>
definition valid_batch_msg :: "'e polynomial \<Rightarrow> 'a eval_witness \<Rightarrow> 'e eval_position set \<Rightarrow> bool" where 
  "valid_batch_msg r_x w_B B = (w_B \<in> carrier G\<^sub>p \<and> degree r_x < card B \<and> card B < max_deg)"
                    
subsection \<open>Game definition\<close> 

type_synonym ('a', 'e')  adversary = 
  "'a' pk \<Rightarrow> 
 ('a' commit \<times> 'e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness \<times> 'e' eval_position set 
  \<times> 'a' eval_witness \<times> 'e' polynomial) spmf"

text \<open>This is the formalized evaluation binding game\<close>
definition bind_game :: "('a, 'e) adversary \<Rightarrow> bool spmf"
  where "bind_game \<A> = TRY do {
  PK \<leftarrow> KeyGen;
  (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEvalBatch PK C B r_x w_B;
  return_spmf (b \<and> b')} ELSE return_spmf False"

text \<open>The advantage of the adversary over the evaluation binding game is the probabillity that it 
wins.\<close>
definition bind_advantage :: "('a, 'e) adversary \<Rightarrow> real"
  where "bind_advantage \<A> \<equiv> spmf (bind_game \<A>) True"
                                                        
subsection \<open>t-BSDH game\<close>

text \<open>We instantiate the t-BSDH game for the pairing e, with  the group Gp as preimage group and GT 
as target group.\<close>
sublocale t_BSDH: t_BSDH G\<^sub>p G\<^sub>T max_deg "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p" "pow_mod_ring G\<^sub>T" e
  unfolding t_BSDH_def 
  using G\<^sub>T.cyclic_group_axioms G\<^sub>p.cyclic_group_axioms by presburger

subsection \<open>Defining a reduction game to t-BSDH\<close>

text \<open>The reduction function takes a adversary for the evaluation binding game and returns an 
adversary for the t-BSDH game. Specifically, the reduction uses the evaluation binding adversary to 
construct a winning strategy for the t-BSDH game (i.e. to win it every time).
Essentially, it uses the fact that the values supplied by the adversary already break the t-BSDH 
assumption.\<close>
fun reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e,'c) t_BSDH.adversary"                     
where
  "reduction \<A> PK = do {
   (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  let p' = g_pow_PK_Prod PK (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
  let r' = g_pow_PK_Prod PK ((r_x - [:poly r_x i:]) div [:-i,1:]);
  return_spmf (-i::'e mod_ring, (e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))) }"

end

text \<open>This locale captures the proof for the definitions provided earlier.
Note, the proof is structured analogly to the normal KZG's evaluation bidning proof.\<close>
locale bind_game_proof = bind_game_def
begin

text \<open>The reduction adversary extended for asserts that 
are present in the evalutaion binding game. We use this definition to show equivalence to 
the evaluation binding  game. Later on we can then easily over-estimate the probability 
from this extended version to the normal reduction.\<close>
fun ext_reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e,'c) t_BSDH.adversary"                     
where
  "ext_reduction \<A> PK = do {
   (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
  let p' = g_pow_PK_Prod PK (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
  let r' = g_pow_PK_Prod PK ((r_x - [:poly r_x i:]) div [:-i,1:]);
  return_spmf (-i::'e mod_ring, (e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))) }"

subsubsection \<open>helping lemmas\<close>

text \<open>An alternative but equivalent game for the evaluation binding game. 
This alternative game capsulates the 
event that the Adversary wins in the assert_spmf statement.
It's a closely adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def\<close>
lemma bind_game_alt_def:
  "bind_game \<A> = TRY do {
  PK \<leftarrow> KeyGen;
  (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEvalBatch PK C B r_x w_B;
  _::unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True} ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
    TRY do {
    let b = VerifyEval PK C i \<phi>_i w_i;
    let b' = VerifyEvalBatch PK C B r_x w_B;
    return_spmf (b \<and> b')
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding split_def bind_game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
    TRY do {
    let b = VerifyEval PK C i \<phi>_i w_i;
    let b' = VerifyEvalBatch PK C B r_x w_B;
    _::unit \<leftarrow> assert_spmf (b \<and> b');
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

text \<open>show that VerifyEvalBatch of B and r(x) and VerifEval on i\<in>B and \<phi>_i suhc that \<phi>_i \<noteq> r(x) 
implies that the t-BSDH is broken.
This lemma captures that the adversaries messages already break the t-BSDH assumption.\<close>
lemma verifys_impl_t_BSDH_break: 
  assumes 
    "i \<in> B \<and>  \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B \<and>
    VerifyEval (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) C i \<phi>_i w_i \<and>
    VerifyEvalBatch (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) C B r_x
                     w_B"
  shows " e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<alpha> + - i))
        =
          (e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1])
              ((\<Prod>i\<in>B. [:- i, 1:]) div [:- i, 1:]))
           w_B 
        \<otimes>\<^bsub>G\<^sub>T\<^esub>
          e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1])
              ((r_x - [:poly r_x i:]) div [:- i, 1:]) \<otimes>
             inv w_i)
           \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub>
          (1 / (\<phi>_i - poly r_x i))"
  (is "?goal = ?cmpt")
proof -
  obtain b where b: "w_B = \<^bold>g ^ b"
    using assms unfolding valid_batch_msg_def
    by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)
  obtain y where y: "w_i = \<^bold>g ^ y"
    using assms unfolding valid_msg_def
    by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)
  obtain r'_x where r'_x: "r'_x = (r_x - [:poly r_x i:]) div [:- i, 1:]" by blast
  then have r'_x_r_x: "r_x = r'_x *[:- i, 1:] + [:poly r_x i:]" 
    by (metis Groups.mult_ac(2) diff_eq_eq nonzero_mult_div_cancel_left one_neq_zero pCons_eq_0_iff synthetic_div_correct')
  obtain p'_x where p'_x:"p'_x = (\<Prod>i\<in>B. [:- i, 1:]) div [:- i, 1:]" by blast
  then have p'_x_p_x: "(\<Prod>i\<in>B. [:- i, 1:]) = p'_x *  [:- i, 1:]"
    using assms 
    by (metis (no_types, lifting) Groups.mult_ac(2) arith_extra_simps(6) i_in_B_prod_B_zero nonzero_mult_div_cancel_left one_neq_zero pCons_eq_0_iff synthetic_div_correct')

  text \<open>the proof is essentially rearranging equations, an outline can be found in the batched versions
  evaluation binding proof section in the thesis paper.\<close>
  from assms have "e w_i (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1] ! 1 \<otimes> inv (\<^bold>g ^ i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i
    = e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) (\<Prod>i\<in>B. [:- i, 1:])) w_B \<otimes>\<^bsub>G\<^sub>T\<^esub>
  e \<^bold>g (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) r_x)" (is "?lhs = ?rhs")
    unfolding VerifyEval_def VerifyEvalBatch_def Let_def by presburger
  moreover have "?lhs = e (\<^bold>g ^ y) (\<^bold>g ^ (\<alpha>-i) ) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i"
    unfolding y using PK_i d_pos mod_ring_pow_mult_inv_G\<^sub>p by auto
  moreover have "?rhs = e (\<^bold>g ^ poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>) (\<^bold>g ^ b) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g (\<^bold>g ^ poly r_x \<alpha>)"
  proof -
    have "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) (\<Prod>i\<in>B. [:- i, 1:]) 
        = \<^bold>g ^ poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>"
      using g_pow_PK_Prod_correct assms deg_Prod le_simps(1)
      unfolding valid_batch_msg_def by presburger
    moreover have "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) r_x = \<^bold>g ^ poly r_x \<alpha>"
      using g_pow_PK_Prod_correct assms unfolding VerifyEvalBatch_def 
      by (meson assms le_trans less_imp_le_nat valid_batch_msg_def)
    ultimately show ?thesis unfolding b by argo
  qed
  ultimately have "e (\<^bold>g ^ y) (\<^bold>g ^ (\<alpha>-i) ) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i = e (\<^bold>g ^ poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>) (\<^bold>g ^ b) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g (\<^bold>g ^ poly r_x \<alpha>)"
    by argo
  then have "y*(\<alpha>-i) + \<phi>_i = (poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>)*b + poly r_x \<alpha>"
    using e_bilinear e_linear_in_snd by force
  text \<open>mimicking steps from batching opening binding proof in the orginal paper. See Appendix C.3 in [KZG10]\<close>
  then have "(poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>)*b - (\<alpha>-i)*y = \<phi>_i -  poly r_x \<alpha>"
    by (metis (no_types, lifting) add_diff_cancel_left' add_diff_cancel_right' add_diff_eq mult.commute)
  then have "(poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>)*b - (\<alpha>-i)*y = \<phi>_i - (poly r'_x \<alpha>)*(\<alpha>-i) - poly [:poly r_x i:] \<alpha>"
    using r'_x_r_x poly_mult poly_add 
    by (metis (no_types, lifting) diff_diff_eq mult.right_neutral poly_const_conv poly_pCons uminus_add_conv_diff)
  then have "(\<alpha>-i)*(poly p'_x \<alpha>)*b - (\<alpha>-i)*y = \<phi>_i - (poly r'_x \<alpha>)*(\<alpha>-i) - poly [:poly r_x i:] \<alpha>"
    using p'_x_p_x
    by (metis (no_types, lifting) more_arith_simps(6) mpoly_base_conv(2) mult.commute poly_mult poly_pCons uminus_add_conv_diff)
  then have "(\<alpha>-i)*((poly p'_x \<alpha>)*b - y + poly r'_x \<alpha>) = \<phi>_i - poly [:poly r_x i:] \<alpha>"
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) Rings.ring_distribs(1) Rings.ring_distribs(4))
  then have "(\<alpha>-i)*((poly p'_x \<alpha>)*b - y + poly r'_x \<alpha>) = \<phi>_i - poly r_x i"
    by auto
  then have poly_eq_res: "1/(\<alpha>-i) = ((poly p'_x \<alpha>)*b - y + poly r'_x \<alpha>)/(\<phi>_i - poly r_x i)"
    by (metis (no_types, lifting) assms div_self divide_divide_eq_left mult.commute mult_eq_0_iff right_minus_eq)
  moreover have "?cmpt = (e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly p'_x \<alpha>)) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> b) \<otimes>\<^bsub>G\<^sub>T\<^esub> e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly r'_x \<alpha>) \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y))
     \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<phi>_i - poly r_x i))"
  proof -
    have "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) ((\<Prod>i\<in>B. [:- i, 1:]) div [:- i, 1:])
        = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly p'_x \<alpha>)" 
      unfolding p'_x 
      by (rule g_pow_PK_Prod_correct)(metis (no_types, lifting) assms valid_batch_msg_def deg_Prod deg_div le_trans nat_le_linear not_less)
    moreover have "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) ((r_x - [:poly r_x i:]) div [:- i, 1:])
      = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly r'_x \<alpha>)"
      unfolding r'_x 
      by (rule g_pow_PK_Prod_correct)(metis (mono_tags, opaque_lifting) assms deg_div degree_diff_le degree_pCons_0 le_trans less_or_eq_imp_le valid_batch_msg_def zero_le)
    ultimately show ?thesis unfolding y b by argo
  qed
  moreover have "\<dots> = e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (((poly p'_x \<alpha>)*b - y + poly r'_x \<alpha>)/(\<phi>_i - poly r_x i))"
  proof -
    have "(e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly p'_x \<alpha>) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> b) \<otimes>\<^bsub>G\<^sub>T\<^esub>
    e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly r'_x \<alpha> \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y)) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<phi>_i - poly r_x i)) 
    = (e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly p'_x \<alpha>) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> b) \<otimes>\<^bsub>G\<^sub>T\<^esub>
    e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly r'_x \<alpha> - y)) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<phi>_i - poly r_x i))"
      using mod_ring_pow_mult_inv_G\<^sub>p by presburger
    also have "\<dots> = (e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> ((poly p'_x \<alpha>)*b) \<otimes>\<^bsub>G\<^sub>T\<^esub>
    e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (poly r'_x \<alpha> - y)) ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<phi>_i - poly r_x i))"
      using e_linear_in_fst G\<^sub>p.generator_closed e_bilinear by presburger
    also have "\<dots> = (e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> ((poly p'_x \<alpha>)*b + poly r'_x \<alpha> - y)) ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<phi>_i - poly r_x i))"
      by (simp add: add_diff_eq)
    also have "\<dots> = e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (((poly p'_x \<alpha>)*b + poly r'_x \<alpha> - y)/(\<phi>_i - poly r_x i))"
      by (smt (verit) G\<^sub>p.generator_closed G\<^sub>p.int_pow_closed Groups.mult_ac(2) e_linear_in_snd mod_ring_pow_pow_G\<^sub>p more_arith_simps(5) times_divide_eq_right)
    finally show ?thesis by simp
  qed
  ultimately
  show ?thesis by fastforce
qed

subsection \<open>literal helping lemma\<close>

text \<open>CryptHOL has some difficulties with simplifying, thus we need to use literal helping lemmas, 
that state the equalities we want to exchange literally.\<close>

lemma literal_helping: 
  "(i \<in> (B::'e eval_position set) \<and>
                    (\<phi>_i:: 'e eval_value) \<noteq> (poly r_x i:: 'e eval_value) \<and>
                    valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B \<and> 
                    VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) C i \<phi>_i w_i \<and>
                    VerifyEvalBatch (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>::'e mod_ring) ^ t) [0..<max_deg + 1]) C B r_x w_B \<and>
                    e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<alpha> + - i)) =
                    (e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1])
                        ((\<Prod>i\<in>B. [:- i, 1:]) div [:- i, 1:]))
                     w_B \<otimes>\<^bsub>G\<^sub>T\<^esub>
                    e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1])
                        ((r_x - [:poly r_x i:]) div [:- i, 1:]) \<otimes>
                       inv w_i)
                     \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub>
                    ((1::'e mod_ring) / (\<phi>_i - poly r_x i)))
  \<longleftrightarrow>
  (i \<in> B \<and>
                    \<phi>_i \<noteq> poly r_x i \<and> 
                    valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B \<and>
                    VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) C i \<phi>_i w_i \<and>
                    VerifyEvalBatch (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) C B r_x
                     w_B)"
  using verifys_impl_t_BSDH_break by fast

subsection \<open>KZG eval bind game to reduction game - equivalence theorem\<close>

text \<open>We show that the binding game is equivalent to the t-BSDH game with the extended reduction 
adversary.\<close>
lemma bind_game_eq_t_BSDH_red: "bind_game \<A> = t_BSDH.game (ext_reduction \<A>)"
proof - 
  note [simp] = Let_def split_def

  text \<open>abbreviations for the mod_ring version of sample uniform nat 
  and the public key\<close>
  let ?mr = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?mr \<alpha>)^t)) [0..<max_deg+1])"

  text \<open>Firstly, unfold the t-BSDH game and the reduction adversary\<close>
  have "t_BSDH.game (ext_reduction \<A>) =  TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (c, g) \<leftarrow> (ext_reduction \<A>) (?PK \<alpha>);
    _::unit \<leftarrow> assert_spmf((e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+c)) = g);
    return_spmf True 
  } ELSE return_spmf False"
    unfolding t_BSDH.game_alt_def by (metis o_def)
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B);
    let p' = g_pow_PK_Prod (?PK \<alpha>) (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
    let r' = g_pow_PK_Prod (?PK \<alpha>) ((r_x - [:poly r_x i:]) div [:-i,1:]);
    _::unit \<leftarrow>  assert_spmf ((e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+(-i))) = (e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
    return_spmf True  
  } ELSE return_spmf False"
    by force
  text \<open>fold the two asserts together so we can reason about their joined content.\<close>
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B);
    let p' = g_pow_PK_Prod (?PK \<alpha>) (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
    let r' = g_pow_PK_Prod (?PK \<alpha>) ((r_x - [:poly r_x i:]) div [:-i,1:]);
    _::unit \<leftarrow>  assert_spmf ((e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+(-i))) = (e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
    return_spmf True  
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
  unfolding split_def Let_def
  by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
     let p' = g_pow_PK_Prod (?PK \<alpha>) (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
    let r' = g_pow_PK_Prod (?PK \<alpha>) ((r_x - [:poly r_x i:]) div [:-i,1:]);
    _ :: unit \<leftarrow> assert_spmf ( i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B
                              \<and> (e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+(-i))) 
                                = (e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
    return_spmf True  
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    using assert_anding by algebra
    also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    let p' = g_pow_PK_Prod (?PK \<alpha>) (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
    let r' = g_pow_PK_Prod (?PK \<alpha>) ((r_x - [:poly r_x i:]) div [:-i,1:]);
    _ :: unit \<leftarrow> assert_spmf ( i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B
                              \<and> (e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+(-i))) 
                                = (e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
    return_spmf True  
  } ELSE return_spmf False"
   unfolding split_def Let_def
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
 text \<open>erase the pairing check with he literal helping lemma to get closer to the eval bind game\<close>
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B); 
    return_spmf True  
  } ELSE return_spmf False"
    unfolding Let_def using literal_helping by algebra 
  text \<open>Split the message checks off the Evaluations checks, as it is done in the eval bind game\<close>
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B); 
    return_spmf True  
     } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
  unfolding split_def Let_def
  by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B);
    _ :: unit \<leftarrow> assert_spmf (VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B); 
    return_spmf True  
     } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False" 
    using assert_anding by algebra
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B);
    _ :: unit \<leftarrow> assert_spmf (VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B); 
    return_spmf True
  } ELSE return_spmf False" 
  unfolding split_def Let_def
  by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  text \<open>the obtained game is already the evaluation binding game.\<close>
  also have "\<dots>= bind_game \<A>"
    using bind_game_alt_def unfolding KeyGen_def Setup_def by simp
  finally show ?thesis ..
qed

text \<open>From the previous lemma we conclude that the adversarys advantage on winning the evaluation 
binding game is the same as winning the t-BSDH game with the extended reduction adversary.\<close>
lemma evaluation_binding_ext_red: "bind_advantage \<A> = t_BSDH.advantage (ext_reduction \<A>)"
  unfolding bind_advantage_def t_BSDH.advantage_def
  using bind_game_eq_t_BSDH_red by presburger

text \<open>Now we use overestimation to show that the advantage of winning the t-BSDH game with the 
extended reduction adversary is less than or equal to winning it with the normal reduction adversary.\<close>
lemma overestimate_reductions: "spmf (t_BSDH.game (ext_reduction \<A>)) True 
  \<le> spmf (t_BSDH.game (reduction \<A>)) True"
  (is "spmf ?lhgame True \<le> spmf ?rhgame True")
proof -
  note [simp] = Let_def split_def

  text \<open>abbreviations for the mod_ring version of sample uniform nat 
  and the public key\<close>
  let ?\<alpha> = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>)^t)) [0..<max_deg+1])"

  text \<open>We extend the t-BSDH game with the extended reduction adversary to a complete game.\<close>
  have bind_red_ext: "t_BSDH.game (ext_reduction \<A>) = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B);
    let p' = g_pow_PK_Prod (?PK \<alpha>) (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
    let r' = g_pow_PK_Prod (?PK \<alpha>) ((r_x - [:poly r_x i:]) div [:-i,1:]);
    _::unit \<leftarrow>  assert_spmf ((e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?\<alpha> \<alpha>)+(-i))) = (e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
    return_spmf True  
  } ELSE return_spmf False"
    by (force simp add: t_BSDH.game_alt_def[of "(ext_reduction \<A>)"])

  text \<open>We extend the t-BSDH game with reduction adversary to a complete game.\<close>
  have eval_bind_red_ext: "t_BSDH.game (reduction \<A>) = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    let p' = g_pow_PK_Prod (?PK \<alpha>) (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
    let r' = g_pow_PK_Prod (?PK \<alpha>) ((r_x - [:poly r_x i:]) div [:-i,1:]);
    _::unit \<leftarrow>  assert_spmf ((e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?\<alpha> \<alpha>)+(-i))) = (e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
    return_spmf True  
  } ELSE return_spmf False"
    by (force simp add: t_BSDH.game_alt_def[of "(reduction \<A>)"])

  text \<open>We show the thesis in ennreal, which implies the plain thesis\<close>
  have "ennreal (spmf (t_BSDH.game (ext_reduction \<A>)) True) 
    \<le> ennreal (spmf (t_BSDH.game (reduction \<A>)) True)"
    unfolding bind_red_ext eval_bind_red_ext
    apply (simp add: spmf_try_spmf ennreal_spmf_bind)
    apply (rule nn_integral_mono)+
    apply (simp add: assert_spmf_def)
    apply (simp add: measure_spmf.emeasure_eq_measure)
    done

  then show ?thesis by simp
qed

text \<open>Finally we put everything together: 
we conclude that for every efficient adversary the advantage of winning the 
evaluation binding game for the batched KZG is less than or equal to breaking the t-BSDH assumption.\<close>
theorem evaluation_binding: "bind_advantage \<A> \<le> t_BSDH.advantage (reduction \<A>)"
  using evaluation_binding_ext_red overestimate_reductions
  unfolding t_BSDH.advantage_def
  by algebra

end 

end
theory KZG_BatchOpening_binding

imports KZG_eval_bind KZG_BatchOpening_correct tBSDH_assumption
begin

locale bind_game_def = KZG_BatchOpening_correct
begin

text \<open>Expose just the public key from the Setup\<close>
definition key_gen:: "'a pk spmf" where
  "key_gen = do {
    (_::'e sk, PK::'a pk) \<leftarrow> Setup;
    return_spmf PK
  }"

definition valid_msg :: "'e eval_value \<Rightarrow> 'a eval_witness \<Rightarrow> bool" where 
  "valid_msg \<phi>_i w_i = (w_i \<in> carrier G\<^sub>p)"

definition valid_batch_msg :: "'e polynomial \<Rightarrow> 'a eval_witness \<Rightarrow> 'e eval_position set \<Rightarrow> bool" where 
  "valid_batch_msg r_x w_B B = (w_B \<in> carrier G\<^sub>p \<and> degree r_x < card B)"
                    
subsection \<open>Game definition\<close>

type_synonym ('a', 'e')  adversary = 
  "'a' pk \<Rightarrow> 
 ('a' commit \<times> 'e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness \<times> 'e' eval_position set 
  \<times> 'a' eval_witness \<times> 'e' polynomial) spmf"

definition bind_game :: "('a, 'e) adversary \<Rightarrow> bool spmf"
  where "bind_game \<A> = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEvalBatch PK C B r_x w_B;
  return_spmf (b \<and> b')} ELSE return_spmf False"

definition bind_advantage :: "('a, 'e) adversary \<Rightarrow> real"
  where "bind_advantage \<A> \<equiv> spmf (bind_game \<A>) True"
                                                        
subsection \<open>t-SDH game\<close>

sublocale t_BSDH: t_BSDH G\<^sub>p G\<^sub>T max_deg "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p" "pow_mod_ring G\<^sub>T" e
  unfolding t_BSDH_def 
  using G\<^sub>T.cyclic_group_axioms G\<^sub>p.cyclic_group_axioms by presburger

subsection \<open>Defining a reduction game to t-SDH\<close>

fun bind_reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e,'c) t_BSDH.adversary"                     
where
  "bind_reduction \<A> PK = do {
   (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
  let p' = g_pow_PK_Prod PK (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
  let r' = g_pow_PK_Prod PK ((r_x - [:poly r_x i:]) div [:-i,1:]);
  return_spmf (-i::'e mod_ring, e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))) }"

text \<open>An alternative but equivalent game for the binding game. 
This alternative game capsulates the 
event that the Adversary wins in the assert_spmf statement.
It's a closely adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def\<close>
lemma bind_game_alt_def:
  "bind_game \<A> = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEvalBatch PK C B r_x w_B;
  _::unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True} ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
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
    PK \<leftarrow> key_gen;
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
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

end

locale bind_game_proof = bind_game_def
begin

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

lemma verifys_impl_t_BSDH_break: 
  assumes 
    "card B < max_deg \<and> i \<in> B \<and>  \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B \<and>
    VerifyEval (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) C i \<phi>_i w_i \<and>
    VerifyEvalBatch (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) C B r_x
                     w_B"
  shows " e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<alpha> + - i))
        =
          e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1])
              ((\<Prod>i\<in>B. [:- i, 1:]) div [:- i, 1:]))
           w_B 
        \<otimes>\<^bsub>G\<^sub>T\<^esub>
          e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1])
              ((r_x - [:poly r_x i:]) div [:- i, 1:]) \<otimes>
             inv w_i)
           \<^bold>g ^\<^bsub>G\<^sub>T\<^esub>
          (1 / (\<phi>_i - poly r_x i))"
proof -
  obtain b where b: "w_B = \<^bold>g ^ b"
    using assms unfolding valid_batch_msg_def
    by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)
  obtain y where y: "w_i = \<^bold>g ^ y"
    using assms unfolding valid_msg_def
    by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)

  from assms have "e w_i (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1] ! 1 \<otimes> inv (\<^bold>g ^ i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i
    = e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) (\<Prod>i\<in>B. [:- i, 1:])) w_B \<otimes>\<^bsub>G\<^sub>T\<^esub>
  e \<^bold>g (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) r_x)" (is "?lhs = ?rhs")
    unfolding VerifyEval_def VerifyEvalBatch_def Let_def by presburger
  moreover have "?lhs = e (\<^bold>g ^ y) (\<^bold>g ^ (\<alpha>-i) ) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i"
    unfolding y using PK_i d_pos mod_ring_pow_mult_inv_G\<^sub>p by auto
  moreover have "?rhs = e (\<^bold>g ^ poly (\<Prod>i\<in>B. [:- i, 1:]) \<alpha>) (\<^bold>g ^ b) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g (\<^bold>g ^ poly r_x \<alpha>)"
    using g_pow_PK_Prod_correct sorry
  show ?thesis
    using assms unfolding VerifyEval_def VerifyEvalBatch_def Let_def
    
    sorry
qed

lemma literal_helping: 
  "(card B < max_deg \<and> i \<in> (B::'e eval_position set) \<and>
                    (\<phi>_i:: 'e eval_value) \<noteq> (poly r_x i:: 'e eval_value) \<and>
                    valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B \<and> 
                    VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) C i \<phi>_i w_i \<and>
                    VerifyEvalBatch (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>::'e mod_ring) ^ t) [0..<max_deg + 1]) C B r_x w_B \<and>
                    e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1 / (\<alpha> + - i)) =
                    e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1])
                        ((\<Prod>i\<in>B. [:- i, 1:]) div [:- i, 1:]))
                     w_B \<otimes>\<^bsub>G\<^sub>T\<^esub>
                    e (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1])
                        ((r_x - [:poly r_x i:]) div [:- i, 1:]) \<otimes>
                       inv w_i)
                     \<^bold>g ^\<^bsub>G\<^sub>T\<^esub>
                    ((1::'e mod_ring) / (\<phi>_i - poly r_x i)))
  \<longleftrightarrow>
  (card B < max_deg \<and> i \<in> B \<and>
                    \<phi>_i \<noteq> poly r_x i \<and> 
                    valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B \<and>
                    VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) C i \<phi>_i w_i \<and>
                    VerifyEvalBatch (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) C B r_x
                     w_B)"
  using verifys_impl_t_BSDH_break by fast


theorem bind_game_eq_t_BSDH_red:
  shows "bind_game \<A> = t_BSDH.game (bind_reduction \<A>)"
proof - 
  note [simp] = Let_def split_def

  text \<open>abbreviations for the mod_ring version of sample uniform nat 
  and the public key\<close>
  let ?mr = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?mr \<alpha>)^t)) [0..<max_deg+1])"
  have "t_BSDH.game (bind_reduction \<A>) =  TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (c, g) \<leftarrow> (bind_reduction \<A>) (?PK \<alpha>);
    _::unit \<leftarrow> assert_spmf((e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+c)) = g);
    return_spmf True 
  } ELSE return_spmf False"
    unfolding t_BSDH.game_alt_def by (metis o_def)
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B);
    let p' = g_pow_PK_Prod (?PK \<alpha>) (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
    let r' = g_pow_PK_Prod (?PK \<alpha>) ((r_x - [:poly r_x i:]) div [:-i,1:]);
    _::unit \<leftarrow>  assert_spmf ((e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+(-i))) = e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
    return_spmf True  
  } ELSE return_spmf False"
    by force
  text \<open>fold the two asserts together so we can reason about their joined content.\<close>
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B);
    let p' = g_pow_PK_Prod (?PK \<alpha>) (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
    let r' = g_pow_PK_Prod (?PK \<alpha>) ((r_x - [:poly r_x i:]) div [:-i,1:]);
    _::unit \<leftarrow>  assert_spmf ((e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+(-i))) = e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
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
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B
                              \<and> (e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+(-i))) 
                                = e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
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
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B
                              \<and> (e \<^bold>g \<^bold>g) ^\<^bsub>G\<^sub>T\<^esub> (1/((?mr \<alpha>)+(-i))) 
                                = e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))); 
    return_spmf True  
  } ELSE return_spmf False"
   unfolding split_def Let_def
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                              \<and> VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B); 
    return_spmf True  
  } ELSE return_spmf False"
    unfolding Let_def using literal_helping by algebra 
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
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
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B);
    _ :: unit \<leftarrow> assert_spmf (VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B); 
    return_spmf True  
     } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False" 
    using assert_anding by algebra
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (card B < max_deg \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B);
    _ :: unit \<leftarrow> assert_spmf (VerifyEval (?PK \<alpha>) C i \<phi>_i w_i \<and> VerifyEvalBatch (?PK \<alpha>) C B r_x w_B); 
    return_spmf True
  } ELSE return_spmf False" 
  unfolding split_def Let_def
  by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots>= bind_game \<A>"
    using bind_game_alt_def unfolding key_gen_def Setup_def by simp
  finally show ?thesis ..
qed

theorem batchOpening_binding: "bind_advantage \<A> = t_BSDH.advantage (bind_reduction \<A>)"
  unfolding bind_advantage_def t_BSDH.advantage_def
  using bind_game_eq_t_BSDH_red by presburger

end 

end
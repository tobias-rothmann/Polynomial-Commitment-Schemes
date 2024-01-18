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
                    
subsection \<open>Game definition\<close>

type_synonym ('a', 'e')  adversary = 
  "'a' pk \<Rightarrow> 
 ('a' commit \<times> 'e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness \<times> 'e' eval_position set 
  \<times> 'a' eval_witness \<times> 'e' polynomial) spmf"

definition bind_game :: "('a, 'e) adversary \<Rightarrow> bool spmf"
  where "bind_game \<A> = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i); 
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEvalBatch PK C B r_x w_B;
  return_spmf (b \<and> b')} ELSE return_spmf False"

definition bind_advantage :: "('a, 'e) adversary \<Rightarrow> real"
  where "bind_advantage \<A> \<equiv> spmf (bind_game \<A>) True"
                                                        
subsection \<open>t-SDH game\<close>

sublocale t_BSDH: t_BSDH G\<^sub>p G\<^sub>T max_deg "of_int_mod_ring \<circ> int" pow_mod_ring_G\<^sub>p pow_mod_ring_G\<^sub>T e
  unfolding t_BSDH_def 
  using G\<^sub>T.cyclic_group_axioms G\<^sub>p.cyclic_group_axioms by presburger

subsection \<open>Defining a reduction game to t-SDH\<close>

fun bind_reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e,'c) t_BSDH.adversary"                     
where
  "bind_reduction \<A> PK = do {
   (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
  let p' = g_pow_PK_Prod PK (prod (\<lambda>i. [:-i,1:]) B div [:-i,1:]);
  let r' = g_pow_PK_Prod PK ((r_x - [:poly r_x i:]) div [:-i,1:]);
  return_spmf (-i::'e mod_ring, e p' w_B \<otimes>\<^bsub>G\<^sub>T\<^esub> e (r' \<div>\<^bsub>G\<^sub>p\<^esub> w_i) \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (1/(\<phi>_i - poly r_x i))) }"

end

end
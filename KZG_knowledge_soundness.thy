theory KZG_knowledge_soundness

imports KZG_eval_bind

begin

text \<open>We show knowledge soundness oriented at the definition in the PLONK paper (see section 3.1
in the PLONK paper: https://eprint.iacr.org/2019/953.pdf). However, we show the property only for 
a commitment to one polynomial to stay consistent with the other proofs in this work. Due to the 
layout of the property though, this proof should be easily extendable to multiple polynomials 
and thus serve as a strong basis for a proof for the full PLONK version.\<close>

locale knowledge_sound__game_def = bind_game_proof
begin

subsection \<open>Game definition\<close>

type_synonym 'e' calc_vector = "'e' mod_ring list"

type_synonym ('a', 'e')  adversary_1 = 
  "'a' pk \<Rightarrow> 
 ('a' commit \<times> 'e' calc_vector) spmf"

type_synonym ('a', 'e')  adversary_2 = 
  "'a' pk \<Rightarrow> 'a' commit \<Rightarrow> 'e' calc_vector \<Rightarrow> 
   ('e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness) spmf"

type_synonym ('a', 'e') extractor = 
  "'a' commit \<Rightarrow> 'e' calc_vector \<Rightarrow> 
    'e' mod_ring poly"

definition knowledge_soundness_game :: "('a, 'e) extractor \<Rightarrow> ('a, 'e) adversary_1 \<Rightarrow> ('a, 'e) adversary_2 
  \<Rightarrow> bool spmf"
  where "knowledge_soundness_game E \<A> \<A>' = TRY do {
  PK \<leftarrow> key_gen;
  (C,calc_vec) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
  return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i)} ELSE return_spmf False"

(*definition bind_game :: "('a, 'e) adversary \<Rightarrow> bool spmf"
  where "bind_game \<A> = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i); 
    \<comment>\<open>maybe \<or> for w_i or no w_i at all?\<close>
  let b = verify PK C i \<phi>_i w_i;
  let b' = verify PK C i \<phi>'_i w'_i;
  return_spmf (b \<and> b')} ELSE return_spmf False"*)

fun knowledge_soundness_reduction
  :: "('a, 'e) extractor \<Rightarrow> ('a, 'e) adversary_1 \<Rightarrow> ('a, 'e) adversary_2 \<Rightarrow> ('a, 'e) adversary"                     
where
  "knowledge_soundness_reduction E \<A> \<A>' PK = do {
  (C,calc_vec) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
  let \<phi>'_i = poly \<phi> i;
  let w'_i = createWitness PK (to_qr \<phi>) i;
  return_spmf (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i)}"

fun extractor :: "('a, 'e) extractor" where 
  "extractor C calc_vec = Poly calc_vec"

theorem "knowledge_soundness_game E \<A> \<A>' = bind_game (knowledge_soundness_reduction E \<A> \<A>')"
  sorry


end

end
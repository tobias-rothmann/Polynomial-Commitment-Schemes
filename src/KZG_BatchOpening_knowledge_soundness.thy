theory KZG_BatchOpening_knowledge_soundness

imports KZG_BatchOpening_binding
begin

(*TODO change discrp*)
text \<open>We show knowledge soundness oriented at the definition in the PLONK paper (see section 3.1
in the PLONK paper: https://eprint.iacr.org/2019/953.pdf). However, we show the property only for 
a commitment to one polynomial to stay consistent with the other proofs in this work. Due to the 
layout of the property though, this proof should be easily extendable to multiple polynomials 
and thus serve as a strong basis for a proof for the full PLONK version.\<close>

locale knowledge_sound_game_def = bind_game_proof
begin

type_synonym 'e' calc_vector = "'e' mod_ring list"

type_synonym ('a', 'e')  adversary_1 = 
  "'a' pk \<Rightarrow> 
 ('a' commit \<times> 'e' calc_vector) spmf"

type_synonym ('a', 'e')  adversary_2 = 
  "'a' pk \<Rightarrow> 'a' commit \<Rightarrow> 'e' calc_vector \<Rightarrow> 
   ('e' eval_position \<times> 'e' eval_position set\<times> 'e' polynomial \<times> 'a' eval_witness) spmf"

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
  (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
  _ ::unit \<leftarrow> assert_spmf (i \<in> B  \<and> valid_batch_msg r_x w_B B);
  return_spmf (VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i)} ELSE return_spmf False"

definition knowledge_soundness_game_advantage :: "('a, 'e) extractor \<Rightarrow> ('a, 'e) adversary_1 \<Rightarrow> ('a, 'e) adversary_2 
   \<Rightarrow> real"
  where "knowledge_soundness_game_advantage E \<A> \<A>' \<equiv> spmf (knowledge_soundness_game E \<A> \<A>') True"

subsubsection \<open>reduction definition\<close>

definition knowledge_soundness_reduction
  :: "('a, 'e) extractor \<Rightarrow> ('a, 'e) adversary_1 \<Rightarrow> ('a, 'e) adversary_2 \<Rightarrow> ('a, 'e) adversary"                     
where
  "knowledge_soundness_reduction E \<A> \<A>' PK = do {
  (C,calc_vec) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
  let \<phi>_i = poly \<phi> i;
  let w_i = createWitness PK \<phi> i;
  return_spmf (C, i, \<phi>_i, w_i, B, w_B, r_x)}"

subsubsection \<open>Extractor definition\<close>
fun E :: "('a, 'e) extractor" where 
  "E C calc_vec = Poly calc_vec"

subsubsection \<open>alternative definitions for easier proving + their equivalence proofs\<close>

lemma pull_down_assert_spmf_with_return:
"do {
    z::'z \<leftarrow> Z:: 'z spmf;
    x::'x \<leftarrow> (X:: 'z \<Rightarrow> 'x spmf) z;
    _ :: unit \<leftarrow> assert_spmf((f::'z \<Rightarrow> 'x \<Rightarrow> bool) z x);
    y::'y \<leftarrow> (Y:: 'z \<Rightarrow> 'x \<Rightarrow> 'y spmf) z x;
    _ :: unit \<leftarrow> assert_spmf ((A::'y \<Rightarrow> bool) y);
    return_spmf ((g::'z \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) z x y) }
  = do {
    z::'z \<leftarrow> Z:: 'z spmf;
    x::'x \<leftarrow> (X:: 'z \<Rightarrow> 'x spmf) z;
    y::'y \<leftarrow> (Y:: 'z \<Rightarrow> 'x \<Rightarrow> 'y spmf) z x;
    _ :: unit \<leftarrow> assert_spmf((f::'z \<Rightarrow> 'x \<Rightarrow> bool) z x);
    _ :: unit \<leftarrow> assert_spmf ((A::'y \<Rightarrow> bool) y);
    return_spmf ((g::'z \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) z x y) }"
proof -
  have "\<forall>z x. do {
    _ :: unit \<leftarrow> assert_spmf((f::'z \<Rightarrow> 'x \<Rightarrow> bool) z x);
    y::'y \<leftarrow> (Y:: 'z \<Rightarrow> 'x \<Rightarrow> 'y spmf) z x;
    _ :: unit \<leftarrow> assert_spmf ((A::'y \<Rightarrow> bool) y);
    return_spmf ((g::'z \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) z x y) }
  = do {
    y::'y \<leftarrow> (Y:: 'z \<Rightarrow> 'x \<Rightarrow> 'y spmf) z x;
    _ :: unit \<leftarrow> assert_spmf((f::'z \<Rightarrow> 'x \<Rightarrow> bool) z x);
    _ :: unit \<leftarrow> assert_spmf ((A::'y \<Rightarrow> bool) y);
    return_spmf ((g::'z \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) z x y) }"
    using bind_commute_spmf by fast
  then show ?thesis by presburger
qed

lemma pull_down_assert_spmf_with_assert:
"do {
    z::'z \<leftarrow> Z:: 'z spmf;
    x::'x \<leftarrow> (X:: 'z \<Rightarrow> 'x spmf) z;
    _ :: unit \<leftarrow> assert_spmf((f::'z \<Rightarrow> 'x \<Rightarrow> bool) z x);
    y::'y \<leftarrow> (Y:: 'z \<Rightarrow> 'x \<Rightarrow> 'y spmf) z x;
    _ :: unit \<leftarrow> assert_spmf((g::'z \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) z x y);
    return_spmf True }
  = do {
    z::'z \<leftarrow> Z:: 'z spmf;
    x::'x \<leftarrow> (X:: 'z \<Rightarrow> 'x spmf) z;
    y::'y \<leftarrow> (Y:: 'z \<Rightarrow> 'x \<Rightarrow> 'y spmf) z x;
    _ :: unit \<leftarrow> assert_spmf((f::'z \<Rightarrow> 'x \<Rightarrow> bool) z x);
    _ :: unit \<leftarrow> assert_spmf((g::'z \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) z x y);
    return_spmf True }"
proof -
  have "\<forall>z x. do {
    _ :: unit \<leftarrow> assert_spmf((f::'z \<Rightarrow> 'x \<Rightarrow> bool) z x);
    y::'y \<leftarrow> (Y:: 'z \<Rightarrow> 'x \<Rightarrow> 'y spmf) z x;
    _ :: unit \<leftarrow> assert_spmf((g::'z \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) z x y);
    return_spmf True }
  = do {
    y::'y \<leftarrow> (Y:: 'z \<Rightarrow> 'x \<Rightarrow> 'y spmf) z x;
    _ :: unit \<leftarrow> assert_spmf((f::'z \<Rightarrow> 'x \<Rightarrow> bool) z x);
    _ :: unit \<leftarrow> assert_spmf((g::'z \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> bool) z x y);
    return_spmf True}"
    using bind_commute_spmf by fast
  then show ?thesis by presburger
qed

lemma key_gen_alt_def: "key_gen = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x) in
    return_spmf (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])
  }"
  unfolding key_gen_def Setup_def Let_def split_def by simp

lemma knowledge_soundness_game_alt_def: 
  "knowledge_soundness_game E \<A> \<A>' = 
   TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> i \<in> B  
            \<and> valid_batch_msg r_x w_B B
            \<and> VerifyEvalBatch PK C B r_x w_B 
            \<and> poly r_x i \<noteq> poly \<phi> i);
   return_spmf True
  } ELSE return_spmf False"
proof -
  note [simp] = Let_def split_def
  have "do {
  PK \<leftarrow> key_gen;
  (C,calc_vec) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (i \<in> B  \<and> valid_batch_msg r_x w_B B);
  return_spmf (VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly (E C calc_vec) i)} 
  = 
  do {
  PK \<leftarrow> key_gen;
  (C,calc_vec) \<leftarrow> \<A> PK;
  (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  _ :: unit \<leftarrow> assert_spmf (i \<in> B  \<and> valid_batch_msg r_x w_B B);  
  return_spmf (VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly (E C calc_vec) i)}"
    using pull_down_assert_spmf_with_return[of key_gen \<A>] by fastforce
  then have "knowledge_soundness_game E \<A> \<A>' = 
  TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    _ :: unit \<leftarrow> assert_spmf (i \<in> B  \<and> valid_batch_msg r_x w_B B);
    return_spmf (VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly (E C calc_vec) i)
  } ELSE return_spmf False"
    unfolding knowledge_soundness_game_def by algebra
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B  \<and> valid_batch_msg r_x w_B B);  
    TRY return_spmf (VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i)  ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
   unfolding split_def Let_def
   by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B  \<and> valid_batch_msg r_x w_B B);  
    _ :: unit \<leftarrow> assert_spmf (VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
   by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B  \<and> valid_batch_msg r_x w_B B
            \<and> VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    using assert_anding by presburger
   also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);
    _ :: unit \<leftarrow> assert_spmf (i \<in> B  \<and> valid_batch_msg r_x w_B B
            \<and> VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
   also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> i \<in> B  \<and> valid_batch_msg r_x w_B B
            \<and> VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
     using assert_anding by presburger
   text \<open>next step, add assert PK construction\<close>
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> i \<in> B  \<and> valid_batch_msg r_x w_B B
            \<and> VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i);
    return_spmf True
  } ELSE return_spmf False"
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    PK \<leftarrow> return_spmf (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]);
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> i \<in> B  \<and> valid_batch_msg r_x w_B B
            \<and> VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i);
    return_spmf True
  } ELSE return_spmf False"
     using key_gen_alt_def
     by (smt (verit, ccfv_SIG) bind_spmf_assoc bind_spmf_cong)
    also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> i \<in> B  \<and> valid_batch_msg r_x w_B B
            \<and> VerifyEvalBatch PK C B r_x w_B \<and> poly r_x i \<noteq> poly \<phi> i);
    return_spmf True
  } ELSE return_spmf False"
      using return_bind_spmf by meson
  finally show ?thesis .
qed

lemma bind_game_knowledge_soundness_reduction_alt_def: 
  "bind_game (knowledge_soundness_reduction E \<A> \<A>') = 
  TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> i \<in> B 
            \<and> poly \<phi> i \<noteq>  poly r_x i
            \<and> valid_msg (poly \<phi> i) (createWitness PK \<phi> i)
            \<and> valid_batch_msg r_x w_B B
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK \<phi> i) 
            \<and> VerifyEvalBatch PK C B r_x w_B);
       return_spmf True
    } ELSE return_spmf False"
proof -
  have "bind_game (knowledge_soundness_reduction E \<A> \<A>') = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, B, w_B, r_x) \<leftarrow> (knowledge_soundness_reduction E \<A> \<A>') PK;
  _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEvalBatch PK C B r_x w_B;
  _::unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True} ELSE return_spmf False" 
    by (fact bind_game_alt_def)
  also have "\<dots> = TRY do {
  PK \<leftarrow> key_gen;
  (C,calc_vec) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
  let \<phi>_i = poly \<phi> i;
  let w_i = createWitness PK \<phi> i;
  _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEvalBatch PK C B r_x w_B;
  _::unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True} ELSE return_spmf False"
  unfolding knowledge_soundness_reduction_def by (simp add: split_def Let_def)
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do{
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B); 
    let b = VerifyEval PK C i \<phi>_i w_i;
    let b' = VerifyEvalBatch PK C B r_x w_B;
    _::unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True
    } ELSE return_spmf False 
    } ELSE return_spmf False 
    } ELSE return_spmf False 
    } ELSE return_spmf False 
  } ELSE return_spmf False"
   unfolding split_def Let_def 
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do{
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
    return_spmf True
    } ELSE return_spmf False 
    } ELSE return_spmf False 
    } ELSE return_spmf False 
    } ELSE return_spmf False 
  } ELSE return_spmf False"
    using assert_anding by presburger
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
    return_spmf True
  } ELSE return_spmf False"
   unfolding split_def Let_def 
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
    return_spmf True
  } ELSE return_spmf False"
  proof -
    have "do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
    return_spmf True
    } = do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
    return_spmf True
    }"
      using pull_down_assert_spmf_with_assert[of key_gen \<A>] 
      by (simp add: Let_def split_def)
    then show ?thesis by argo
  qed
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False 
    } ELSE return_spmf False
  } ELSE return_spmf False"
  unfolding split_def Let_def 
  by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
    let \<phi> = E C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
                            \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False 
    } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding Let_def
    using assert_anding by presburger
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi> = E C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
                            \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
    return_spmf True
  } ELSE return_spmf False"
   unfolding split_def Let_def 
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
 text \<open>make PK definition extractable\<close>
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    PK \<leftarrow> return_spmf (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]);
    (C,calc_vec) \<leftarrow> \<A> PK;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi> = E C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
                            \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
       return_spmf True
    } ELSE return_spmf False"
    using key_gen_alt_def
    by (smt (verit, ccfv_SIG) bind_spmf_assoc bind_spmf_cong)
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec) \<leftarrow> \<A> PK;
    (i, B, r_x, w_B) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi> = E C calc_vec;
    let \<phi>_i = poly \<phi> i;
    let w_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
                            \<and> i \<in> B \<and> \<phi>_i \<noteq> poly r_x i 
                            \<and> valid_msg \<phi>_i w_i \<and> valid_batch_msg r_x w_B B
                            \<and> VerifyEval PK C i \<phi>_i w_i \<and> VerifyEvalBatch PK C B r_x w_B);
       return_spmf True
    } ELSE return_spmf False"
    using return_bind_spmf by meson
  finally show ?thesis unfolding Let_def .
qed

lemma asserts_are_equal: 
  "length (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) = length calc_vec \<and>
                      C =
                      fold
                       (\<lambda>(i::nat) acc::'a.
                           acc \<otimes>\<^bsub>G\<^sub>p\<^esub> map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)] ! i ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i)
                       [0::nat..<length (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)])] \<one> \<and>
                      i \<in> B \<and>
                      valid_batch_msg r_x w_B B \<and>
                      VerifyEvalBatch (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) C B r_x w_B \<and>
                      poly r_x i \<noteq> poly (E C calc_vec) i 
      \<longleftrightarrow> 
  length (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) = length calc_vec \<and>
                      C =
                      fold
                       (\<lambda>(i::nat) acc::'a.
                           acc \<otimes>\<^bsub>G\<^sub>p\<^esub> map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)] ! i ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i)
                       [0::nat..<length (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)])] \<one> \<and>
                      i \<in> B \<and>
                      poly (E C calc_vec) i \<noteq> poly r_x i \<and>
                      valid_msg (poly (E C calc_vec) i)
                       (createWitness (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) (E C calc_vec) i) \<and>
                      valid_batch_msg r_x w_B B \<and>
                      VerifyEval (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) C i
                       (poly (E C calc_vec) i)
                       (createWitness (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) (E C calc_vec) i) \<and>
                      VerifyEvalBatch (map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) C B r_x w_B"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  let ?PK = "(map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])"
  let ?\<phi> = "Poly calc_vec"
  
  assume asm: ?lhs
  show ?rhs
  proof (intro conjI)
    show "length (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) = length calc_vec"
      using asm by blast
    show C: "C =
    fold (\<lambda>(i::nat) acc::'a. acc \<otimes> map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)] ! i ^ calc_vec ! i)
     [0::nat..<length (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)])] \<one>"
      using asm by fast
    show " i \<in> B"
      using asm by blast
    show "poly (E C calc_vec) i \<noteq> poly r_x i"
      using asm by argo
    (*TODO remove this duplicate prove (with normal knowledge soundness)*)
    show "valid_msg (poly (E C calc_vec) i) 
     (createWitness (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) (E C calc_vec) i)"
      proof -
      have "g_pow_PK_Prod ?PK (\<psi>_of (Poly calc_vec) i) 
      = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (\<psi>_of (Poly calc_vec) i) \<alpha>)"
      proof (rule g_pow_PK_Prod_correct)
        show "degree (\<psi>_of (Poly calc_vec) i) \<le> max_deg"
        proof (rule  le_trans[OF degree_q_le_\<phi>])
          have "length calc_vec = max_deg +1"
            using asm by force
          moreover have "length (coeffs (Poly calc_vec)) \<le> length calc_vec"
            by (simp add: length_strip_while_le)
          ultimately show "degree (Poly calc_vec) \<le> max_deg"
            using degree_eq_length_coeffs[of "Poly calc_vec"] by linarith
        qed
      qed
      then show ?thesis 
        unfolding valid_msg_def createWitness.simps Let_def
        by simp
    qed
    show "valid_batch_msg r_x w_B B"
      using asm by fast
    (*TODO remove this duplicate prove (with normal knowledge soundness)*)
    show "VerifyEval (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) C i (poly (E C calc_vec) i)
     (createWitness (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) (E C calc_vec) i)"
     proof -
      have length_calc_vec: "length calc_vec = max_deg +1"
            using asm by force
      moreover have "length (coeffs (Poly calc_vec)) \<le> length calc_vec"
        by (simp add: length_strip_while_le)
      ultimately have deg_poly_calc_vec_le_max_deg: "degree (Poly calc_vec) \<le> max_deg"
        using degree_eq_length_coeffs[of "Poly calc_vec"] by linarith
      
      have 1: "(g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1])
        (\<psi>_of (Poly calc_vec) i))
        = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>_of (Poly calc_vec) i) \<alpha>)"
      proof(rule  g_pow_PK_Prod_correct)
        show "degree (\<psi>_of (Poly calc_vec) i) \<le> max_deg"
          by (rule le_trans[OF degree_q_le_\<phi>])(fact deg_poly_calc_vec_le_max_deg)
      qed

      have 2: "map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1] ! 1 = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha>"
        by (metis (no_types, lifting) One_nat_def add.commute d_pos diff_zero le_add_same_cancel1 le_zero_eq length_upt nth_map nth_upt plus_1_eq_Suc power_one_right zero_compare_simps(1))
      
      have 3: "C = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (Poly calc_vec) \<alpha>)"
      proof -
        have "(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (Poly calc_vec) \<alpha>) 
             = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (Poly calc_vec)"
          by (rule  g_pow_PK_Prod_correct[symmetric])(fact deg_poly_calc_vec_le_max_deg)
        also have g_pow_to_fold: "\<dots> = fold (\<lambda>i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^i)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff (Poly calc_vec) i)) [0..<Suc (degree (Poly calc_vec))] \<one>\<^bsub>G\<^sub>p\<^esub>"
          by(rule g_pow_PK_Prod_to_fold)(fact deg_poly_calc_vec_le_max_deg)
        also have "\<dots> 
        =fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^i)) ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<max_deg+1] \<one>\<^bsub>G\<^sub>p\<^esub>"
        proof -
          have "fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) [0..<max_deg + 1] \<one>
              = fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) 
                  ([0..<Suc (degree (Poly calc_vec))] @ [Suc (degree (Poly calc_vec))..<max_deg + 1]) 
                  \<one>" 
          proof -
            have "Suc (degree (Poly calc_vec)) \<le> max_deg +1"
              by (simp add: deg_poly_calc_vec_le_max_deg)
            then show ?thesis
              by (metis (no_types, lifting) nat_le_iff_add not_less not_less_eq_eq upt_add_eq_append zero_less_Suc)
          qed
          also have "\<dots> = fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) 
                            [Suc (degree (Poly calc_vec))..<max_deg + 1]
                            (fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) 
                             [0..<Suc (degree (Poly calc_vec))] \<one>)"
            by fastforce
          also have "\<dots> = fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff (Poly calc_vec) i) 
                            [0..<Suc (degree (Poly calc_vec))] 
                            \<one>"
          proof -
            have "fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) [0..<Suc (degree (Poly calc_vec))] \<one> 
                = fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff (Poly calc_vec) i) [0..<Suc (degree (Poly calc_vec))] \<one>" 
            proof (rule List.fold_cong) 
              show " \<And>x. x \<in> set [0..<Suc (degree (Poly calc_vec))] \<Longrightarrow>
                       (\<lambda>acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x) =
                       (\<lambda>acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff (Poly calc_vec) x)"
              proof 
                fix x::nat
                fix acc::'a
                assume asm: "x \<in> set [0..<Suc (degree (Poly calc_vec))]"
                then have " calc_vec ! x = poly.coeff (Poly calc_vec) x"
                  by (metis \<open>length calc_vec = max_deg + 1\<close> atLeastLessThan_iff coeff_Poly deg_poly_calc_vec_le_max_deg dual_order.trans less_Suc_eq_le nth_default_nth semiring_norm(174) set_upt)
                then show " acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x = acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff (Poly calc_vec) x "
                  by presburger
              qed
            qed simp+
            moreover have "\<forall>init \<in> carrier G\<^sub>p. 
                    fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) 
                      [Suc (degree (Poly calc_vec))..<max_deg + 1] 
                      init 
                    = init"
            proof 
              fix init ::'a
              assume init_in_carrier: "init \<in> carrier G\<^sub>p"
              have "fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) 
                      [Suc (degree (Poly calc_vec))..<max_deg + 1] 
                      init = fold (\<lambda>i acc. acc \<otimes> \<one>) 
                      [Suc (degree (Poly calc_vec))..<max_deg + 1] 
                      init"
              proof (rule List.fold_cong)
                show " \<And>x. x \<in> set [Suc (degree (Poly calc_vec))..<max_deg + 1] \<Longrightarrow>
                        (\<lambda>acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x) = (\<lambda>acc. acc \<otimes> \<one>)"
                proof 
                  fix x::nat
                  fix acc ::'a
                  assume asm: "x \<in> set [Suc (degree (Poly calc_vec))..<max_deg + 1]"
                  show "acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x = acc  \<otimes> \<one>"
                  proof -
                    have " calc_vec ! x = 0" using asm length_calc_vec
                      by (smt (verit) add.commute coeff_Poly_eq in_set_conv_nth le_degree length_upt less_diff_conv not_less_eq_eq nth_default_eq_dflt_iff nth_upt order.refl trans_le_add2)
                    then have "(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x = \<one>" by simp
                    then show ?thesis by argo 
                  qed
                qed
              qed simp+
              also have "\<dots> = init" 
              proof (induction max_deg)
                case 0
                then show ?case by fastforce
              next
                case (Suc max_deg)
                have "fold (\<lambda>i acc. acc \<otimes> \<one>) [Suc (degree (Poly calc_vec))..<Suc max_deg + 1] init
                = fold (\<lambda>i acc. acc \<otimes> \<one>) ([Suc (degree (Poly calc_vec))..<max_deg + 1] @ [Suc max_deg]) init"
                  by (simp add: init_in_carrier)
                also have "\<dots> = fold (\<lambda>i acc. acc \<otimes> \<one>) [Suc max_deg] (fold (\<lambda>i acc. acc \<otimes> \<one>) [Suc (degree (Poly calc_vec))..<max_deg + 1] init)"
                  by force
                also have "\<dots> = fold (\<lambda>i acc. acc \<otimes> \<one>) [Suc max_deg] init" using Suc.IH by argo
                also have "\<dots> = init \<otimes> \<one>" by force
                also have "\<dots> = init" by (simp add: init_in_carrier)
                finally show ?case .
              qed
              finally show "fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) 
                      [Suc (degree (Poly calc_vec))..<max_deg + 1] 
                      init 
                   = init" .
            qed
            ultimately show ?thesis
              by (metis (no_types, lifting) G\<^sub>p.generator_closed G\<^sub>p.int_pow_closed \<open>\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (Poly calc_vec) \<alpha> = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (Poly calc_vec)\<close> g_pow_to_fold)
          qed
          finally show ?thesis by presburger
        qed
        also have "\<dots> 
        =fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<max_deg+1] \<one>\<^bsub>G\<^sub>p\<^esub>"
        proof(rule List.fold_cong)
          show "\<one> = \<one>" by simp
          show "[0..<max_deg + 1] = [0..<max_deg + 1]" by simp
          show "\<And>x. x \<in> set [0..<max_deg + 1] \<Longrightarrow>
           (\<lambda>acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x) =
           (\<lambda>acc. acc \<otimes> map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1] ! x ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x)"
          proof 
            fix x::nat 
            fix acc :: 'a
            assume asm: "x \<in> set [0..<max_deg + 1]"
            show " acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x 
                 = acc \<otimes> map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1] ! x ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! x"
              using PK_i[symmetric] asm
              by (metis Suc_eq_plus1 atLeastLessThan_iff less_Suc_eq_le set_upt)
          qed
        qed
        also have "\<dots> = C" 
          using asm by fastforce
        finally show ?thesis ..
      qed
      show ?thesis
      unfolding VerifyEval_def createWitness.simps Let_def g_pow_PK_Prod_correct 3 2 1 E.simps
      using eq_on_e[of "(Poly calc_vec)" i \<alpha>] by blast
  qed
    show "VerifyEvalBatch (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) C B r_x w_B"
      using asm by linarith
  qed 
qed argo

theorem knowledge_soundness_game_eq_bind_game_knowledge_soundness_reduction: 
  "knowledge_soundness_game E \<A> \<A>' = bind_game (knowledge_soundness_reduction E \<A> \<A>')"
  unfolding knowledge_soundness_game_alt_def 
            bind_game_knowledge_soundness_reduction_alt_def
            Let_def
  using asserts_are_equal by simp

theorem evaluation_knowledge_soundness: 
  "knowledge_soundness_game_advantage E \<A> \<A>' 
  = t_BSDH.advantage (bind_reduction (knowledge_soundness_reduction E \<A> \<A>'))"
  using knowledge_soundness_game_eq_bind_game_knowledge_soundness_reduction 
        batchOpening_binding
  unfolding bind_advantage_def knowledge_soundness_game_advantage_def
  by algebra
  

end
theory KZG_BatchOpening_knowledge_soundness

imports KZG_BatchOpening_binding
begin

(*TODOD change discrp*)
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

declare [[show_types]]
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
    show "valid_msg (poly (E C calc_vec) i)
     (createWitness (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) (E C calc_vec) i)"
      unfolding valid_msg_def createWitness.simps Let_def  sorry
    show "valid_batch_msg r_x w_B B"
      using asm by fast
    show "VerifyEval (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) C i (poly (E C calc_vec) i)
     (createWitness (map (\<lambda>t::nat. \<^bold>g ^ \<alpha> ^ t) [0::nat..<max_deg + (1::nat)]) (E C calc_vec) i)"
      unfolding VerifyEval_def createWitness.simps Let_def C sorry
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
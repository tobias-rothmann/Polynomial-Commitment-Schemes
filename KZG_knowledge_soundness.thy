theory KZG_knowledge_soundness

imports KZG_eval_bind

begin

text \<open>We show knowledge soundness oriented at the definition in the PLONK paper (see section 3.1
in the PLONK paper: https://eprint.iacr.org/2019/953.pdf). However, we show the property only for 
a commitment to one polynomial to stay consistent with the other proofs in this work. Due to the 
layout of the property though, this proof should be easily extendable to multiple polynomials 
and thus serve as a strong basis for a proof for the full PLONK version.\<close>

locale knowledge_sound_game_def = bind_game_proof
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

(* TODO add valid_msg check for the adversaries output of the witness and the polynomial*)
definition knowledge_soundness_game :: "('a, 'e) extractor \<Rightarrow> ('a, 'e) adversary_1 \<Rightarrow> ('a, 'e) adversary_2 
  \<Rightarrow> bool spmf"
  where "knowledge_soundness_game E \<A> \<A>' = TRY do {
  PK \<leftarrow> key_gen;
  (C,calc_vec) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
  _ ::unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
  return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i)} ELSE return_spmf False"

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
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
  _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
  let \<phi>'_i = poly \<phi> i;
  let w'_i = createWitness PK (to_qr \<phi>) i;
  return_spmf (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i)}"

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
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> valid_msg \<phi>_i w_i 
            \<and> VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
   return_spmf True
  } ELSE return_spmf False"
proof -
  note [simp] = Let_def split_def
  have "do {
  PK \<leftarrow> key_gen;
  (C,calc_vec) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
  return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly (E C calc_vec) i)} 
  = 
  do {
  PK \<leftarrow> key_gen;
  (C,calc_vec) \<leftarrow> \<A> PK;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);  
  return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly (E C calc_vec) i)}"
    using pull_down_assert_spmf_with_return[of key_gen \<A>] by fastforce
  then have "knowledge_soundness_game E \<A> \<A>' = 
  TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i)
  } ELSE return_spmf False"
    unfolding knowledge_soundness_game_def by algebra
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);  
    TRY return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i)  ELSE return_spmf False
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
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);  
    _ :: unit \<leftarrow> assert_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
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
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i 
            \<and> VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
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
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i 
            \<and> VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
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
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> valid_msg \<phi>_i w_i 
            \<and> VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
     using assert_anding by presburger
   text \<open>next step, add assert PK construction\<close>
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    PK \<leftarrow> return_spmf (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]);
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> valid_msg \<phi>_i w_i 
            \<and> VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
     using key_gen_alt_def
     by (smt (verit, ccfv_SIG) bind_spmf_assoc bind_spmf_cong)
    also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
     _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> valid_msg \<phi>_i w_i 
            \<and> VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
      using return_bind_spmf by meson
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> valid_msg \<phi>_i w_i 
            \<and> VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
   return_spmf True
  } ELSE return_spmf False" 
   unfolding split_def Let_def
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
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
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i) 
            \<and> w_i \<noteq> (createWitness PK (to_qr \<phi>) i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK (to_qr \<phi>) i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK (to_qr \<phi>) i));
       return_spmf True
    } ELSE return_spmf False"
proof -
  have "bind_game (knowledge_soundness_reduction E \<A> \<A>') = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> (knowledge_soundness_reduction E \<A> \<A>') PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEval PK C i \<phi>'_i w'_i;
  _ :: unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True } ELSE return_spmf False" 
    by (fact bind_game_alt_def)
  also have "\<dots> = TRY do {
  PK \<leftarrow> key_gen;
  (C,calc_vec) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
  _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
  let \<phi>'_i = poly \<phi> i;
  let w'_i = createWitness PK (to_qr \<phi>) i;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEval PK C i \<phi>'_i w'_i;
  _ :: unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True } ELSE return_spmf False"
  unfolding knowledge_soundness_reduction_def by (simp add: split_def Let_def)
  also have "\<dots> =  TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK (to_qr \<phi>) i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg \<phi>'_i w'_i);
    _ :: unit \<leftarrow> assert_spmf (VerifyEval PK C i \<phi>_i w_i \<and> VerifyEval PK C i \<phi>'_i w'_i);
    return_spmf True 
    } ELSE return_spmf False
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
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK (to_qr \<phi>) i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg \<phi>'_i w'_i 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i \<phi>'_i w'_i);
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
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK (to_qr \<phi>) i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg \<phi>'_i w'_i 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i \<phi>'_i w'_i);
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
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK (to_qr \<phi>) i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg \<phi>'_i w'_i 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i \<phi>'_i w'_i);
    return_spmf True 
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False"
  proof -
    have "\<forall>\<phi>_i w_i \<phi>'_i w'_i PK C i.  valid_msg \<phi>_i w_i 
        \<and> \<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
        \<and> valid_msg \<phi>_i w_i 
        \<and> valid_msg \<phi>'_i w'_i 
        \<and> VerifyEval PK C i \<phi>_i w_i 
        \<and> VerifyEval PK C i \<phi>'_i w'_i 
      \<longleftrightarrow>
        \<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
        \<and> valid_msg \<phi>_i w_i 
        \<and> valid_msg \<phi>'_i w'_i 
        \<and> VerifyEval PK C i \<phi>_i w_i 
        \<and> VerifyEval PK C i \<phi>'_i w'_i "
      by meson
    then show ?thesis using assert_anding by algebra
  qed
  also have "\<dots> =  TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> w_i \<noteq> (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i));
    return_spmf True
    } ELSE return_spmf False"
    unfolding split_def Let_def 
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> =  TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> w_i \<noteq> (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i));
    return_spmf True
    } ELSE return_spmf False"
  proof -
    have "do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> w_i \<noteq> (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i));
    return_spmf True
    } = do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> w_i \<noteq> (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i));
    return_spmf True
    }"
      using pull_down_assert_spmf_with_assert[of key_gen \<A>] 
      by (simp add: Let_def split_def)
    then show ?thesis by argo
  qed
  also have "\<dots> =  TRY do {
    PK \<leftarrow> key_gen;
    TRY do {
    (C,calc_vec) \<leftarrow> \<A> PK;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> w_i \<noteq> (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i));
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
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly (E C calc_vec) i) 
            \<and> w_i \<noteq> (createWitness PK (to_qr (E C calc_vec)) i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (to_qr (E C calc_vec)) i));
       return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False"
    using assert_anding by presburger
  also have "\<dots> = TRY do {
    PK \<leftarrow> key_gen;
    (C,calc_vec) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i) 
            \<and> w_i \<noteq> (createWitness PK (to_qr \<phi>) i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK (to_qr \<phi>) i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK (to_qr \<phi>) i));
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
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i) 
            \<and> w_i \<noteq> (createWitness PK (to_qr \<phi>) i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK (to_qr \<phi>) i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK (to_qr \<phi>) i));
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
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i) 
            \<and> w_i \<noteq> (createWitness PK (to_qr \<phi>) i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK (to_qr \<phi>) i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK (to_qr \<phi>) i));
       return_spmf True
    } ELSE return_spmf False"
    using return_bind_spmf by meson
  finally show ?thesis .
qed

subsection \<open>Reduction proof\<close>

text \<open>show the equivalence of the content of the assert statements in the alt games i.e. 
assert content of knowledge_soundness_game_alt_def
is equivalent to the 
assert content of bind_game_knowledge_soundness_reduction_alt_def\<close>
lemma asserts_are_equal: 
      "length (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> valid_msg \<phi>_i w_i 
            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly (Poly calc_vec) i
  \<longleftrightarrow>
       length (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly (Poly calc_vec) i) 
            \<and> w_i \<noteq> (createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (to_qr (Poly calc_vec)) i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly (Poly calc_vec) i) (createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (to_qr (Poly calc_vec)) i) 
            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>_i w_i 
            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i (poly (Poly calc_vec) i) (createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (to_qr (Poly calc_vec)) i)"
proof 
  let ?PK = "(map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])"
  let ?\<phi> = "Poly calc_vec"
  assume asm: "length ?PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> ?PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length ?PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> valid_msg \<phi>_i w_i 
            \<and> VerifyEval ?PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly ?\<phi> i"
  show "length ?PK = length calc_vec \<and>
    C = fold (\<lambda>i acc. acc \<otimes> ?PK ! i ^\<^bsub>G\<^sub>p\<^esub> calc_vec ! i) [0..<length ?PK] \<one> \<and>
    \<phi>_i \<noteq> poly ?\<phi> i \<and>
    w_i \<noteq> createWitness ?PK (to_qr ?\<phi>) i \<and>
    valid_msg \<phi>_i w_i \<and>
    valid_msg (poly ?\<phi> i) (createWitness ?PK (to_qr ?\<phi>) i) \<and>
    VerifyEval ?PK C i \<phi>_i w_i \<and> VerifyEval ?PK C i (poly ?\<phi> i) (createWitness ?PK (to_qr ?\<phi>) i)"
  proof(intro conjI)
    show "length ?PK = length calc_vec"
      using asm by blast
    
    show "valid_msg (poly ?\<phi> i) (createWitness ?PK (to_qr ?\<phi>) i)" 
    proof -
      have "g_pow_PK_Prod ?PK (\<psi>_of (to_qr (Poly calc_vec)) i) 
      = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (\<psi>_of (to_qr (Poly calc_vec)) i) \<alpha>)"
      proof (rule g_pow_PK_Prod_correct)
        show "degree (\<psi>_of (to_qr (Poly calc_vec)) i) \<le> max_deg"
          by (metis \<psi>_of_and_\<psi>_of_poly degree_of_qr degree_q_le_\<phi> le_trans)
      qed
      then show ?thesis 
        unfolding valid_msg_def createWitness.simps Let_def
        by simp
    qed

    show "VerifyEval ?PK C i \<phi>_i w_i" 
      using asm by fast 
    
    show  "VerifyEval ?PK C i (poly ?\<phi> i) (createWitness ?PK (to_qr ?\<phi>) i)"
    proof -
      have 3: "C = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (of_qr (to_qr (Poly calc_vec))) \<alpha>)"
        sorry
      have 1: " 
        (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1])
        (\<psi>_of (to_qr (Poly calc_vec)) i))
        = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>_of (to_qr (Poly calc_vec)) i) \<alpha>)"
        sorry
      have 2: "map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1] ! 1 = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha>"
        sorry
      show ?thesis
      unfolding VerifyEval_def createWitness.simps Let_def g_pow_PK_Prod_correct 3 2 1
      using eq_on_e[of "to_qr (Poly calc_vec)" i \<alpha>] 
      
      sorry
      qed
    
     show "w_i \<noteq> createWitness ?PK (to_qr ?\<phi>) i"  
      sorry
  qed (simp add: asm)+
qed linarith

theorem knowledge_soundness_game_eq_bind_game_knowledge_soundness_reduction: 
  "knowledge_soundness_game E \<A> \<A>' = bind_game (knowledge_soundness_reduction E \<A> \<A>')"
  unfolding knowledge_soundness_game_alt_def 
            bind_game_knowledge_soundness_reduction_alt_def
            Let_def
  using asserts_are_equal by simp

theorem evaluation_knowledge_soundness: 
  "knowledge_soundness_game_advantage E \<A> \<A>' 
  = t_SDH_G\<^sub>p.advantage (bind_reduction (knowledge_soundness_reduction E \<A> \<A>'))"
  using knowledge_soundness_game_eq_bind_game_knowledge_soundness_reduction 
        evaluation_binding
  unfolding bind_advantage_def knowledge_soundness_game_advantage_def
  by algebra


end

end
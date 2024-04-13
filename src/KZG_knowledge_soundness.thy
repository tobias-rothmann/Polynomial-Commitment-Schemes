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

section \<open>Definitions for the knowledge soundness game\<close>

text \<open>We define the knowledge soundness game, the reduction to the evaluation binding game and thus 
transitively to the t-SDH assumption as well as any functions needed to construct them in this locale. 
This file contains another locale below which contains the proof.\<close>

subsection \<open>Game definition\<close>

text \<open>Note, the adversary for the knowledge soundness is in the Algebraic Group Model (AGM) and 
thus has to provide a vector we typed `calc_vector` for every group element it outputs. Furthermore, 
the group elements must be a linear combination of the group elements the adversary has seen so far.
the vector indicates the parameters of the linear combination. Intuitively, for e.g.
seen group elements (3,2,1), the adversary could create the value 5 with the vector (0,2,1) as 
5 = 3*0+2*2+1*1.\<close>

text \<open>Furthermore, the adversary for knowledge soundness is split up into two parts A=(A',A'') 
that share a state.\<close>

type_synonym '\<sigma>' state = '\<sigma>'

type_synonym 'e' calc_vector = "'e' mod_ring list"

type_synonym ('a', 'e', '\<sigma>')  adversary_1 = 
  "'a' pk \<Rightarrow> 
 ('a' commit \<times> 'e' calc_vector \<times> '\<sigma>' state) spmf"

type_synonym ('a', 'e', '\<sigma>')  adversary_2 = 
  "'\<sigma>' state \<Rightarrow> 'a' pk \<Rightarrow> 'a' commit \<Rightarrow> 'e' calc_vector \<Rightarrow> 
   ('e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness) spmf"

text \<open>The extractor is an algorithm that plays against the adversary. It is granted access to the 
adversaries messages and state (which we neglect in this case as we do not need it because the 
calculation vector is enough to create sensible values) and has to come up with a polynomial such 
that the adversary cannot create valid opening points that are not part of the polynomial.\<close>
type_synonym ('a', 'e') extractor = 
  "'a' commit \<Rightarrow> 'e' calc_vector \<Rightarrow> 
    'e' mod_ring poly"

text \<open>This is the formalized knowledge soundness game\<close>
definition knowledge_soundness_game :: "('a, 'e) extractor \<Rightarrow> ('a, 'e, '\<sigma>) adversary_1 \<Rightarrow> ('a, 'e, '\<sigma>) adversary_2 
  \<Rightarrow> bool spmf"
  where "knowledge_soundness_game E \<A> \<A>' = TRY do {
  PK \<leftarrow> KeyGen;
  (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
  _ ::unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
  return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i)} ELSE return_spmf False"

text \<open>The advantage of the adversary over the knowledge soundness game is the probabillity that it 
wins.\<close>
definition knowledge_soundness_game_advantage :: "('a, 'e) extractor \<Rightarrow> ('a, 'e, '\<sigma>) adversary_1 \<Rightarrow> ('a, 'e, '\<sigma>) adversary_2 
   \<Rightarrow> real"
  where "knowledge_soundness_game_advantage E \<A> \<A>' \<equiv> spmf (knowledge_soundness_game E \<A> \<A>') True"

subsection \<open>reduction definition\<close>

text \<open>The reduction function takes a adversary for the knowledge soundess game and returns an 
adversary for the evaluation binding game. Specifically, the reduction uses the knowledge soundness 
adversary to construct a winning strategy for the evaluation binding game (i.e. to win it every 
time).
Essentially, it uses the fact that the values supplied by the adversary already break the binding 
game.\<close>
definition knowledge_soundness_reduction
  :: "('a, 'e) extractor \<Rightarrow> ('a, 'e, '\<sigma>) adversary_1 \<Rightarrow> ('a, 'e, '\<sigma>) adversary_2 \<Rightarrow> ('a, 'e) adversary"                     
where
  "knowledge_soundness_reduction E \<A> \<A>' PK = do {
  (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK; 
  let \<phi> = E C calc_vec;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
  let \<phi>'_i = poly \<phi> i;
  let w'_i = createWitness PK \<phi> i;
  return_spmf (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i)}"

end

text \<open>This locale captures the proof for the definitions provided earlier\<close>
locale knowledge_sound_game_proof = knowledge_sound_game_def
begin

subsection \<open>helping definitions\<close>

text \<open>The knowledge soundness reduction adversary extended for asserts that 
are present in the evaluation binding game. We use this definition to show equivalence to 
the evaluation binding game. Later on we can then easily over-estimate the probability from 
this extended version to the normal reduction.\<close>
definition knowledge_soundness_reduction_ext
  :: "('a, 'e) extractor \<Rightarrow> ('a, 'e, '\<sigma>) adversary_1 \<Rightarrow> ('a, 'e, '\<sigma>) adversary_2 \<Rightarrow> ('a, 'e) adversary"                     
where
  "knowledge_soundness_reduction_ext E \<A> \<A>' PK = do {
  (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
  _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
  let \<phi>'_i = poly \<phi> i;
  let w'_i = createWitness PK \<phi> i;
  return_spmf (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i)}"

text \<open>Extractor definition\<close>
fun E :: "('a, 'e) extractor" where 
  "E C calc_vec = Poly calc_vec"

lemma key_gen_alt_def: "KeyGen = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x) in
    return_spmf (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])
  }"
  unfolding KeyGen_def Setup_def Let_def split_def by simp


subsection \<open>literal helping lemmas\<close>

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

subsection \<open>Reduction proof\<close>

text \<open>We structure the proof in 5 parts:

1. We restate the knowledge soundness game such that all assert statements are combined in one.

2. We restate the evaluation binding game with the extended reduction adversary such that all 
assert statements are combined in one.

3. We show that the accumulated assert statements in the last two steps are equivalent. Furthermore, 
we can conclude that the games are in fact equivalent.

4. We conclude from step 1 to 3 that the knowledge soundness game is the same game as the evalutaion 
binding game for the extended adversary

5. We overestimate the extended reduction with the normal reduction.

6. We conclude from step 4 that the probability of winning the knowledge soundness game is less 
than or equal to winning the evaluation binding game with the normal reduction adversary. 
Furthermore, we can conclude transitively through the evaluation binding game, that the probability 
of the adversary winning the knowledge soundness game is less than or equal to breaking the 
t-SDH assumption.
\<close>


text \<open>Proof Step 1:\<close>
lemma knowledge_soundness_game_alt_def: 
  "knowledge_soundness_game E \<A> \<A>' = 
   TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> valid_msg \<phi>_i w_i 
            \<and> VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i);
   return_spmf True
  } ELSE return_spmf False"
proof -
  note [simp] = Let_def split_def

  text \<open>we rearrange the asserts together in the knowledge soundness game so that we can combine 
  them later on.\<close>
  have "do {
  PK \<leftarrow> KeyGen;
  (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
  return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly (E C calc_vec) i)} 
  = 
  do {
  PK \<leftarrow> KeyGen;
  (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);  
  return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly (E C calc_vec) i)}"
    using pull_down_assert_spmf_with_return[of KeyGen \<A>] by fastforce
  then have "knowledge_soundness_game E \<A> \<A>' = 
  TRY do {
    PK \<leftarrow> KeyGen;
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    return_spmf (VerifyEval PK C i \<phi>_i w_i \<and> \<phi>_i \<noteq> poly \<phi> i)
  } ELSE return_spmf False"
    unfolding knowledge_soundness_game_def by algebra
  text \<open>Now we unfold the knowledge soundness game to merge multiple asserts together.\<close>
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
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
  text \<open>However, before merging we turn the return statement into another assert\<close>
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
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
  text \<open>Now we add the first two asserts together\<close>
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
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
  text \<open>we fold again to merge the remaining asserts\<close>
   also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
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
  text \<open>Now we can merge the remaining two asserts\<close>
   also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
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
   text \<open>next we want to make the construction of PK accessible in the assert. 
    For that we have to take two steps. Firstly we have unfold KeyGen to obtain access to the 
    computation of PK.\<close>
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    PK \<leftarrow> return_spmf (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]);
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
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
   text \<open>Secondly, we have to unwrap the definition of PK from the spmf into a constant one. 
   If PK is constant, we can drag its definition into the assert, instead of the variable 
   PK.\<close>
    also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
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
  text \<open>Lastly we fold the game together to obtain a clean game with all asserts accumulated.\<close>
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
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

text \<open>Proof Step 2:\<close>
lemma bind_game_knowledge_soundness_reduction_alt_def: 
  "bind_game (knowledge_soundness_reduction_ext E \<A> \<A>') = 
  TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i) 
            \<and> w_i \<noteq> (createWitness PK \<phi> i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK \<phi> i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK \<phi> i));
       return_spmf True
    } ELSE return_spmf False"
proof -
  text \<open>Firstly we extract the return value from the evaluation binding game into a assert statement.\<close>
  have "bind_game (knowledge_soundness_reduction_ext E \<A> \<A>') = TRY do {
  PK \<leftarrow> KeyGen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> (knowledge_soundness_reduction_ext E \<A> \<A>') PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEval PK C i \<phi>'_i w'_i;
  _ :: unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True } ELSE return_spmf False" 
    by (fact bind_game_alt_def)
  text \<open>Secondly, we inline the extended knowledge soundness adversary, so we can accumulate
  the asserts from the reduction and the game together.\<close>
  also have "\<dots> = TRY do {
  PK \<leftarrow> KeyGen;
  (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                          \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
  let \<phi> = E C calc_vec;
  (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
  _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
  let \<phi>'_i = poly \<phi> i;
  let w'_i = createWitness PK \<phi> i;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
  let b = VerifyEval PK C i \<phi>_i w_i;
  let b' = VerifyEval PK C i \<phi>'_i w'_i;
  _ :: unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True } ELSE return_spmf False"
  unfolding knowledge_soundness_reduction_ext_def by (simp add: split_def Let_def)
  text \<open>We fold the game into smaller sub games, such that we can combine the individual asserts.\<close>
  also have "\<dots> =  TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK \<phi> i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i
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
 text \<open>We combine the first two asserts\<close>
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK \<phi> i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i
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
  text \<open>WE fold again to accumulate the next two asserts\<close>  
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK \<phi> i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i
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
 text \<open>We merge the next two asserts, but omit repeated checks\<close>
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK \<phi> i;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i 
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
        \<and> \<phi>_i \<noteq> \<phi>'_i  
        \<and> valid_msg \<phi>_i w_i 
        \<and> valid_msg \<phi>'_i w'_i 
        \<and> VerifyEval PK C i \<phi>_i w_i 
        \<and> VerifyEval PK C i \<phi>'_i w'_i 
      \<longleftrightarrow>
        \<phi>_i \<noteq> \<phi>'_i 
        \<and> valid_msg \<phi>_i w_i 
        \<and> valid_msg \<phi>'_i w'_i 
        \<and> VerifyEval PK C i \<phi>_i w_i 
        \<and> VerifyEval PK C i \<phi>'_i w'_i "
      by meson
    then show ?thesis using assert_anding by algebra
  qed
  text \<open>We fold the game into one coherent game again to rearrange asserts.
  We aim to bring the asserts closer together so we can merge them.\<close>
  also have "\<dots> =  TRY do {
    PK \<leftarrow> KeyGen;
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i));
    return_spmf True
    } ELSE return_spmf False"
    unfolding split_def Let_def 
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> =  TRY do {
    PK \<leftarrow> KeyGen;
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK  (E C calc_vec) i));
    return_spmf True
    } ELSE return_spmf False"
  proof -
    have "do {
    PK \<leftarrow> KeyGen;
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i)  
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK  (E C calc_vec) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i));
    return_spmf True
    } = do {
    PK \<leftarrow> KeyGen;
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i));
    return_spmf True
    }"
      using pull_down_assert_spmf_with_assert[of KeyGen \<A>] 
      by (simp add: Let_def split_def)
    then show ?thesis by argo
  qed
  text \<open>We unfold the game again into smaller sub games, so we can accumulate the rearranged assert 
  as well.\<close>
  also have "\<dots> =  TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> (poly (E C calc_vec) i) 
                            \<and> valid_msg \<phi>_i w_i 
                            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i) 
                            \<and> VerifyEval PK C i \<phi>_i w_i 
                            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i));
    return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False"
  unfolding split_def Let_def 
  by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  text \<open>We accumulate the last assert\<close>
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    TRY do {
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    TRY do {
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    TRY do {
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly (E C calc_vec) i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly (E C calc_vec) i) (createWitness PK (E C calc_vec) i));
       return_spmf True
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False"
    using assert_anding by presburger
  text \<open>We fold the sub games together to one clean coherent game.\<close>
  also have "\<dots> = TRY do {
    PK \<leftarrow> KeyGen;
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK \<phi> i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK \<phi> i));
       return_spmf True
    } ELSE return_spmf False"
   unfolding split_def Let_def 
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
 text \<open>Similarly to the prior lemma, we want to make PK accessible in the assert statement and thus
  we unfold KeyGen to reveal the computation of PK.\<close>
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    PK \<leftarrow> return_spmf (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]);
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i)  
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK \<phi> i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK \<phi> i));
       return_spmf True
    } ELSE return_spmf False"
    using key_gen_alt_def
    by (smt (verit, ccfv_SIG) bind_spmf_assoc bind_spmf_cong)
  text \<open>Secondly, we extract the definition of PK out of the spmf into a constant one.\<close>
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK \<phi> i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK \<phi> i));
       return_spmf True
    } ELSE return_spmf False"
    using return_bind_spmf by meson
  text \<open>Lastly we add a statement implied by the other statement in the assert, namely that the 
  witness w_i cannot be equal to `createWitness PK \<phi> i`. This will allow for easier reasoning about 
  the equivalence of the asserts in the next step.\<close>
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha> = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>
            \<and> \<phi>_i \<noteq> (poly \<phi> i) 
            \<and> w_i \<noteq> (createWitness PK \<phi> i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly \<phi> i) (createWitness PK \<phi> i) 
            \<and> VerifyEval PK C i \<phi>_i w_i 
            \<and> VerifyEval PK C i (poly \<phi> i) (createWitness PK \<phi> i));
       return_spmf True
    } ELSE return_spmf False"
    using add_witness_neq_if_eval_neq by algebra
  finally show ?thesis .
qed

lemma fold_split:"i\<le>n \<Longrightarrow> fold f [0..<n] init = fold f [i..<n] (fold f [0..<i] init)"
proof -
  assume asm: "i\<le>n"
  have "fold f [0..<n] init = fold f ([0..<i] @ [i..<n]) init"
    by (metis Nat.add_diff_assoc add_diff_cancel_left' asm length_upt less_imp_le upt_add_eq_append zero_le)
  also have "\<dots> = fold f [i..<n] (fold f [0..<i] init)" 
    by fastforce
  finally show "fold f [0..<n] init = fold f [i..<n] (fold f [0..<i] init)" .
qed

text \<open>Proof Step 3:

We show the equivalence of the content of the assert statements in the alt games i.e.
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
            \<and> w_i \<noteq> (createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (Poly calc_vec) i) 
            \<and> valid_msg \<phi>_i w_i 
            \<and> valid_msg (poly (Poly calc_vec) i) (createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (Poly calc_vec) i) 
            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i \<phi>_i w_i 
            \<and> VerifyEval (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) C i (poly (Poly calc_vec) i) (createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (Poly calc_vec) i)"
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
    w_i \<noteq> createWitness ?PK ?\<phi> i \<and>
    valid_msg \<phi>_i w_i \<and>
    valid_msg (poly ?\<phi> i) (createWitness ?PK ?\<phi> i) \<and>
    VerifyEval ?PK C i \<phi>_i w_i \<and> VerifyEval ?PK C i (poly ?\<phi> i) (createWitness ?PK ?\<phi> i)"
  proof(intro conjI)
    show "length ?PK = length calc_vec"
      using asm by blast

    show valid_msg_generated: "valid_msg (poly ?\<phi> i) (createWitness ?PK ?\<phi> i)" 
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

    show verify_eval_Adversary: "VerifyEval ?PK C i \<phi>_i w_i" 
      using asm by fast 
    
    show verify_eval_generated: "VerifyEval ?PK C i (poly ?\<phi> i) (createWitness ?PK ?\<phi> i)"
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
      unfolding VerifyEval_def createWitness.simps Let_def g_pow_PK_Prod_correct 3 2 1
      using eq_on_e[of "(Poly calc_vec)" i \<alpha>] by blast
    qed

    show "w_i \<noteq> createWitness ?PK ?\<phi> i" 
    proof -
      obtain w_i_pow where w_i_pow: "w_i = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> w_i_pow" 
        using asm 
        unfolding valid_msg_def
        by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)
      obtain crt_Witn_pow where crt_Witn_pow: "createWitness ?PK ?\<phi> i = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> crt_Witn_pow" 
        using valid_msg_generated 
        unfolding valid_msg_def
        by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)

      from verify_eval_Adversary verify_eval_generated 
      have "e w_i (?PK ! 1 \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i 
          = e (createWitness ?PK ?\<phi> i) (?PK ! 1 \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> poly (Poly calc_vec) i" unfolding VerifyEval_def by force
      then have "e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> w_i_pow) ((\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i 
          = e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> crt_Witn_pow) ((\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> poly (Poly calc_vec) i"
        using crt_Witn_pow w_i_pow PK_i
        using add.commute add_diff_cancel_right' d_pos landau_product_preprocess(52) length_upt less_diff_conv nth_map nth_upt power_one_right
        by auto
      then have "e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> w_i_pow) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>-i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> \<phi>_i 
          = e (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> crt_Witn_pow) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>-i)) 
            \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> poly (Poly calc_vec) i"
        using mod_ring_pow_mult_inv_G\<^sub>p by presburger
      then have "e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (w_i_pow * (\<alpha>-i) + \<phi>_i)
          = e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> (crt_Witn_pow * (\<alpha>-i) + poly (Poly calc_vec) i)"
        using e_bilinear by force
      then have "w_i_pow * (\<alpha>-i) + \<phi>_i = crt_Witn_pow * (\<alpha>-i) + poly (Poly calc_vec) i"
        by simp
      then have "w_i_pow \<noteq> crt_Witn_pow"
        using asm by fastforce
      then show ?thesis 
        using w_i_pow crt_Witn_pow pow_on_eq_card by presburger
  qed
  qed (simp add: asm)+
qed linarith

text \<open>Proof step 4:\<close>

text \<open>From the last three steps, we conclude that the know,ledge_soundness_game is the same game as 
the evaluation binding game for the extended reduction adversary.\<close>
lemma knowledge_soundness_game_eq_bind_game_knowledge_soundness_reduction_ext: 
  "knowledge_soundness_game E \<A> \<A>' = bind_game (knowledge_soundness_reduction_ext E \<A> \<A>')"
  unfolding knowledge_soundness_game_alt_def 
            bind_game_knowledge_soundness_reduction_alt_def
            Let_def
  using asserts_are_equal by simp

text \<open>Proof Step 5:

We overestimate the probability of winning the evaluation binding game with the extended adversary 
by winning it with the normal adversary.\<close>
lemma overestimate_reductions: "spmf (bind_game (knowledge_soundness_reduction_ext E \<A> \<A>')) True 
  \<le> spmf (bind_game (knowledge_soundness_reduction E \<A> \<A>')) True"
proof -
   note [simp] = Let_def split_def

   have w_assert_ext: "bind_game (knowledge_soundness_reduction_ext E \<A> \<A>') = TRY do {
    PK \<leftarrow> KeyGen;
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf (length PK = length calc_vec 
                            \<and> C = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (calc_vec!i)) [0..<length PK] \<one>\<^bsub>G\<^sub>p\<^esub>);  
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    _ :: unit \<leftarrow> assert_spmf (valid_msg \<phi>_i w_i);
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
    let b = VerifyEval PK C i \<phi>_i w_i;
    let b' = VerifyEval PK C i \<phi>'_i w'_i;
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True } ELSE return_spmf False"
     unfolding bind_game_alt_def knowledge_soundness_reduction_ext_def 
     by (simp add: split_def Let_def)

   have wo_assert_ext: "bind_game (knowledge_soundness_reduction E \<A> \<A>') = TRY do {
    PK \<leftarrow> KeyGen;
    (C,calc_vec, \<sigma>) \<leftarrow> \<A> PK;
    let \<phi> = E C calc_vec;
    (i, \<phi>_i, w_i) \<leftarrow> \<A>' \<sigma> PK C calc_vec;
    let \<phi>'_i = poly \<phi> i;
    let w'_i = createWitness PK \<phi> i;
    _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> valid_msg \<phi>_i w_i \<and> valid_msg \<phi>'_i w'_i);
    let b = VerifyEval PK C i \<phi>_i w_i;
    let b' = VerifyEval PK C i \<phi>'_i w'_i;
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True } ELSE return_spmf False"
     unfolding bind_game_alt_def knowledge_soundness_reduction_def 
     by (simp add: split_def Let_def)

  text \<open>We show the thesis in ennreal, which implies the plain thesis\<close>
  have "ennreal (spmf (bind_game (knowledge_soundness_reduction_ext E \<A> \<A>')) True) 
    \<le> ennreal (spmf (bind_game (knowledge_soundness_reduction E \<A> \<A>')) True)"
    unfolding w_assert_ext wo_assert_ext
    apply (simp add: spmf_try_spmf ennreal_spmf_bind)
    apply (rule nn_integral_mono)+
    apply (simp add: assert_spmf_def)
    apply (simp add: measure_spmf.emeasure_eq_measure)
    apply (simp add: mult_left_le nn_integral_mono)
    done
    
  then show ?thesis by simp
qed
  
text \<open>Proof Step 6:

Finally we put everything together:
we conclude that for every efficient adversary in the AGM the advantage of winning the 
knowledge soundness game is less equal to breaking the t-SDH assumption.\<close>
theorem knowledge_soundness: 
  "knowledge_soundness_game_advantage E \<A> \<A>' 
  \<le> t_SDH_G\<^sub>p.advantage (eval_bind_reduction (knowledge_soundness_reduction E \<A> \<A>'))"
  using evaluation_binding[of "knowledge_soundness_reduction E \<A> \<A>'"]
    overestimate_reductions[of \<A> \<A>']
  unfolding bind_advantage_def knowledge_soundness_game_advantage_def 
  unfolding knowledge_soundness_game_eq_bind_game_knowledge_soundness_reduction_ext
  by linarith

end

end
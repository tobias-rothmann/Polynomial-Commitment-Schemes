theory KZG_IND_CPA_hiding

imports KZG_correct DL_assumption Cyclic_Group_SPMF_ext Polynomial_Interpolation.Lagrange_Interpolation 

begin

locale hiding_game_def = KZG_correct
begin

text \<open>Although the hiding game will look similar to the Sigma_Commit_Crypto hiding_game, 
The evaluation commitment and verification phase does not exactly mirror the classical 
commitment scheme as defined in Sigma_Commit_Crypto, which is why we will define our own game 
to show this property. 
Explanation:
In a classical commitment-scheme one tries to break the commitment by coming up with two 
plain texts that verify for the same commitment. 
However in the evaluation commitment phase, one tries to come up with a commitment to a 
polynomial that allows to verify the commitment of the evaluation of two different polynomials and the witness 
to these evaluations. This could be modelled in the classical approach, however the semantics would 
not really fit as we are not trying to come up with two different plain texts but with commitments.
\<close>
text \<open>The evaluation commitment scheme functions.\<close>

text \<open>Expose just the public key from the Setup\<close>
definition key_gen:: "'a pk spmf" where
  "key_gen = do {
    (_::'e sk, PK::'a pk) \<leftarrow> Setup;
    return_spmf PK
  }"

definition valid_msg :: "'e eval_value \<Rightarrow> 'a eval_witness \<Rightarrow> bool" where 
  "valid_msg \<phi>_i w_i = (w_i \<in> carrier G\<^sub>p)"

subsection \<open>Game definition\<close>

type_synonym ('a', 'e', 'state) IND_CPA_adversary = 
  "('a' pk \<Rightarrow> 'a' commit \<Rightarrow> ('e', 'a') witness_tuple set \<Rightarrow> ('e' eval_position \<times> 'e' eval_position \<times> 'state) spmf)
   \<times> ('e' eval_value \<Rightarrow> 'state \<Rightarrow> bool spmf)"

definition IND_CPA_hiding_game :: "'e polynomial \<Rightarrow> 'e eval_position set \<Rightarrow> ('a,'e,'state) IND_CPA_adversary \<Rightarrow> bool spmf"
  where "IND_CPA_hiding_game \<phi> I \<A> = TRY do {
     PK \<leftarrow> key_gen;
     (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK (Commit PK \<phi>) ((\<lambda>i. CreateWitness PK \<phi> i) ` I);
     b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"

text \<open>put C and eval_poses in parameter and assert\<close>

definition hiding_advantage :: "'e polynomial \<Rightarrow> 'e eval_position set \<Rightarrow> ('a,'e,'state) IND_CPA_adversary \<Rightarrow> real"
  where "hiding_advantage \<phi> I \<A> \<equiv> spmf (IND_CPA_hiding_game \<phi> I \<A>) True"

subsection \<open>reduction game\<close>

type_synonym ('a', 'e', 'state) next_coord_adversary = 
  "(('e' eval_position \<times> 'e' eval_value) set \<Rightarrow> ('e' eval_position \<times> 'e' eval_position \<times> 'state) spmf)
   \<times> ('e' eval_value \<Rightarrow> 'state \<Rightarrow> bool spmf)"

definition next_coord_game :: "'e polynomial \<Rightarrow> 'e eval_position set \<Rightarrow> ('a,'e,'state) next_coord_adversary \<Rightarrow> bool spmf"
  where "next_coord_game \<phi> I \<A> = TRY do {
    (i, j, \<sigma>) \<leftarrow> (fst \<A>) ((\<lambda>i. (i, poly \<phi> i)) ` I);
    b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"

sublocale DL_G\<^sub>p: DL G\<^sub>p "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding DL_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

subsection \<open>reduction fun\<close>

fun reduction :: "('a,'e,'state) IND_CPA_adversary 
  \<Rightarrow> ('e eval_position \<times> 'e eval_value) set \<Rightarrow> ('e eval_position \<times> 'e eval_position \<times> 'state) spmf" where
  "reduction \<A> Eval_set = do {
   x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
   let (\<alpha>::'e mod_ring) = of_int_mod_ring (int x);
   let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
   let g_exp =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>;
   ((fst \<A>) PK g_exp ((\<lambda>(x,y). (x,y, g_exp)) ` Eval_set))
  }"

theorem
  assumes deg_\<phi>_le_max_deg: "degree \<phi> \<le> max_deg"
  and deg_\<phi>_gr_0: "degree \<phi> > 0"
  shows "IND_CPA_hiding_game \<phi> I \<A> = next_coord_game \<phi> I (reduction \<A>, snd \<A>)"
  including monad_normalisation
proof -
  note [simp] = Let_def split_def
  let ?\<alpha> = "(\<lambda>x. (of_int_mod_ring (int x) :: 'e mod_ring))"
  let ?PK = "(\<lambda>x. map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int x) :: 'e mod_ring)^t)) [0..<max_deg+1])"

  have "IND_CPA_hiding_game \<phi> I \<A> = TRY do {
     PK \<leftarrow> key_gen;
     (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK (Commit PK \<phi>) ((\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) ` I);
     b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"
    unfolding IND_CPA_hiding_game_def 
    unfolding CreateWitness_def createWitness.simps Let_def ..
  also have "\<dots> = TRY do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let (\<alpha>::'e mod_ring) = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK (Commit PK \<phi>) ((\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) ` I);
     b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"
    unfolding key_gen_def Setup_def by simp
  also have "\<dots> = TRY do {
     x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let (\<alpha>::'e mod_ring) = of_int_mod_ring (int x);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    let C = Commit PK \<phi>;
    let W = (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) ` I;
    (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK C W;
     b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"
    by presburger
  also have "\<dots> = TRY do {
     x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let (PK, C,W) = (?PK x, Commit (?PK x) \<phi>, (\<lambda>i. (i, poly \<phi> i, createWitness (?PK x) \<phi> i)) ` I);
    (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK C W;
     b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"
    unfolding Let_def by force
  also have "\<dots> = TRY do {
     x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let (PK, C,W) = (?PK x, \<^bold>g ^ (poly \<phi> (?\<alpha> x)), (\<lambda>i. (i, poly \<phi> i, createWitness (?PK x) \<phi> i)) ` I);
    (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK C W;
     b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"
    unfolding Commit_def 
    using g_pow_PK_Prod_correct[OF deg_\<phi>_le_max_deg]
    by algebra
  also have "\<dots> = TRY do {
     x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let (PK, C,W) = (?PK x, \<^bold>g ^ (poly \<phi> (?\<alpha> x)), (\<lambda>i. (i, poly \<phi> i, \<^bold>g ^  (poly (\<psi>_of \<phi> i) (?\<alpha> x)))) ` I);
    (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK C W;
     b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"
  proof -
    have deg_\<psi>: "\<And>i. degree (\<psi>_of \<phi> i) \<le> max_deg"
      using assms(1) degree_q_le_\<phi> le_trans by blast
    show ?thesis
      unfolding createWitness.simps 
      using g_pow_PK_Prod_correct[OF deg_\<psi>]
      by algebra
  qed
  also have "\<dots> = TRY do {
    (PK,C,W) \<leftarrow> map_spmf (\<lambda>x. (?PK x, \<^bold>g ^ (poly \<phi> (?\<alpha> x)), (\<lambda>i. (i, poly \<phi> i, \<^bold>g ^  (poly (\<psi>_of \<phi> i) (?\<alpha> x)))) ` I)) (sample_uniform (order G\<^sub>p));
    (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK C W;
     b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"
    by (simp add: bind_map_spmf o_def)
  also have "\<dots> = TRY do {
    (PK,C,W) \<leftarrow> map_spmf (\<lambda>x. (?PK x, \<^bold>g ^ (?\<alpha> x), (\<lambda>i. (i, poly \<phi> i, \<^bold>g ^  (?\<alpha> x))) ` I)) (sample_uniform (order G\<^sub>p));
    (i, j, \<sigma>) \<leftarrow> (fst \<A>) PK C W;
     b \<leftarrow> coin_spmf;
     let eval = (if b then poly \<phi> i else poly \<phi> j);
     b' \<leftarrow> (snd \<A>) eval \<sigma>;
     return_spmf (b=b')
  } ELSE coin_spmf"
    sorry
  also have "\<dots> = TRY do {
    (i, j, \<sigma>) \<leftarrow> reduction \<A> ((\<lambda>i. (i, poly \<phi> i)) ` I);
    b \<leftarrow> coin_spmf;
    let eval = (if b then poly \<phi> i else poly \<phi> j);
    b' \<leftarrow> (snd \<A>) eval \<sigma>;
    return_spmf (b=b')
  } ELSE coin_spmf"  
    unfolding reduction.simps
    Let_def split_def
    by (simp add: bind_map_spmf o_def image_image)
  also have "\<dots> = next_coord_game \<phi> I (reduction \<A>, snd \<A>)"
    unfolding next_coord_game_def
    by fastforce
  finally show ?thesis .
qed

end

end
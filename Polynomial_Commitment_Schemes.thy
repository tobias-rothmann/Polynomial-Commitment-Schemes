theory Polynomial_Commitment_Schemes 
  imports CryptHOL.CryptHOL "HOL-Computational_Algebra.Polynomial" Sigma_Commit_Crypto.Commitment_Schemes
begin

locale abstract_polynomial_commitment_scheme =
  fixes key_gen :: "('ck \<times> 'vk) spmf" \<comment> \<open>outputs the keys received by the two parties\<close>
    and commit :: "'ck \<Rightarrow> 'r::zero poly  \<Rightarrow> ('commit \<times> 'trapdoor) spmf" 
      \<comment> \<open>outputs the commitment as well as the secret, which might be used to derive witnesses, 
         and the opening values sent by the committer in the reveal phase\<close>    
    and verify_poly :: "'vk \<Rightarrow> 'r poly \<Rightarrow> 'commit \<Rightarrow> 'trapdoor \<Rightarrow> bool"       
      \<comment> \<open>checks whether the polynomial corresponds to the commitment\<close>
    and eval :: "'ck \<Rightarrow> 'trapdoor \<Rightarrow> 'r poly \<Rightarrow> 'argument \<Rightarrow> ('evaluation \<times> 'witness)"
      \<comment> \<open>outputs a point and a witness\<close>
    and verify_eval :: "'vk \<Rightarrow> 'commit \<Rightarrow> 'argument \<Rightarrow> ('evaluation \<times> 'witness) \<Rightarrow> bool"
      \<comment> \<open>checks whether the point is on the polynomial corresponding to the commitment\<close>
    and valid_poly :: "'r poly \<Rightarrow> bool" \<comment> \<open>checks whether a polynomial is a valid message e.g. it's 
        degree is bounded\<close>
    and valid_eval :: "('evaluation \<times> 'witness) \<Rightarrow> bool"
begin

sublocale cs: abstract_commitment key_gen commit verify_poly valid_poly .

definition correct_cs_game :: "'r poly \<Rightarrow> bool spmf"
  where "correct_cs_game \<equiv> cs.correct_game"

definition correct_cs 
  where "correct_cs \<equiv> cs.correct"

definition correct_eval_game :: "'r poly \<Rightarrow> 'argument \<Rightarrow> bool spmf"
  where "correct_eval_game p i = do {
  (ck, vk) \<leftarrow> key_gen;
  (c,d) \<leftarrow> commit ck p;
  let w  = eval ck d p i;
  return_spmf (verify_eval vk c i w)
  }"

lemma lossless_correct_eval_game: "\<lbrakk> lossless_spmf key_gen; lossless_spmf TI;
          \<And>ck p. valid_msg p \<Longrightarrow> lossless_spmf (commit ck p)\<rbrakk>
              \<Longrightarrow> valid_msg p \<Longrightarrow> lossless_spmf (correct_eval_game p i)"  
  by (simp add: correct_eval_game_def split_def Let_def)
 
definition correct_eval
  where "correct_eval \<equiv> (\<forall>p i. valid_poly p \<longrightarrow> spmf (correct_eval_game p i) True = 1)"

definition poly_bind_game
  where "poly_bind_game \<equiv> cs.bind_game"

definition poly_bind_advantage
  where "poly_bind_advantage \<equiv> cs.bind_advantage"

type_synonym ('ck', 'commit', 'argument', 'evaluation', 'witness')  eval_bind_adversary = 
  "'ck' \<Rightarrow> ('commit' \<times> 'argument'  \<times> 'evaluation' \<times> 'witness'  \<times> 'evaluation' \<times> 'witness') spmf"

definition eval_bind_game :: "('ck, 'commit, 'argument, 'evaluation, 'witness) eval_bind_adversary \<Rightarrow> bool spmf"
  where "eval_bind_game \<A> = TRY do {
  (ck, vk) \<leftarrow> key_gen;
  (c, i, v, w, v', w') \<leftarrow> \<A> ck;     
  _ :: unit \<leftarrow> assert_spmf (v \<noteq> v' \<and> valid_eval (v, w) \<and> valid_eval (v', w'));                     
  let b = verify_eval vk c i (v,w);
  let b' = verify_eval vk c i (v',w');
  return_spmf (b \<and> b')} ELSE return_spmf False"  

definition eval_bind_advantage :: "('ck, 'commit, 'argument, 'evaluation, 'witness) eval_bind_adversary \<Rightarrow> real"
  where "eval_bind_advantage \<A> \<equiv> spmf (eval_bind_game \<A>) True"

type_synonym ('r', 'vk', 'commit', 'argument', 'evaluation', 'witness')  eval_hiding_adversary = 
  "('vk' \<Rightarrow> 'commit' \<Rightarrow> 'argument' list \<Rightarrow> ('evaluation' \<times> 'witness') list \<Rightarrow> ('r' poly) spmf)"

definition eval_hiding_game :: "'r poly \<Rightarrow> 'argument list \<Rightarrow> ('r, 'vk, 'commit, 'argument, 'evaluation, 'witness) 
  eval_hiding_adversary \<Rightarrow> bool spmf"
  where "eval_hiding_game p I \<A> = TRY do {
  (ck, vk) \<leftarrow> key_gen;
  (c,d) \<leftarrow> commit ck p; 
  let W = map (\<lambda>i. eval ck d p i) I; 
  p' \<leftarrow> \<A> vk c I W;
  return_spmf (p = p')} ELSE return_spmf False"

definition hiding_advantage :: "'r poly \<Rightarrow> 'argument list \<Rightarrow> ('r, 'vk, 'commit, 'argument, 'evaluation, 'witness) 
  eval_hiding_adversary \<Rightarrow> real"
  where "hiding_advantage p i \<A> \<equiv> spmf (eval_hiding_game p i \<A>) True"


type_synonym ('ck', 'commit', 'state') knowledge_soundness_adversary1 = "'ck' \<Rightarrow> ('commit' \<times> 'state') spmf"

type_synonym ('state', 'argument', 'evaluation', 'witness') knowledge_soundness_adversary2 
  = "'state' \<Rightarrow> ('argument' \<times> ('evaluation' \<times> 'witness')) spmf"

type_synonym ('ck', 'commit', 'state', 'argument', 'evaluation', 'witness') 
  knowledge_soundness_adversary =                                                           
  "('ck', 'commit', 'state') knowledge_soundness_adversary1 
  \<times> ('state', 'argument', 'evaluation', 'witness') knowledge_soundness_adversary2"  

type_synonym ('r', 'commit', 'trapdoor') extractor = "'commit' \<Rightarrow> ('r' poly \<times> 'trapdoor') spmf"
                                                                                                 
definition knowledge_soundness_game :: "('ck, 'commit, 'state, 'argument, 'evaluation, 'witness) 
  knowledge_soundness_adversary \<Rightarrow> ('r, 'commit, 'trapdoor) extractor \<Rightarrow> bool spmf"
  where "knowledge_soundness_game \<A> E = TRY do {
  let (\<A>1,\<A>2) = \<A>;
  (ck,vk) \<leftarrow> key_gen;
  (c,\<sigma>) \<leftarrow> \<A>1 ck;
  (p,d) \<leftarrow> E c;
  (i, w) \<leftarrow> \<A>2 \<sigma>;
  let (p_i,_) = w;
  let (p_i',_) = eval ck d p i;         
  return_spmf (verify_eval vk c i w \<and> p_i \<noteq> p_i' \<and> valid_eval w)       
  } ELSE return_spmf False"

definition knowledge_soundness_advantage :: " ('ck, 'commit, 'state, 'argument, 'evaluation, 'witness) 
  knowledge_soundness_adversary \<Rightarrow> ('r, 'commit, 'trapdoor) extractor \<Rightarrow> real"
  where "knowledge_soundness_advantage \<A> E \<equiv> spmf (knowledge_soundness_game \<A> E) True"

end

end                                                         
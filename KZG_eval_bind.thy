theory KZG_eval_bind

imports KZG_correct "Sigma_Commit_Crypto.Commitment_Schemes" "tSDH_assumption"

begin

locale bind_game_def = KZG_correct
begin

subsection \<open>Function definitions for the binding game, mirroring the KZG evaluation commit phase\<close>

text \<open>The abstract commitment scheme from Sigma_Commit_Crypto uses 4 functions.\<close>

definition SCC_key_gen:: "('a pk \<times> 'a pk) spmf" where
  "SCC_key_gen = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x);
    PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1] in
    return_spmf (PK, PK)
  }"

text \<open>Commit is the triple of eval position, eval value, and eval witness. 
Opening is the polynomial and the evaluation position.\<close>
definition SCC_CreateWitness :: "'a pk \<Rightarrow> 'e polynomial \<times> 'e eval_position  
\<Rightarrow> (('e eval_position \<times> 'e eval_value \<times> 'a eval_witness) \<times> ('e polynomial \<times> 'e eval_position)) spmf"
where 
  "SCC_CreateWitness PK plain = do {
    let \<phi> = fst plain;
        i = snd plain 
    in
    let \<phi>_of_i = poly (of_qr \<phi>) i; \<comment>\<open>\<phi>(i)\<close>
        \<psi> = \<psi>_of \<phi> i; \<comment>\<open>\<psi> in \<phi>(x) - \<phi>(i) = (x-i) * \<psi>(x)\<close>
        w_i = g_pow_PK_Prod PK \<psi> \<comment>\<open>g^\<psi>(\<alpha>)\<close>
    in
    return_spmf ((i, \<phi>_of_i,w_i), (\<phi>,i))
  }" 

end

end
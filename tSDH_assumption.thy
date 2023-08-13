theory tSDH_assumption

imports "Sigma_Commit_Crypto.Commitment_Schemes"

begin

locale t_SDH = G\<^sub>p : cyclic_group G
for G (structure) and t::nat
begin

(*type_synonym 'grp' t_SDH_adversary = "'grp' list \<Rightarrow> ('q mod_ring *'grp') spmf"*)
type_synonym 'grp adversary = "'grp list \<Rightarrow> (nat *'grp) spmf"


definition game :: "'a adversary \<Rightarrow> bool spmf" where 
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
    return_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g) 
  } ELSE return_spmf False"


definition advantage :: " 'a adversary \<Rightarrow> real"
  where "advantage \<A> = spmf (game \<A>) True" \<comment>\<open>subtract Pr random (\<alpha>+c)\<close>

(* adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def  *)
lemma game_alt_def:
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g);
    return_spmf (True) } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
   have "?lhs = TRY do {
      \<alpha> \<leftarrow> sample_uniform (order G);
      TRY do {
        (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
          TRY return_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g) ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding split_def game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      \<alpha> \<leftarrow> sample_uniform (order G);
      TRY do {
        (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g);
            return_spmf True
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
 
end
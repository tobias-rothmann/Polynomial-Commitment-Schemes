theory DL_assumption

imports "Sigma_Commit_Crypto.Commitment_Schemes" "Berlekamp_Zassenhaus.Finite_Field"

begin

text\<open>The DL game and advantage as in the Definition 2.1 of the original paper 
"Constant-Size Commitments to Polynomials and Their Applications".
You can find the paper here: https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf\<close>

locale DL = G : cyclic_group G
  for G:: "('a, 'b) cyclic_group_scheme" (structure)
  and to_type :: "nat \<Rightarrow> ('c::prime_card) mod_ring"
  and exp :: "'a \<Rightarrow> 'c mod_ring \<Rightarrow> 'a"
begin

type_synonym ('grp,'mr) adversary = "'grp \<Rightarrow> 'mr mod_ring spmf"

text \<open>The discrete Logarithm game\<close>
definition game :: "('a,'c) adversary \<Rightarrow> bool spmf" where 
  "game \<A> = TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G);
    a' \<leftarrow> \<A> (exp \<^bold>g (to_type a));
    return_spmf (to_type a = a') 
  } ELSE return_spmf False"

text \<open>The advantage is that the Adversary wins the game. 
For the DL assumption to hold this advantage should be negligible.\<close>
definition advantage :: " ('a,'c) adversary \<Rightarrow> real"
  where "advantage \<A> = spmf (game \<A>) True" 
  

text \<open>An alternative but equivalent game for the DL-game. This alternative game capsulates the 
event that the Adversary wins in the assert_spmf statement.
adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def\<close>
lemma game_alt_def:
  "game \<A> = TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G);
    a' \<leftarrow> \<A> (exp \<^bold>g (to_type a));
    _::unit \<leftarrow> assert_spmf (to_type a = a');
    return_spmf True 
  } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
   have "?lhs =  TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G);
    TRY do {
    a' \<leftarrow> \<A> (exp \<^bold>g (to_type a));
    TRY do {
   return_spmf (to_type a = a')
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding split_def game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      a \<leftarrow> sample_uniform (Coset.order G);
      TRY do {
        a' \<leftarrow> \<A> (exp \<^bold>g (to_type a));
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (to_type a = a');
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
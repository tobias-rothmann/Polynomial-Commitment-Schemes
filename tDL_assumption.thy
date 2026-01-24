theory tDL_assumption

imports "Sigma_Commit_Crypto.Commitment_Schemes" "Berlekamp_Zassenhaus.Finite_Field"

begin

text\<open>The t-DL game and advantage defined as in the section 6 of the paper 
"The Algebraic Group Model and its Applications" by Fuchsbauer, Kiltz, and Loss.
You can find the paper here: https://eprint.iacr.org/2017/620.pdf\<close>

locale t_DL = G : cyclic_group G
  for G:: "('a, 'b) cyclic_group_scheme" (structure) 
  and t::nat  
  and to_type :: "nat \<Rightarrow> ('c::prime_card) mod_ring"
  and exp :: "'a \<Rightarrow> 'c mod_ring \<Rightarrow> 'a"
begin

type_synonym ('grp,'mr) adversary = "'grp list \<Rightarrow> ('mr mod_ring) spmf"

declare [[show_types]]
text \<open>The t-Dl game states that given a t+1-long tuple in the form of (g,g^\<alpha>,g^\<alpha>^2,...,g^\<alpha>^t)
the Adversary has to return \<alpha>)).\<close>
definition game :: "('a,'c) adversary \<Rightarrow> bool spmf" where 
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (Coset.order G);
    \<alpha>' \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
    return_spmf (to_type \<alpha> = \<alpha>') 
  } ELSE return_spmf False"

text \<open>The advantage is that the Adversary wins the game. 
For the t-DL assumption to hold this advantage should be negligible.\<close>
definition advantage :: " ('a,'c) adversary \<Rightarrow> real"
  where "advantage \<A> = spmf (game \<A>) True" 

text \<open>An alternative but equivalent game for the t-DL-game. This alternative game encapsulates the 
event that the Adversary wins in the assert_spmf statement.
adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def\<close>
lemma game_alt_def:
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (Coset.order G);
    \<alpha>' \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
    _::unit \<leftarrow> assert_spmf (to_type \<alpha> = \<alpha>');
    return_spmf True 
  } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
   have "?lhs = TRY do {
      \<alpha> \<leftarrow> sample_uniform (Coset.order G);
      TRY do {
        \<alpha>' \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
          TRY return_spmf (to_type \<alpha> = \<alpha>') 
          ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding split_def game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      \<alpha> \<leftarrow> sample_uniform (Coset.order G);
      TRY do {
       \<alpha>' \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (to_type \<alpha> = \<alpha>');
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
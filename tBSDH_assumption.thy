theory tBSDH_assumption

imports "Sigma_Commit_Crypto.Commitment_Schemes" "Berlekamp_Zassenhaus.Finite_Field"

begin

text\<open>The t-BSDH game and advantage as in the section 2.4 of the original paper 
"Constant-Size Commitments to Polynomials and Their Applications".
You can find the paper here: https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf\<close>

text \<open>The t-BSDH assumption is a extension of the t-SDH assumption (of sectiomn 2.3. in the paper). 
Similar to the t-SDH assumpotion it requires the adversary to put out some c and some group element 
g' such that a certain group elment g exponentiated with 1/(a+c) is equal to g'. While the group 
element g was simply the generator of G in the t-SDH assumotion, it is now the result of the 
bilinear function e of the same generator of G.\<close>
locale t_BSDH = G : cyclic_group G + G\<^sub>T : cyclic_group G\<^sub>T 
  for G:: "('a, 'b) cyclic_group_scheme" (structure) and G\<^sub>T :: "('c, 'd) cyclic_group_scheme" (structure)
  and t::nat  
  and to_type :: "nat \<Rightarrow> ('e::prime_card) mod_ring"
  and exp :: "'a \<Rightarrow> 'e mod_ring \<Rightarrow> 'a"
  and exp_G\<^sub>T :: "'c \<Rightarrow> 'e mod_ring \<Rightarrow> 'c"
  and e :: "'a \<Rightarrow> 'a \<Rightarrow> 'c" \<comment>\<open>bilinear function from G to GT \<close>
begin

type_synonym ('grp,'mr, 'tgrp) adversary = "'grp list \<Rightarrow> ('mr mod_ring *'tgrp) spmf"

text \<open>The t-BSDH game states that given a t+1-long tuple in the form of (g,g^\<alpha>,g^\<alpha>^2,...,g^\<alpha>^t)
the Adversary has to return an element c and e (g,g)^(1/(c+\<alpha>)).\<close>
definition game :: "('a,'e,'c) adversary \<Rightarrow> bool spmf" where 
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (Coset.order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
    return_spmf (exp_G\<^sub>T (e \<^bold>g \<^bold>g) (1/((to_type \<alpha>)+c)) = g) 
  } ELSE return_spmf False"

text \<open>The advantage is that the Adversary wins the game. 
For the t-BSDH assumption to hold this advantage should be negligible.\<close>
definition advantage :: " ('a,'e,'c) adversary \<Rightarrow> real"
  where "advantage \<A> = spmf (game \<A>) True" 

text \<open>An alternative but equivalent game for the t-BSDH-game. This alternative game capsulates the 
event that the Adversary wins in the assert_spmf statement.
adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def\<close>
lemma game_alt_def:
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (Coset.order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
    _::unit \<leftarrow>assert_spmf (exp_G\<^sub>T (e \<^bold>g \<^bold>g) (1/((to_type \<alpha>)+c)) = g);
    return_spmf True
  } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
   have "?lhs = TRY do {
      \<alpha> \<leftarrow> sample_uniform (Coset.order G);
      TRY do {
        (c, g) \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
          TRY return_spmf (exp_G\<^sub>T (e \<^bold>g \<^bold>g) (1/((to_type \<alpha>)+c)) = g) ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding split_def game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      \<alpha> \<leftarrow> sample_uniform (Coset.order G);
      TRY do {
        (c, g) \<leftarrow> \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (exp_G\<^sub>T (e \<^bold>g \<^bold>g) (1/((to_type \<alpha>)+c)) = g);
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
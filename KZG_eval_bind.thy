theory KZG_eval_bind

imports KZG_correct "tSDH_assumption"

begin

locale bind_game_def = KZG_correct
begin

subsection \<open>Function definitions for the binding game, mirroring the KZG evaluation commit phase\<close>

text \<open>Altough the binding game will look similar to the Sigma_Commit_Crypto bind_game, 
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

definition key_gen:: "'a pk spmf" where
  "key_gen = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x);
    PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1] in
    return_spmf PK
  }"

definition verify :: "'a pk \<Rightarrow> 'a commit \<Rightarrow> 'e eval_position \<Rightarrow> 'e eval_value \<Rightarrow> 'a eval_witness \<Rightarrow> bool"
where 
  "verify PK C i \<phi>_of_i w_i =
    (e w_i (PK!1  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i) = e C \<^bold>g\<^bsub>G\<^sub>p\<^esub>) 
    \<comment>\<open>e(g^\<psi>(\<alpha>), g^\<alpha> / g^i) \<otimes> e(g,g)^\<phi>(i) = e(C, g)\<close>"
                    
subsection \<open>Game definition\<close>

type_synonym ('a', 'e')  adversary = 
  "'a' pk \<Rightarrow> 
 ('a' commit \<times> 'e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness \<times> 'e' eval_value \<times> 'a' eval_witness) spmf"

definition bind_game :: "('a, 'e) adversary \<Rightarrow> bool spmf"
  where "bind_game \<A> = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i); \<comment>\<open>maybe \<or>?\<close>
  let b = verify PK C i \<phi>_i w_i;
  let b' = verify PK C i \<phi>'_i w'_i;
  return_spmf (b \<and> b')} ELSE return_spmf False"

subsection \<open>putting together the binding game\<close>
                                                        
subsection \<open>t-SDH game\<close>

sublocale t_SDH_G\<^sub>p: t_SDH G\<^sub>p max_deg "of_int_mod_ring \<circ> int" pow_mod_ring_G\<^sub>p
  unfolding t_SDH_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

text \<open>bind_commit.bind_game is the binding game we will reduce to the t-SDH assumption, thus showing 
that cracking the KZG's evaluation binding is at least as hard as solving the t-SDH problem. Hence 
proving the security of the KZG for groups where the t-SDH is difficult.\<close>

subsection \<open>Defining a reduction game to t-SDH\<close>


text \<open>TODO update: Intuetively what we want to show is that if we have an adversary that can compute two 
polynomials such that they have the same commitment in polynomial time, we can construct an 
algorithm, using that adversary, that can solve the t-SDH in polynomial time, thus breaking the 
t-SDH assumption.\<close>

text \<open>TODO update: The reduction: 
An adversary for the KZG polynomial binding can output two polynomials \<phi> and \<phi>' that have the same 
commitment, i.e g^\<phi>(\<alpha>) = g^\<phi>(\<alpha>), which is equivalent to \<phi>(\<alpha>) = \<phi>'(\<alpha>) (same argument as in the 
function above). Hence (\<phi>-\<phi>')(\<alpha>) = 0, so (\<phi>-\<phi>') has a root at \<alpha>. Furthermore we have g^\<alpha> in the 
public key at position 1. Hence we can use the find_\<alpha> function to compute \<alpha> in 
polynomial time. Given \<alpha> we can easily compute a c and a g' such that g^(1/((\<alpha>+c))) = g'.
E.g. c=0 and g' = g^(1/\<alpha>)
Hence we can break the t-SDH assumption, as we have a polynomial-time algorithm to compute (c,g).
\<close>
fun bind_reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e) t_SDH.adversary"                     
where
  "bind_reduction \<A> PK = do {
  (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> verify PK C i \<phi>_of_i w_i 
                            \<and> verify PK C i \<phi>'_of_i w'_i); 
  \<comment>\<open>maybe \<or>? or w uneq not even necessary?\<close>
  return_spmf (-i::'e mod_ring, (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)) )}"
end

locale bind_game_proof = bind_game_def
begin

subsubsection \<open>helping lemmas\<close>

text \<open>An alternative but equivalent game for the ealuation binding game. 
This alternative game capsulates the 
event that the Adversary wins in the assert_spmf statement.
It's a closely adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def\<close>
lemma bind_game_alt_def:
  "bind_game \<A> = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i);
  let b = verify PK C i \<phi>_i w_i;
  let b' = verify PK C i \<phi>'_i w'_i;
  _ :: unit \<leftarrow> assert_spmf (b \<and> b');
  return_spmf True } ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do {
      PK \<leftarrow> key_gen;
      TRY do {
        (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i);
          TRY return_spmf (verify PK C i \<phi>_i w_i \<and> verify PK C i \<phi>'_i w'_i) ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding split_def bind_game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      PK \<leftarrow> key_gen;
      TRY do {
        (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i);
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (verify PK C i \<phi>_i w_i \<and> verify PK C i \<phi>'_i w'_i);
            return_spmf True
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"   
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = ?rhs"
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  finally show ?thesis .
qed

lemma assert_anding: "TRY do {
          _ :: unit \<leftarrow> assert_spmf (a);
            _ :: unit \<leftarrow> assert_spmf (b);
            return_spmf True
        } ELSE return_spmf False 
    = TRY do {
          _ :: unit \<leftarrow> assert_spmf (a \<and> b);
          return_spmf True
      } ELSE return_spmf False"
  by (simp add: try_bind_assert_spmf)

lemma two_eval_verify_imp_tSDH_break: 
  assumes "\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> verify ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<alpha>)^t)) [0..<max_deg+1])) C i \<phi>_of_i w_i 
                            \<and> verify ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<alpha>)^t)) [0..<max_deg+1])) C i \<phi>'_of_i w'_i"
  shows "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha> + (-i))) 
                              = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i))"
proof -
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<alpha>)^t)) [0..<max_deg+1])"
  obtain \<psi>\<^sub>i where "w_i = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<psi>\<^sub>i" try0
  
  have "verify (?PK \<alpha>) C i \<phi>_of_i w_i = (e w_i ((\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i) = e C \<^bold>g\<^bsub>G\<^sub>p\<^esub>)" 
    unfolding verify_def
    using PK_i[of 1 max_deg] d_pos by force
  show ?thesis 
    
    sorry
qed

subsubsection \<open>KZG eval bind game to reduction game - equivalence theorem\<close>

theorem poly_bind_game_eq_t_SDH_strong_red:
  shows "bind_game \<A> = t_SDH_G\<^sub>p.game (bind_reduction \<A>)"
proof -
  note [simp] = Let_def split_def

  text \<open>abbreviations for the mod_ring version of sample uniform nat 
  and the public key\<close>
  let ?\<alpha> = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>)^t)) [0..<max_deg+1])"

  have "t_SDH_G\<^sub>p.game (bind_reduction \<A>) = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> verify (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> verify (?PK \<alpha>) C i \<phi>'_of_i w'_i);
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False"
    by (force simp add: t_SDH_G\<^sub>p.game_alt_def[of "(bind_reduction \<A>)"])
  text \<open>Goal is to erase the second assert statement, such that we just end up with the 
  evaluation_game. To do that, we first merge the two asserts and show that the first assert's 
  statement implies the second one's statement, hence we can leave the second assert's statement 
  out and are left with only the first assert statement.\<close>
  also have "\<dots> = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> verify (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> verify (?PK \<alpha>) C i \<phi>'_of_i w'_i);
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False 
  } ELSE return_spmf False 
  } ELSE return_spmf False "
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
    TRY do {
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> verify (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> verify (?PK \<alpha>) C i \<phi>'_of_i w'_i
                            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) 
                              = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False 
  } ELSE return_spmf False 
  } ELSE return_spmf False "  
  using assert_anding by presburger
  also have "\<dots> = TRY do { 
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, i, \<phi>_of_i, w_i, \<phi>'_of_i, w'_i) \<leftarrow> \<A> (?PK \<alpha>);
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i \<and> w_i \<noteq> w'_i 
                            \<and> verify (?PK \<alpha>) C i \<phi>_of_i w_i 
                            \<and> verify (?PK \<alpha>) C i \<phi>'_of_i w'_i
                            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(?\<alpha> \<alpha> + (-i))) 
                              = (w_i \<div>\<^bsub>G\<^sub>p\<^esub> w'_i) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<phi>'_of_i - \<phi>_of_i)));
    return_spmf True 
  } ELSE return_spmf False"



  
    text \<open>We start with the poly bind game and perform logical 
  transitions until we obtain the t-SDH game with the (stronger-)reduction\<close>
  have "bind_game \<A> = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i);
  _ :: unit \<leftarrow> assert_spmf (verify PK C i \<phi>_i w_i \<and> verify PK C i \<phi>'_i w'_i);  
  return_spmf True} ELSE return_spmf False"
    using bind_game_alt_def by presburger
  also have "\<dots> = TRY do {
  PK \<leftarrow> key_gen;
    TRY do {
    (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
      TRY do {
      _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i);
      _ :: unit \<leftarrow> assert_spmf (verify PK C i \<phi>_i w_i \<and> verify PK C i \<phi>'_i w'_i);  
      return_spmf True
      } ELSE return_spmf False 
    } ELSE return_spmf False 
  } ELSE return_spmf False"
   unfolding split_def Let_def
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
  PK \<leftarrow> key_gen;
  TRY do {
    (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
      TRY do {
      _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
                                \<and> verify PK C i \<phi>_i w_i 
                                \<and> verify PK C i \<phi>'_i w'_i);  
      return_spmf True
      } ELSE return_spmf False 
    } ELSE return_spmf False 
  } ELSE return_spmf False"
    using assert_anding by presburger
  also have "\<dots> = TRY do {
  PK \<leftarrow> key_gen;
  (C, i, \<phi>_i, w_i, \<phi>'_i, w'_i) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf (\<phi>_i \<noteq> \<phi>'_i \<and> w_i \<noteq> w'_i 
                            \<and> verify PK C i \<phi>_i w_i 
                            \<and> verify PK C i \<phi>'_i w'_i);  
  return_spmf True} ELSE return_spmf False"
   unfolding split_def Let_def
   by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp

  show ?thesis unfolding bind_game_def t_SDH_G\<^sub>p.game_def
    sorry
qed

end

end
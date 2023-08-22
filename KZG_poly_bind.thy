theory KZG_poly_bind

imports KZG_correct "Sigma_Commit_Crypto.Commitment_Schemes" tSDH_assumption
(*maybe*)  "Berlekamp_Zassenhaus.Finite_Field_Factorization" Complex_Main

begin

section \<open>polynomial binding\<close>
text \<open>We show that the KZG is polynomial binding for every polynomial of degree <= deg_t.
We use the Sigma_Commit_Crypto template to prove the binding game.
The proof is adapted from the Appendix C.1 in the original paper:
A. Kate, G. Zaverucha, and I. Goldberg. Polynomial commitments. Technical report, 2010. 
CACR 2010-10, Centre for Applied Cryptographic Research, University of Waterloo 
(available at https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf)\<close>

locale bind_game_def = KZG_correct
begin

subsection \<open>Function definitions for the binding game, mirroring the KZG poly commit phase\<close>

text \<open>The abstract commitment scheme from Sigma_Commit_Crypto uses 4 functions.\<close>

text\<open>1. The key_gen function, that distributes the key's for prover and verifier. Those keys are in the 
case of the KZG both the same public key (remember the KZG uses a trusted setup.) Hence we copy the 
Setup function from KZG_Def but let it return the the public key for prover and verifier\<close>
definition SCC_key_gen:: "('a pk \<times> 'a pk) spmf" where
  "SCC_key_gen = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x);
    PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1] in
    return_spmf (PK, PK)
  }"

text \<open>2. the Commit function, that commits to the plain text (polynomials in the KZG case).
The Sigma_Commit_Crypto Commit function gives the Commitment, just like the KZG defined Commit 
function, and a opening (the polynomial in the KZG case) for the commitment 
(unlike the KZG's Commit function).
Hence the Commit function from KZG_Def is extended to also return the polynomial that is commited 
to.\<close>
definition SCC_Commit :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> ('a commit \<times> 'e polynomial) spmf"
where 
  "SCC_Commit PK \<phi> = do {
    return_spmf (g_pow_PK_Prod PK (of_qr \<phi>), \<phi>)
  }" 

lemma "spmf (VerifyPoly PK C \<phi>) True =  (if C = g_pow_PK_Prod PK (of_qr \<phi>) then 1 else 0)"
  unfolding VerifyPoly_def by simp

text \<open>3. the Verify function, that verifies that the commitment was actually made to the plain-text, 
using the opening, which in the KZG case is equivalent to the plain-text. Since the opening is 
cryptographic irrelevant (i.e. binding is evaluated on commitments to plain texts) and equivalent 
to the plain text, it does not hold relevant information and can be neglected.
The function is copied from KZG_Def with extended parameter, opening. 
Furthermore, it does not return a bool spmf, like in the KZG_Def, but a just a bool. The two 
are still equivalent though as the bool spmf is depended on C and \<phi> either {1} or {0} 
(for spmf _ True).
\<close>
definition SCC_verify :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> 'a commit \<Rightarrow> 'e polynomial \<Rightarrow> bool"
where 
  "SCC_verify PK \<phi> C _ \<equiv> (C = g_pow_PK_Prod PK (of_qr \<phi>))"

text \<open>4. the valid_msg function, that checks whether a provided plain text / polynomial is actually 
a valid/allowed message. For the KZG, a polynomial must be of degree less than or equal to the maximum 
degree max_deg. This however is already ensured by the type qr that is a quotient ring over 
polynomials for degree max_deg. Hence the valid_msg function is True\<close>
definition SCC_valid_msg :: "'e polynomial \<Rightarrow> bool"
where 
  "SCC_valid_msg _ \<equiv> True" 

subsection \<open>putting together the binding game\<close>
                                                        
sublocale bind_commit: abstract_commitment SCC_key_gen SCC_Commit SCC_verify SCC_valid_msg .

subsection \<open>t-SDH game\<close>

sublocale t_SDH_G\<^sub>p: t_SDH G\<^sub>p max_deg 
  unfolding t_SDH_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

text \<open>bind_commit.bind_game is the binding game we will reduce to the t-SDH assumption, thus showing 
that cracking the KZG's polynomial binding is at least as hard as solving the t-SDH problem. Hence 
proving the security of the KZG in groups where the t-SDH is difficult. \<close>

subsection \<open>Defining a reduction game to t-SDH\<close>

text \<open>Intuetively what we want to show is that if we have an adversary that can compute two 
polynomials such that they have the same commitment in polynomial time, we can construct an 
algorithm, using that adversary, that can solve the t-SDH in polynomial time, thus breaking the 
t-SDH assumption.\<close>


text \<open>This functions purpose is to extract \<alpha> based on the inputs g^\<alpha> and \<phi>, where \<phi> has a root at \<alpha>. 
The function factorizes \<phi> and filters for all roots. Since \<alpha>'s mod_ring is of the same cardinality 
as g's group's order, we can conclude that if g^r = g^\<alpha> then r=\<alpha>\<close>
fun find_\<alpha>_square_free :: "'a \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring" where
  "find_\<alpha>_square_free g_pow_\<alpha> \<phi> = (let (c, polys) = finite_field_factorization \<phi>;
    deg1_polys = filter (\<lambda>f. degree f = 1) polys;
    root_list = map (\<lambda>p. poly.coeff p 0) deg1_polys;
    \<alpha>_roots = filter (\<lambda>r. g_pow_\<alpha> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> r) root_list
in -\<alpha>_roots!0)"

(*TODO finite_field_factorization works only for square-free polys \<rightarrow> add step for non-sf to sf*)
fun find_\<alpha> :: "'a \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring" where
  "find_\<alpha> g_pow_\<alpha> \<phi> = find_\<alpha>_square_free g_pow_\<alpha> \<phi>"

text \<open>The reduction: 
An adversary for the KZG polynomial binding can output two polynomials \<phi> and \<phi>' that have the same 
commitment, i.e g^\<phi>(\<alpha>) = g^\<phi>(\<alpha>), which is equivalent to \<phi>(\<alpha>) = \<phi>'(\<alpha>) (same argument as in the 
function above). Hence (\<phi>-\<phi>')(\<alpha>) = 0, so (\<phi>-\<phi>') has a root at \<alpha>. Furthermore we have g^\<alpha> in the 
public key at position 1. Hence we can use the find_\<alpha>_square_free function to compute \<alpha> in 
polynomial time. Given \<alpha> we can easily compute a c and a g' such that g^(1/((\<alpha>+c))) = g'.
E.g. c=0 and g' = (1/\<alpha>)
Hence we can break the t-SDH assumption, as we have a polynomial-time algorithm to compute (c,g).
\<close>
fun bind_reduction
  :: "('a pk, 'e polynomial, 'a commit, 'e polynomial)  bind_adversary \<Rightarrow> 'a t_SDH.adversary"                     
where
  "bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' \<and> (g_pow_PK_Prod PK (of_qr \<phi>) = g_pow_PK_Prod PK (of_qr \<phi>'))); 
\<comment>\<open>TODO shouldn't it be \<and> Commit \<phi> = Commit \<phi>'? \<rightarrow> Lets try it\<close>
  let \<alpha> = find_\<alpha> (PK!1) (of_qr \<phi> - of_qr \<phi>');
  return_spmf (0::nat, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))}"
end


section \<open>proving the bind_game from Sigma_Commit_Crypto\<close>

locale bind_game_proof = bind_game_def
begin 

text \<open>The reduction game is actually easier than the KZG poly bind game. 
Hence we show the equivalence of the KZG poly bind game to a stronger bind_reduction game, which we 
show to be at least as hard as the real reduction game.\<close>

subsection\<open>reducing KZG poy bind game to stronger reduction game\<close>

text \<open>This function ensures additionally that the commitment C the poly bind Adversary made is 
actually the Commitment of \<phi> and \<phi>'\<close>
fun stronger_bind_reduction
  :: "('a pk, 'e polynomial, 'a commit, 'e polynomial)  bind_adversary \<Rightarrow> 'a t_SDH.adversary"                     
where
  "stronger_bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
  \<and> (C = g_pow_PK_Prod PK (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod PK (of_qr \<phi>')));
  let \<alpha> = find_\<alpha> (PK!1) (of_qr \<phi> - of_qr \<phi>');
  return_spmf (0::nat, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))}"

subsection \<open>Proof of equivalence between KZG poly bind and stronger bind_reduction\<close>

subsubsection \<open>helping lemmas\<close>

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

lemma commit_eq_is_poly_diff_\<alpha>_eq_0: "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (of_qr \<phi>) 
= g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (of_qr \<phi>')
  \<longleftrightarrow> poly (of_qr \<phi> - of_qr \<phi>') \<alpha> = 0"
proof 
  have deg_\<phi>: "degree (of_qr \<phi>) \<le> max_deg" using degree_of_qr by blast
  have deg_\<phi>': "degree (of_qr \<phi>') \<le> max_deg"  using degree_of_qr by blast
  assume commit_eq: "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (of_qr \<phi>) = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (of_qr \<phi>')"
  have acc_\<phi>: "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (of_qr \<phi>) =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha> )"
    by (metis g_pow_PK_Prod_correct deg_\<phi>)
  moreover have acc_\<phi>': "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (of_qr \<phi>') =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>') \<alpha> )"
    by (metis g_pow_PK_Prod_correct deg_\<phi>')
  ultimately show "(poly (of_qr \<phi> - of_qr \<phi>') \<alpha> = 0)"
    using pow_on_eq_card commit_eq by fastforce
next
  have deg_\<phi>: "degree (of_qr \<phi>) \<le> max_deg" using degree_of_qr by blast
  have deg_\<phi>': "degree (of_qr \<phi>') \<le> max_deg"  using degree_of_qr by blast
  assume poly_eq_0: "poly (of_qr \<phi> - of_qr \<phi>') \<alpha> = 0"
  have acc_\<phi>: "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (of_qr \<phi>) =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha> )"
    by (metis g_pow_PK_Prod_correct deg_\<phi>)
  moreover have acc_\<phi>': "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (of_qr \<phi>') =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>') \<alpha> )"
    by (metis g_pow_PK_Prod_correct deg_\<phi>')
  ultimately show "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (of_qr \<phi>) = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (of_qr \<phi>')" 
    using poly_eq_0 by fastforce 
qed


lemma helping_1_add_poly_\<phi>_m_\<phi>': "(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))) 
        = (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
        \<and> (poly (of_qr \<phi> - (of_qr \<phi>')) (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0))"
  using commit_eq_is_poly_diff_\<alpha>_eq_0 by fast

(*TODO*)
lemma sf_poly_eq0_is_find_\<alpha>_eq_\<alpha>: "\<phi> \<noteq> 0 \<Longrightarrow> square_free \<phi> \<Longrightarrow> 
  poly \<phi> \<alpha>=0 \<longleftrightarrow> find_\<alpha>_square_free (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>" 
  sorry

(*TODO goal \<Rightarrow> have to implement algorithm that produces square-free polys from non-square-free ones*)
lemma poly_eq0_is_find_\<alpha>_eq_\<alpha>: "\<phi> \<noteq> 0 \<Longrightarrow> poly \<phi> \<alpha> = 0 \<longleftrightarrow> find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>"
  sorry

lemma helping_2_factorize_\<alpha>: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
        \<and> (poly (of_qr \<phi> - (of_qr \<phi>')) (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0)
        \<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (of_qr \<phi> - of_qr \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))"
  by (metis poly_eq0_is_find_\<alpha>_eq_\<alpha> right_minus_eq to_qr_of_qr)

lemma helping_3_\<alpha>_is_found: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (of_qr \<phi> - of_qr \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring)) 
\<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (((of_int_mod_ring (int \<alpha>)::'e mod_ring)))) (of_qr \<phi> - of_qr \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1])!1) (of_qr \<phi> - of_qr \<phi>'))"
  (is "?lhs = ?rhs")
proof 
  assume ?lhs
  then show ?rhs
    (*TODO real? ? ?*)
    sorry
next 
  assume ?rhs
  then show ?lhs
    by linarith
qed

subsubsection \<open>KZG poly bind game to strong reduction game - reducing lemma\<close>

lemma poly_bind_game_eq_t_SDH_strong_red: 
  shows "bind_commit.bind_game \<A> = t_SDH_G\<^sub>p.game (stronger_bind_reduction \<A>)"
proof -
  note [simp] = Let_def split_def
  let ?\<alpha> = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>)^t)) [0..<max_deg+1])"
  
  have "bind_commit.bind_game \<A> = TRY do {
    (ck,vk) \<leftarrow> SCC_key_gen;
    (c, m, d, m', d') \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf(m \<noteq> m' \<and> SCC_valid_msg m \<and> SCC_valid_msg m'); 
    let b = SCC_verify vk m c d;
    let b' = SCC_verify vk m' c d';
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True} ELSE return_spmf False" 
    by (simp add: abstract_commitment.bind_game_alt_def) 
    also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1];
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>'); 
    _ :: unit \<leftarrow> assert_spmf ((C = g_pow_PK_Prod PK (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod PK (of_qr \<phi>')));
    return_spmf True} ELSE return_spmf False"
      unfolding SCC_key_gen_def SCC_verify_def by simp
    also have "\<dots> = TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
         _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>'); 
         _ :: unit \<leftarrow> assert_spmf ((C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>')));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>')));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"    
    using assert_anding by presburger 
  also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
        \<and> (poly (of_qr \<phi> - (of_qr \<phi>')) (?\<alpha> \<alpha>) = 0));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"    
    using helping_1_add_poly_\<phi>_m_\<phi>' by presburger
 also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>)));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"    
   using helping_2_factorize_\<alpha> by presburger
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False "
  using helping_3_\<alpha>_is_found by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>)));   
      _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    using assert_anding by presburger 
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
     _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>)));   
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
    return_spmf True } ELSE return_spmf False " 
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
        \<and> (poly (of_qr \<phi> - (of_qr \<phi>')) (?\<alpha> \<alpha>) = 0));    
  _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
    return_spmf True } ELSE return_spmf False"
    using helping_2_factorize_\<alpha> by presburger
   also have "\<dots>  = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
      \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>')));
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
    return_spmf True } ELSE return_spmf False "
     using helping_1_add_poly_\<phi>_m_\<phi>' by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (c, g) \<leftarrow>  do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
  \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>')));
  let \<alpha> = find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>');
  return_spmf (0::nat, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))};
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g);
    return_spmf True } ELSE return_spmf False"
    by fastforce
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (c, g) \<leftarrow> (stronger_bind_reduction \<A>) (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<max_deg+1]);
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g);
    return_spmf True } ELSE return_spmf False"
    unfolding stronger_bind_reduction.simps 
    using g_pow_to_int_mod_ring_of_int_mod_ring_pow_t by presburger
   also have "\<dots>= t_SDH_G\<^sub>p.game (stronger_bind_reduction \<A>)"
    using t_SDH_G\<^sub>p.game_alt_def[of "(stronger_bind_reduction \<A>)"] by argo
  finally show ?thesis .
qed

subsection \<open>advantage of stronger bind reduction less or equal to advantage of bind reduction\<close>

subsubsection \<open>helping lemmas\<close>

lemma helping_1_add_poly_\<phi>_m_\<phi>'_bindv: "(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>) = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))) 
        = (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>) = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
        \<and> (poly (of_qr \<phi> - (of_qr \<phi>')) (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0))"
  using commit_eq_is_poly_diff_\<alpha>_eq_0 by fast

lemma helping_2_factorize_\<alpha>_bindv: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)
           = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
        \<and> (poly (of_qr \<phi> - (of_qr \<phi>')) (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0)
        \<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>) 
           = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (of_qr \<phi> - of_qr \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))"
  by (metis poly_eq0_is_find_\<alpha>_eq_\<alpha> right_minus_eq to_qr_of_qr)

lemma helping_3_\<alpha>_is_found_bindv: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>) = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (of_qr \<phi> - of_qr \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring)) 
\<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>) = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (((of_int_mod_ring (int \<alpha>)::'e mod_ring)))) (of_qr \<phi> - of_qr \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1])!1) (of_qr \<phi> - of_qr \<phi>'))"
  (is "?lhs = ?rhs")
proof 
  assume ?lhs
  then show ?rhs
    (*TODO copy and adapt helping_3_\<alpha>_is_found*)
    sorry
next 
  assume ?rhs
  then show ?lhs
    by linarith
qed

lemma helping_4_g_powPK_eq: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)) 
            \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (of_qr \<phi> - of_qr \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))   
            \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1])!1) (of_qr \<phi> - of_qr \<phi>')) 
  \<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>)) 
            \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
            \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>) 
             = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) (of_qr \<phi>'))
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (of_qr \<phi> - of_qr \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))   
            \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1])!1) (of_qr \<phi> - of_qr \<phi>'))"
  by meson

subsubsection \<open>less equal reduction\<close>

text \<open>generalized lemmas\<close>

(*TODO rename*)
lemma help_lem: "spmf ((\<A>::'x spmf) \<bind> (\<lambda>x. assert_spmf ((f::'x \<Rightarrow> bool) x \<and> (q::'x \<Rightarrow> bool) x) \<bind> (\<lambda>_::unit. return_spmf True))) True 
  \<le> spmf ((\<A>::'x spmf) \<bind> (\<lambda>x. assert_spmf ((f::'x \<Rightarrow> bool) x) \<bind> (\<lambda>_::unit. return_spmf True))) True"
  (is "?lhs \<le> ?rhs")
proof -
  thm ennreal_spmf_bind
  have "?lhs = \<integral>\<^sup>+ x. ennreal (spmf (assert_spmf (f x \<and> q x) \<bind> (\<lambda>_::unit. return_spmf True)) True) \<partial>measure_spmf \<A>"
    by (rule ennreal_spmf_bind[of \<A> "(\<lambda>x. assert_spmf (f x \<and> q x) \<bind> (\<lambda>_::unit. return_spmf True))"])
  also have "\<dots> \<le> \<integral>\<^sup>+ x. ennreal (spmf (assert_spmf (f x) \<bind> (\<lambda>_::unit. return_spmf True)) True) \<partial>measure_spmf \<A>"
    by (rule nn_integral_mono_AE)
   (*TODO replace smt-proof with full proof*)    
   (smt (verit, best) AE_measure_spmf_iff assert_spmf_simps(1) bernoulli_pmf.rep_eq bernoulli_pmf_1 dual_order.eq_iff ennreal_1 ennreal_le_1 pmf_le_1 return_bind_spmf spmf_of_pmf_return_pmf spmf_spmf_of_pmf)
  also have "\<dots>=?rhs"
    using ennreal_spmf_bind[of \<A> "(\<lambda>x. assert_spmf (f x) \<bind> (\<lambda>_::unit. return_spmf True))"] ..
  finally show ?thesis by simp    
qed

lemma spmf_reduction:
"spmf (do {
    \<alpha>::nat \<leftarrow> sample_uniform (order G\<^sub>p);
    x::'x \<leftarrow> (\<A>::nat \<Rightarrow> 'x spmf) \<alpha>;
    _ :: unit \<leftarrow> assert_spmf((f::'x \<Rightarrow> bool) x \<and> (q::'x \<Rightarrow> bool) x);
    return_spmf True }) True 
  \<le> spmf (do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    x::'x \<leftarrow> \<A> \<alpha>;
    _ :: unit \<leftarrow> assert_spmf(f x);
    return_spmf True }) True"
  (is "?lhs \<le> ?rhs")
proof -
  have "?lhs =
  \<integral>\<^sup>+ x. ennreal (spmf (\<A> x \<bind> (\<lambda>x. assert_spmf (f x \<and> q x) \<bind> (\<lambda>_::unit. return_spmf True))) True)
     \<partial>measure_spmf (sample_uniform (Coset.order G\<^sub>p))"
    by (rule ennreal_spmf_bind[of "sample_uniform (Coset.order G\<^sub>p)" "(\<lambda>\<alpha>. \<A> \<alpha> \<bind> (\<lambda>x. assert_spmf (f x \<and> q x) \<bind> (\<lambda>_::unit. return_spmf True)))"])
  also have "\<dots> \<le>  \<integral>\<^sup>+ x. ennreal (spmf (\<A> x \<bind> (\<lambda>x. assert_spmf (f x) \<bind> (\<lambda>_::unit. return_spmf True))) True)
     \<partial>measure_spmf (sample_uniform (Coset.order G\<^sub>p))"
    by (rule nn_integral_mono_AE)(simp add: help_lem)
  also have "\<dots>=?rhs" 
   using ennreal_spmf_bind[of "sample_uniform (Coset.order G\<^sub>p)" "(\<lambda>\<alpha>. \<A> \<alpha> \<bind> (\<lambda>x. assert_spmf (f x) \<bind> (\<lambda>_::unit. return_spmf True)))"]
   ..
  finally show ?thesis by fastforce
qed

lemma spmf_reduction_TRY_ret_spmf_False_ext: 
  assumes "spmf A True \<le> spmf C True"
shows "spmf (TRY A ELSE return_spmf False) True \<le> spmf (TRY C ELSE return_spmf False) True"
  (is "?lhs\<le>?rhs")
proof -
  have "?lhs = spmf A True + pmf A None * spmf (return_spmf False) True"
    by (rule spmf_try_spmf[of A "return_spmf False" True])
  also have "\<dots> \<le> spmf C True + pmf C None * spmf (return_spmf False) True"
    using assms by force
  also have "\<dots> = spmf (TRY C ELSE return_spmf False) True"
    using spmf_try_spmf[of C "return_spmf False" True] ..
  finally show ?thesis .
qed

corollary spmf_reduction_TRY_version:
"spmf (TRY do {
    \<alpha>::nat \<leftarrow> sample_uniform (order G\<^sub>p);
    x::'x \<leftarrow> (\<A>::nat \<Rightarrow> 'x spmf) \<alpha>;
    _ :: unit \<leftarrow> assert_spmf((f::'x \<Rightarrow> bool) x \<and> (q::'x \<Rightarrow> bool) x);
    return_spmf True } ELSE return_spmf False) True 
  \<le> spmf (TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    x::'x \<leftarrow> \<A> \<alpha>;
    _ :: unit \<leftarrow> assert_spmf(f x);
    return_spmf True } ELSE return_spmf False) True"
  (is "?lhs \<le> ?rhs")
  apply (rule spmf_reduction_TRY_ret_spmf_False_ext)
  apply (rule spmf_reduction)
  done

lemma spmf_reduction_ext:
"spmf (do {
    \<alpha>::nat \<leftarrow> sample_uniform (order G\<^sub>p);
    x::'x \<leftarrow> (\<A>::nat \<Rightarrow> 'x spmf) \<alpha>;
    _ :: unit \<leftarrow> assert_spmf((f::'x \<Rightarrow> nat \<Rightarrow> bool) x \<alpha> \<and> (q::'x \<Rightarrow> nat \<Rightarrow> bool) x \<alpha>);
    return_spmf True }) True 
  \<le> spmf (do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    x::'x \<leftarrow> \<A> \<alpha>;
    _ :: unit \<leftarrow> assert_spmf(f x \<alpha>);
    return_spmf True }) True"
  sorry

text \<open>Actual reduction lemma\<close>

lemma t_SDH_advantage_stronger_red_le_red: "t_SDH_G\<^sub>p.advantage (stronger_bind_reduction \<A>) \<le> t_SDH_G\<^sub>p.advantage (bind_reduction \<A>)"
proof -
  let ?sr_game = "t_SDH_G\<^sub>p.game (stronger_bind_reduction \<A>)"
  let ?r_game = "t_SDH_G\<^sub>p.game (bind_reduction \<A>)"
  let ?\<alpha> = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>)^t)) [0..<max_deg+1])"
  note [simp] = Let_def split_def

  text \<open>same proof technique as in the stronger_bind_equivalence. But instead of showing equivalence 
  we use the spmf_reduction lemma to show less or equal\<close>

  text \<open>part 1 bring ?sr_game into a a the form required for the spmf_reduction lemma.\<close>
  have "?sr_game = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
      \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>')));
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
    return_spmf True } ELSE return_spmf False"
    apply (simp add: t_SDH_G\<^sub>p.game_alt_def[of "(stronger_bind_reduction \<A>)"])
    apply (simp add: g_pow_to_int_mod_ring_of_int_mod_ring_pow_t)
    done
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
     _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>)));   
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
    return_spmf True } ELSE return_spmf False "
    using helping_1_add_poly_\<phi>_m_\<phi>' helping_2_factorize_\<alpha> by presburger
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>)));   
      _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    using assert_anding by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False"
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False"
    using helping_4_g_powPK_eq by algebra
  finally have sbr_game_ref: "t_SDH_G\<^sub>p.advantage (stronger_bind_reduction \<A>) = spmf (
    TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False
    ) True"
    unfolding t_SDH_G\<^sub>p.advantage_def by presburger

  text \<open>part 2 bring ?r_game into the form required for the spmf_reduction lemma.\<close>
  

   have "?r_game = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
      \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)= g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>')));
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
    return_spmf True } ELSE return_spmf False"
    apply(simp add: t_SDH_G\<^sub>p.game_alt_def[of "(bind_reduction \<A>)"])
    apply (simp add: g_pow_to_int_mod_ring_of_int_mod_ring_pow_t)
    done
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
     _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>)));   
    _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
    return_spmf True } ELSE return_spmf False "
    using helping_1_add_poly_\<phi>_m_\<phi>'_bindv helping_2_factorize_\<alpha>_bindv by presburger
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>)));   
      _::unit \<leftarrow> assert_spmf (\<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    using assert_anding by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
      return_spmf True } ELSE return_spmf False"
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  finally have br_game_ref: "t_SDH_G\<^sub>p.advantage (bind_reduction \<A>) = spmf (
    TRY do { 
      \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
      (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
         _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
            \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
        return_spmf True } ELSE return_spmf False
    ) True"
    unfolding t_SDH_G\<^sub>p.advantage_def by presburger

    text \<open>part 3 apply the spmf_reduction lemma to the results of part 1 & 2. Hence show 
  less equal..\<close>  
    
    show ?thesis
    proof -
      note [simp] = Let_def split_def
      let ?f_n_q = "\<lambda>(C, \<phi>, \<phi>') . \<lambda>\<alpha>. \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
            \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
            \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>'))"
      let ?f = "\<lambda>(C, \<phi>, \<phi>') . \<lambda>\<alpha>. \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>'
            \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
            \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>'))"
      let ?q = "\<lambda>(C, \<phi>, \<phi>') . \<lambda>\<alpha>. 
          (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))"
      have f_n_q_conv : "\<forall>C \<phi> \<phi>' \<alpha>. ?f_n_q (C,\<phi>,\<phi>') \<alpha> \<longleftrightarrow> ?f (C,\<phi>,\<phi>') \<alpha> \<and> ?q (C,\<phi>, \<phi>') \<alpha>"
      proof (intro allI)
        fix C::'a
        fix \<phi> \<phi>':: "'e qr"
        fix \<alpha> :: nat
        show "?f_n_q (C,\<phi>,\<phi>') \<alpha> \<longleftrightarrow> ?f (C,\<phi>,\<phi>') \<alpha> \<and> ?q (C,\<phi>, \<phi>') \<alpha>"
        proof 
          assume "?f_n_q (C,\<phi>,\<phi>') \<alpha>"
          then show "?f (C,\<phi>,\<phi>') \<alpha> \<and> ?q (C,\<phi>, \<phi>') \<alpha>"
            by fast
        next
          assume "?f (C,\<phi>,\<phi>') \<alpha> \<and> ?q (C,\<phi>, \<phi>') \<alpha>"
          then show "?f_n_q (C,\<phi>,\<phi>') \<alpha>"
            by fast
        qed
      qed

      have "t_SDH_G\<^sub>p.advantage (stronger_bind_reduction \<A>) = spmf (
       TRY do { 
       \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
       (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);      
         _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>)) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
            \<and> (g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>) = g_pow_PK_Prod (?PK \<alpha>) (of_qr \<phi>'))
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (of_qr \<phi> - of_qr \<phi>') = (?\<alpha> \<alpha>))   
            \<and> \<^bold>g [^] (1/\<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (of_qr \<phi> - of_qr \<phi>')));
       return_spmf True } ELSE return_spmf False
      ) True"
        by (rule sbr_game_ref)
      also have "\<dots>= spmf (
       TRY do { 
       \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
       (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);      
         _ :: unit \<leftarrow> assert_spmf (?f_n_q (C, \<phi>, \<phi>') \<alpha>);
       return_spmf True } ELSE return_spmf False
      ) True"
        by fast
     also have "\<dots> = spmf (
       TRY do { 
       \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
       (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);      
         _ :: unit \<leftarrow> assert_spmf (?f (C, \<phi>, \<phi>') \<alpha> \<and> ?q (C, \<phi>, \<phi>') \<alpha>);
       return_spmf True } ELSE return_spmf False
      ) True"
       using f_n_q_conv by presburger
      also have "\<dots> \<le> spmf (
       TRY do { 
       \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
       (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);      
         _ :: unit \<leftarrow> assert_spmf (?f (C, \<phi>, \<phi>') \<alpha>);
       return_spmf True } ELSE return_spmf False
      ) True"
        apply (rule spmf_reduction_TRY_ret_spmf_False_ext)
        using spmf_reduction_ext[of "\<lambda>\<alpha>. \<A> (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0..<max_deg + 1])"
             "\<lambda>(C, \<phi>, _, \<phi>', _). ?f (C,\<phi>,\<phi>')" "\<lambda>(C, \<phi>, _, \<phi>', _). ?q (C,\<phi>,\<phi>')"]
        by simp
      also have "\<dots> =  t_SDH_G\<^sub>p.advantage (bind_reduction \<A>)"
        using br_game_ref[symmetric] by fast
      finally show ?thesis .
    qed
  qed

theorem polynomial_binding: "bind_commit.bind_advantage \<A> \<le> t_SDH_G\<^sub>p.advantage (bind_reduction \<A>)"
  unfolding bind_commit.bind_advantage_def 
  proof (subst poly_bind_game_eq_t_SDH_strong_red)
    show "spmf (t_SDH_G\<^sub>p.game (stronger_bind_reduction \<A>)) True 
       \<le> t_SDH_G\<^sub>p.advantage (bind_reduction \<A>)" 
      using t_SDH_advantage_stronger_red_le_red 
      unfolding t_SDH_G\<^sub>p.advantage_def .
  qed

end


end
theory KZG_poly_bind

imports KZG_correct "Sigma_Commit_Crypto.Commitment_Schemes" "tSDH_assumption"
 "Berlekamp_Zassenhaus.Finite_Field_Factorization" "ERF_Squarefree"

begin

section \<open>polynomial binding\<close>
text \<open>We show that the KZG is polynomial binding for every polynomial of degree <= max_deg.
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
    (_::'e sk, PK::'a pk) \<leftarrow> Setup;
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
    return_spmf (Commit PK \<phi>, \<phi>)
  }" 

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
  "SCC_verify PK \<phi> C _ \<equiv> VerifyPoly PK C \<phi>"

text \<open>4. the valid_msg function, that checks whether a provided plain text / polynomial is actually 
a valid/allowed message. For the KZG, a polynomial must be of degree less than or equal to the maximum 
degree max_deg. This however is already ensured by the type qr that is a quotient ring over 
polynomials for degree max_deg. Hence the valid_msg function is True\<close>
definition SCC_valid_msg :: "'e polynomial \<Rightarrow> bool"
where 
  "SCC_valid_msg \<phi> \<equiv> degree \<phi> \<le> max_deg" 

subsection \<open>putting together the binding game\<close>
                                                        
sublocale bind_commit: abstract_commitment SCC_key_gen SCC_Commit SCC_verify SCC_valid_msg .

subsection \<open>t-SDH game\<close>


sublocale t_SDH_G\<^sub>p: t_SDH G\<^sub>p max_deg "of_int_mod_ring \<circ> int" pow_mod_ring_G\<^sub>p
  unfolding t_SDH_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

text \<open>bind_commit.bind_game is the binding game we will reduce to the t-SDH assumption, thus showing 
that cracking the KZG's polynomial binding is at least as hard as solving the t-SDH problem. Hence 
proving the security of the KZG for groups where the t-SDH is difficult.\<close>

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
    \<alpha>_roots = filter (\<lambda>r. g_pow_\<alpha> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> -r) root_list
in -\<alpha>_roots!0)"

(*TODO finite_field_factorization works only for square-free polys \<rightarrow> add step for non-sf to sf*)
fun find_\<alpha> :: "'a \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring" where
  "find_\<alpha> g_pow_\<alpha> \<phi> = find_\<alpha>_square_free g_pow_\<alpha> (ERF \<phi>)"

text \<open>The reduction: 
An adversary for the KZG polynomial binding can output two polynomials \<phi> and \<phi>' that have the same 
commitment, i.e g^\<phi>(\<alpha>) = g^\<phi>(\<alpha>), which is equivalent to \<phi>(\<alpha>) = \<phi>'(\<alpha>) (same argument as in the 
function above). Hence (\<phi>-\<phi>')(\<alpha>) = 0, so (\<phi>-\<phi>') has a root at \<alpha>. Furthermore we have g^\<alpha> in the 
public key at position 1. Hence we can use the find_\<alpha> function to compute \<alpha> in 
polynomial time. Given \<alpha> we can easily compute a c and a g' such that g^(1/((\<alpha>+c))) = g'.
E.g. c=0 and g' = g^(1/\<alpha>)
Hence we can break the t-SDH assumption, as we have a polynomial-time algorithm to compute (c,g).
\<close>
fun bind_reduction
  :: "('a pk, 'e polynomial, 'a commit, 'e polynomial)  bind_adversary \<Rightarrow> ('a,'e) t_SDH.adversary"                     
where
  "bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' 
                  \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
                  \<and> (g_pow_PK_Prod PK \<phi> = g_pow_PK_Prod PK \<phi>')); 
  \<comment>\<open>\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' \<and> Commit \<phi> = Commit \<phi>'\<close>
  let \<alpha> = find_\<alpha> (PK!1) (\<phi> - \<phi>');
  return_spmf (0::'e mod_ring, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))}"
end


section \<open>proving the bind_game from Sigma_Commit_Crypto\<close>

locale bind_game_proof = bind_game_def
begin 

text \<open>The reduction game is actually easier than the KZG poly bind game. 
Hence we show the equivalence of the KZG poly bind game to a stronger bind_reduction game, which we 
show to be at least as hard as the real reduction game.\<close>

subsection\<open>reducing KZG poy bind game to stronger reduction game\<close>

text \<open>This function ensures additionally that the commitment C the poly bind Adversary made is 
actually the Commitment of \<phi> and \<phi>' (so not only that the Commit of \<phi> equals the Commit of \<phi>', but 
also the Commitment C that was outputed.)\<close>
fun stronger_bind_reduction
  :: "('a pk, 'e polynomial, 'a commit, 'e polynomial)  bind_adversary \<Rightarrow> ('a,'e) t_SDH.adversary"                     
where
  "stronger_bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
  \<and> (C = g_pow_PK_Prod PK \<phi>) \<and> (C = g_pow_PK_Prod PK \<phi>'));
  let \<alpha> = find_\<alpha> (PK!1) (\<phi> - \<phi>');
  return_spmf (0::'e mod_ring, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))}"

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

text \<open>g^\<phi>(\<alpha>)=g^\<phi>'(\<alpha>) is equivalent to (\<phi>-\<phi>')(\<alpha>)=0\<close>
lemma commit_eq_is_poly_diff_\<alpha>_eq_0: 
  assumes "degree \<phi> \<le> max_deg" "degree \<phi>' \<le> max_deg"
  shows "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) \<phi>
= g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) \<phi>'
  \<longleftrightarrow> poly (\<phi> - \<phi>') \<alpha> = 0"
proof 
  assume commit_eq: 
    "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) \<phi> 
   = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) \<phi>'"
  have acc_\<phi>: "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) \<phi> 
              =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi> \<alpha> )"
    by (metis g_pow_PK_Prod_correct assms(1))
  moreover have acc_\<phi>': 
    "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) \<phi>' 
    =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi>' \<alpha> )"
    by (metis g_pow_PK_Prod_correct assms(2))
  ultimately show "(poly (\<phi> - \<phi>') \<alpha> = 0)"
    using pow_on_eq_card commit_eq by fastforce
next
  assume poly_eq_0: "poly (\<phi> - \<phi>') \<alpha> = 0"
  have acc_\<phi>: "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) \<phi> 
            =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi> \<alpha> )"
    by (metis g_pow_PK_Prod_correct assms(1))
  moreover have acc_\<phi>': 
    "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) \<phi>' 
    =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi>' \<alpha> )"
    by (metis g_pow_PK_Prod_correct assms(2))
  ultimately show "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) \<phi> 
                 = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) \<phi>'" 
    using poly_eq_0 by fastforce 
qed


text \<open>TODO document\<close>
lemma finite_field_factorization_roots:
fixes \<phi>::"'e mod_ring poly"
  assumes sf_f: "square_free \<phi>"
    and us: "finite_field_factorization \<phi> = (c,us)"
  shows "poly \<phi> \<alpha> = 0 \<longleftrightarrow> c=0 \<or> (\<exists>u\<in>set us. poly u \<alpha> = 0)"
proof 
  assume asm: "poly \<phi> \<alpha> = 0"
  have smult: "\<phi> = Polynomial.smult c (prod_list us)"
    using finite_field_factorization_explicit[OF assms] ..
  then show "c = 0 \<or> (\<exists>u\<in>set us. poly u \<alpha> = 0)"
  proof (cases "c=0")
    case True
    then show ?thesis ..
  next
    case False
    then show ?thesis
      using asm
      by (simp add: poly_prod_list_zero_iff smult)
  qed
next 
  assume asm: "c = 0 \<or> (\<exists>u\<in>set us. poly u \<alpha> = 0)"
  have smult: "\<phi> = Polynomial.smult c (prod_list us)"
    using finite_field_factorization_explicit[OF assms] ..
  show "poly \<phi> \<alpha> = 0"
  proof (cases "c=0")
    case True
    then show ?thesis using smult by force
  next
    case False
    then have "(\<exists>u\<in>set us. poly u \<alpha> = 0)" using asm by blast 
    then show ?thesis
      using smult poly_prod_list_zero_iff poly_smult_zero_iff by blast
  qed
qed

lemma root_imp_deg_1:
  assumes "monic (u::'e mod_ring poly) \<and> irreducible u"
  shows "(\<exists>x. poly u x = 0) \<longleftrightarrow> degree u = 1"
proof 
  assume asm: "\<exists>x. poly u x = 0"
  show "degree u = 1"
  proof (rule ccontr)
    assume deg_ne_1: "degree u \<noteq> 1"
    obtain c where c: "poly u c = 0" using asm by blast
    with synthetic_div_correct' [of c u] have split_u: "u = [:-c, 1:] * synthetic_div u c" by simp
    from c deg_ne_1 have deg_u_pos: "degree u \<ge> 2"
      by (metis One_nat_def assms leading_coeff_0_iff less_2_cases not_le poly_zero rel_simps(93))
    then have "degree (synthetic_div u c) \<ge> 1" using degree_synthetic_div[of u c] by linarith  
    then have "\<not>(synthetic_div u c) dvd 1" by auto
    moreover have "\<not>[:-c, 1:] dvd 1" by auto
    ultimately show "False"
      using irreducible_def[of u] split_u assms by blast  
  qed
next
  assume asm: "degree u = 1"  
  have poly_deg_1: "\<forall>x. poly u x = poly.coeff u 0 + x"
  proof 
    fix x 
    have "poly u x = (\<Sum>i\<le>degree u. poly.coeff u i * x ^ i)"
      using poly_altdef by fast
    also have "\<dots> = poly.coeff u 0 + poly.coeff u 1 * x"
      using asm by force
    also have "\<dots> = poly.coeff u 0 + x"
    proof -
      have "poly.coeff u 1 = 1"
        using asm assms by force
      then show ?thesis  by fastforce
    qed
    finally show "poly u x = poly.coeff u 0 + x" .
  qed    
  show "\<exists>x. poly u x = 0"
  proof
    show "poly u (-poly.coeff u 0) = 0"
      using poly_deg_1 by fastforce
  qed
qed


lemma poly_eq0_is_find_\<alpha>_sf_eq_\<alpha>: 
  assumes "\<phi> \<noteq> 0 \<and> square_free \<phi>" 
  shows "poly \<phi> \<alpha> = 0 \<Longrightarrow> find_\<alpha>_square_free (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>"
proof -
  assume asm: "poly \<phi> \<alpha> = 0"
  obtain c polys where c_polys: "(c, polys) = finite_field_factorization \<phi>"
    by (metis prod.exhaust)
  then have "c\<noteq>0" using assms
    by (metis finite_field_factorization_explicit smult_0_left)
  then have "\<exists>u \<in> set polys. poly u \<alpha> = 0" using c_polys asm
    by (metis assms finite_field_factorization_roots)
  then obtain u where u: "u \<in> set polys \<and> poly u \<alpha> = 0" by blast
  then have "degree u = 1" using root_imp_deg_1 
    by (metis (mono_tags, lifting) assms c_polys finite_field_factorization_explicit)
  moreover have "monic u" using u c_polys
    by (metis assms finite_field_factorization_explicit)
  ultimately have u_coeff0: "poly.coeff u 0 = -\<alpha>" using u
    (*TODO better proof*)
    by (metis (no_types, lifting) One_nat_def add_0_right coeff_pCons_0 coeff_pCons_Suc degree1_coeffs degree_1 mpoly_base_conv(2) mult_cancel_left1 one_pCons pCons_0_hom.hom_zero synthetic_div_correct' synthetic_div_eq_0_iff synthetic_div_pCons)
  then show "find_\<alpha>_square_free (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>"
  proof -
    have "find_\<alpha>_square_free (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> 
    = (- (filter (\<lambda>r. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> -r) (map (\<lambda>p. poly.coeff p 0) (filter (\<lambda>f. degree f = 1) (snd (finite_field_factorization \<phi>))))) ! 0)"
      unfolding find_\<alpha>_square_free.simps by (simp add: split_def)
    also have "\<dots> = (- (filter (\<lambda>r. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> -r) (map (\<lambda>p. poly.coeff p 0) (filter (\<lambda>f. degree f = 1) (polys)))) ! 0)"
      using c_polys by (smt (verit, best) snd_conv)
    also have "\<dots> = \<alpha>"
    proof -
      have "u \<in> set (filter (\<lambda>f. degree f = 1) polys)"
        by (simp add: \<open>degree u = 1\<close> u)
      then have "-\<alpha> \<in> set (map (\<lambda>p. poly.coeff p 0) (filter (\<lambda>f. degree f = 1) polys))"
        using u_coeff0 \<open>degree u = 1\<close> by force
      then have "-\<alpha> \<in> set (filter (\<lambda>r. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> - r) (map (\<lambda>p. poly.coeff p 0) (filter (\<lambda>f. degree f = 1) polys)))"
        by fastforce
      moreover have "\<forall>xs. -\<alpha> \<in> set xs \<longrightarrow> set (filter (\<lambda>r. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> - r) xs) = {-\<alpha>}"
        by (auto simp: pow_on_eq_card)
      ultimately have "set (filter (\<lambda>r. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> - r) (map (\<lambda>p. poly.coeff p 0) (filter (\<lambda>f. degree f = 1) polys))) = {-\<alpha>}"
        by fastforce
      then have "filter (\<lambda>r. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> - r) (map (\<lambda>p. poly.coeff p 0) (filter (\<lambda>f. degree f = 1) polys)) ! 0 = -\<alpha>"
        by (metis length_pos_if_in_set nth_mem singleton_iff)
      then show ?thesis by force
      qed
    finally show ?thesis . 
  qed
qed

(*TODO goal \<Rightarrow> have to implement algorithm that produces square-free polys from non-square-free ones*)
text \<open>show find_\<alpha> correctly finds(factorizes) \<alpha>, if \<alpha> is a root and \<phi> is not a zero-polynomial.\<close>
lemma poly_eq0_imp_find_\<alpha>_eq_\<alpha>: "\<phi> \<noteq> 0 \<Longrightarrow> poly \<phi> \<alpha> = 0 \<Longrightarrow> find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>"
proof -
  assume \<phi>_ne_0: "\<phi> \<noteq> 0"
  assume \<alpha>_root: "poly \<phi> \<alpha> = 0"
  have "(ERF \<phi>) \<noteq> 0"
    using f_ne_0_imp_ERF_ne_0[OF \<phi>_ne_0] .
  moreover have "poly (ERF \<phi>) \<alpha> = 0" 
    using \<alpha>_root same_zeros_in_square_free_part by blast
  moreover have "square_free (ERF \<phi>)" using square_free_ERF[OF \<phi>_ne_0] by simp
  ultimately show "find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>"
    unfolding find_\<alpha>.simps using poly_eq0_is_find_\<alpha>_sf_eq_\<alpha> by blast
qed

subsubsection \<open>literal helping lemmas\<close>

text \<open>From here on we define literal helping lemmas, with name-pattern: helping_*number*_*content-reference*. 
These lemmas are literal logic blocks that are used in the actual equivalence proof. 
They all capture one step in the transition (from poly_bind game to t-SDH reduction game logic), that is either 
too complicated for Isabelle to prove in the monadic/game-based form or requires some additional proving steps 
that would complicate the equivalence proof.
Basically extracted logical reasoning.\<close>

text \<open>The logical addition of (\<phi>-\<phi>')(\<alpha>)=0, which is implied by \<phi>(\<alpha>)=\<phi>'(\<alpha>), which we derive from C=g^\<phi>(\<alpha>) \<and> C=g^\<phi>'(\<alpha>)\<close>
lemma helping_1_add_poly_\<phi>_m_\<phi>': "(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')) 
        = (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (poly (\<phi> - (\<phi>')) (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0))"
  unfolding SCC_valid_msg_def 
  using commit_eq_is_poly_diff_\<alpha>_eq_0 by fast

text\<open>\<close>
lemma helping_2_factorize_\<alpha>: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (poly (\<phi> - \<phi>') (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0)
        \<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs using poly_eq0_imp_find_\<alpha>_eq_\<alpha>
    by (metis right_minus_eq to_qr_of_qr)
next 
  assume ?rhs
  then show ?lhs 
    unfolding SCC_valid_msg_def
    using commit_eq_is_poly_diff_\<alpha>_eq_0 by fast
qed
                                
text \<open>\<close>
lemma helping_3_\<alpha>_is_found: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring)) 
\<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (((of_int_mod_ring (int \<alpha>)::'e mod_ring)))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))   
          \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/of_int_mod_ring (int \<alpha>)) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1])!1) (\<phi> - \<phi>'))"
  (is "?lhs = ?rhs")
proof 
  assume asm:?lhs
  moreover have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/of_int_mod_ring (int \<alpha>)) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1 / find_\<alpha> (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0..<max_deg + 1] ! 1) (\<phi> - \<phi>'))"
  proof -
    have "map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0::nat..<max_deg + (1::nat)] ! (1::nat) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>)"
      using PK_i d_pos by force
    then show ?thesis using asm by argo
  qed
  ultimately show ?rhs by linarith
next 
  assume ?rhs
  then show ?lhs by linarith
qed

subsubsection \<open>KZG poly bind game to strong reduction game - equivalence theorem\<close>

text \<open>showing the equivalence of the KZG poly bind game to the stronger bind_reduction game, which we 
show to be at least as hard as the real reduction game in the next subsection.\<close>

theorem poly_bind_game_eq_t_SDH_strong_red: 
  shows "bind_commit.bind_game \<A> = t_SDH_G\<^sub>p.game (stronger_bind_reduction \<A>)"
proof -
  note [simp] = Let_def split_def

  text \<open>abbreviations for the mod_ring version of sample uniform nat 
  and the public key\<close>
  let ?\<alpha> = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>)^t)) [0..<max_deg+1])"

  text \<open>We start with the poly bind game and perform logical 
  transitions until we obtain the t-SDH game with the (stronger-)reduction\<close>
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
    _ :: unit \<leftarrow> assert_spmf ((C = g_pow_PK_Prod PK \<phi>) \<and> (C = g_pow_PK_Prod PK \<phi>'));
    return_spmf True} ELSE return_spmf False"
      unfolding SCC_key_gen_def SCC_verify_def VerifyPoly_def Setup_def by simp
    also have "\<dots> = TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
         _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>'); 
         _ :: unit \<leftarrow> assert_spmf ((C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
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
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
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
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (poly (\<phi> - \<phi>') (?\<alpha> \<alpha>) = 0));
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
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));
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
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
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
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));   
      _::unit \<leftarrow> assert_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    using assert_anding by presburger 
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
     _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));   
    _::unit \<leftarrow> assert_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
    return_spmf True } ELSE return_spmf False " 
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (poly (\<phi> - \<phi>') (?\<alpha> \<alpha>) = 0));    
  _::unit \<leftarrow> assert_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
    return_spmf True } ELSE return_spmf False"
    using helping_2_factorize_\<alpha> by presburger
   also have "\<dots>  = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
      \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
    _::unit \<leftarrow> assert_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
    return_spmf True } ELSE return_spmf False "
     using helping_1_add_poly_\<phi>_m_\<phi>' by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (c, g) \<leftarrow>  do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
  \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
  let \<alpha> = find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>');
  return_spmf (0::'e mod_ring, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))};
    _::unit \<leftarrow> assert_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/((?\<alpha> \<alpha>)+c)) = g);
    return_spmf True } ELSE return_spmf False"
    by fastforce
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (c, g) \<leftarrow> (stronger_bind_reduction \<A>) (?PK \<alpha>);
    _::unit \<leftarrow> assert_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/((?\<alpha> \<alpha>)+c)) = g);
    return_spmf True } ELSE return_spmf False"
    unfolding stronger_bind_reduction.simps 
    using g_pow_to_int_mod_ring_of_int_mod_ring_pow_t by presburger
   also have "\<dots>= t_SDH_G\<^sub>p.game (stronger_bind_reduction \<A>)"
    using t_SDH_G\<^sub>p.game_alt_def[of "(stronger_bind_reduction \<A>)"] by simp
  finally show ?thesis .
qed

subsection \<open>advantage of stronger bind reduction less or equal to advantage of bind reduction\<close>

text \<open>showing the stronger bind_reduction game to be at least as hard as the real reduction game.\<close>

subsubsection \<open>literal helping lemmas\<close>

text \<open>Similar to the equivalence proof, we define literal helping lemmas, 
with name-pattern: helping_*number*_*content-reference*. 
These lemmas are literal logic blocks that are used in the actual reduction proof. 
They all capture one step in the transition (from stronger-reduction to reduction logic), that is either 
too complicated for Isabelle to prove in the monadic/game-based form or requires some additional proving steps 
that would complicate the equivalence proof.
Basically extracted logical reasoning.\<close>

lemma helping_1_add_poly_\<phi>_m_\<phi>'_bindv: "(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi> 
         = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')) 
        = (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi> 
         = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (poly (\<phi> - \<phi>') (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0))"
  unfolding SCC_valid_msg_def
  using commit_eq_is_poly_diff_\<alpha>_eq_0 
  by blast

lemma helping_2_factorize_\<alpha>_bindv: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>
           = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (poly (\<phi> - \<phi>') (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0)
        \<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi> 
           = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs using poly_eq0_imp_find_\<alpha>_eq_\<alpha>
    by (metis right_minus_eq to_qr_of_qr)
next 
  assume ?rhs
  then show ?lhs 
    unfolding SCC_valid_msg_def
    using commit_eq_is_poly_diff_\<alpha>_eq_0 by fast
qed

lemma helping_3_g_powPK_eq: "\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
            \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))   
            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(of_int_mod_ring (int \<alpha>)::'e mod_ring)) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1])!1) (\<phi> - \<phi>')) 
  \<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
            \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
            \<and> (g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi> 
             = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))   
            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/(of_int_mod_ring (int \<alpha>)::'e mod_ring)) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1])!1) (\<phi> - \<phi>'))"
  by meson

subsubsection \<open>generalized less equal reduction\<close>

text \<open>We build a generalized less equal lemma that captures the general structure of the actual 
reduction lemma. We start with a more simple lemma and built upon it.\<close>

text \<open>This is the simple lemma we build the more complex generalized version upon.
It basically expresses, that given an arbitrary spmf instance x, assert(f x \<and> q x) \<le> assert(f x).\<close>
lemma simple_le_on_assert: "spmf ((\<A>::'x spmf) \<bind> (\<lambda>x. assert_spmf ((f::'x \<Rightarrow> bool) x \<and> (q::'x \<Rightarrow> bool) x) \<bind> (\<lambda>_::unit. return_spmf True))) True 
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

text \<open>Upon the simple less equal lemma we introduce the sample uniform construct, which we use as a
parameter for the spmf instance x.\<close>
lemma spmf_reduction:
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
  (is "?lhs \<le> ?rhs")
proof -
  have "?lhs =
  \<integral>\<^sup>+ \<alpha>. ennreal (spmf (\<A> \<alpha> \<bind> (\<lambda>x. assert_spmf (f x \<alpha> \<and> q x \<alpha>) \<bind> (\<lambda>_::unit. return_spmf True))) True)
     \<partial>measure_spmf (sample_uniform (Coset.order G\<^sub>p))"
    by (rule ennreal_spmf_bind[of "sample_uniform (Coset.order G\<^sub>p)" "(\<lambda>\<alpha>. \<A> \<alpha> \<bind> (\<lambda>x. assert_spmf (f x \<alpha> \<and> q x \<alpha>) \<bind> (\<lambda>_::unit. return_spmf True)))"])
  also have "\<dots> \<le>  \<integral>\<^sup>+ \<alpha>. ennreal (spmf (\<A> \<alpha> \<bind> (\<lambda>x. assert_spmf (f x \<alpha>) \<bind> (\<lambda>_::unit. return_spmf True))) True)
     \<partial>measure_spmf (sample_uniform (Coset.order G\<^sub>p))"
    by (rule nn_integral_mono_AE)(simp add: simple_le_on_assert)
  also have "\<dots>=?rhs" 
   using ennreal_spmf_bind[of "sample_uniform (Coset.order G\<^sub>p)" "(\<lambda>\<alpha>. \<A> \<alpha> \<bind> (\<lambda>x. assert_spmf (f x \<alpha>) \<bind> (\<lambda>_::unit. return_spmf True)))"]
   ..
  finally show ?thesis by fastforce
qed

text \<open>Showing the rule that less equal on "spmf (TRY ... ELSE return_spmf False) True"-constructs depends 
only on the contents less equalness (the ...'s). 
This will allow to transform the real games in the reduction-proof into a form to which we can apply 
the spmf_reduction lemma (basically eliminating the TRY ELSE blocks for the spmf_reduction lemma).\<close>
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

subsubsection \<open>less equal reduction theorem\<close>

text \<open>we show that the t-SDH game's advantage for the stronger reduction is less equal than the
t-SDH game's advantage for the "normal" reduction.\<close>
theorem t_SDH_advantage_stronger_red_le_red: "t_SDH_G\<^sub>p.advantage (stronger_bind_reduction \<A>) \<le> t_SDH_G\<^sub>p.advantage (bind_reduction \<A>)"
proof -
  let ?sr_game = "t_SDH_G\<^sub>p.game (stronger_bind_reduction \<A>)"
  let ?r_game = "t_SDH_G\<^sub>p.game (bind_reduction \<A>)"
  let ?\<alpha> = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>)^t)) [0..<max_deg+1])"
  note [simp] = Let_def split_def

  text \<open>same proof technique as in the stronger_bind_equivalence. But instead of showing equivalence 
  we use the spmf_reduction lemma to show less or equal\<close>

  text \<open>part 1 bring ?sr_game, the t-SDH game for the stronger reduction, into the form required for
  the spmf_reduction lemma.\<close>
  have "?sr_game = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
      \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
    return_spmf True } ELSE return_spmf False"
    by (simp add: t_SDH_G\<^sub>p.game_alt_def[of "(stronger_bind_reduction \<A>)"])
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
     _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));   
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
    return_spmf True } ELSE return_spmf False "
    using helping_1_add_poly_\<phi>_m_\<phi>' helping_2_factorize_\<alpha> by presburger
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));   
      _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
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
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    using assert_anding by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
      return_spmf True } ELSE return_spmf False"
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
      return_spmf True } ELSE return_spmf False"
    using helping_3_g_powPK_eq by algebra
  finally have sbr_game_ref: "t_SDH_G\<^sub>p.advantage (stronger_bind_reduction \<A>) = spmf (
    TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
      return_spmf True } ELSE return_spmf False
    ) True"
    unfolding t_SDH_G\<^sub>p.advantage_def by presburger


  text \<open>part 2 bring ?r_game, the t-SDH game for the "normal" reduction, into the form required for
  the spmf_reduction lemma.\<close>
   have "?r_game = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
      \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
    return_spmf True } ELSE return_spmf False"
     by (simp add: t_SDH_G\<^sub>p.game_alt_def[of "(bind_reduction \<A>)"])
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
     _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
        \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));   
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
    return_spmf True } ELSE return_spmf False "
    using helping_1_add_poly_\<phi>_m_\<phi>'_bindv helping_2_factorize_\<alpha>_bindv by presburger
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));   
      _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
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
          \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    using assert_anding by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
          \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
          \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
      return_spmf True } ELSE return_spmf False"
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  finally have br_game_ref: "t_SDH_G\<^sub>p.advantage (bind_reduction \<A>) = spmf (
    TRY do { 
      \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
      (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
         _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
        return_spmf True } ELSE return_spmf False
    ) True"
    unfolding t_SDH_G\<^sub>p.advantage_def by presburger

    
  text \<open>part 3 put the results from part 1 & 2 together and apply the spmf_reduction lemma. 
  Hence show the t-SDH game's advantage for the stronger reduction is less equal than the
  t-SDH game's advantage for the "normal" reduction.\<close>  
    show ?thesis
    proof -

      text \<open>To apply the spmf_reduction lemma we have to divide the logical conjunctions into two 
      functions f and q that take the input from the Adversary. This division allows us to 
      later on use the spmf_reduction lemma to conclude less equalness (adv(f \<and> q) \<le> adv(f)).
      Furthermore we define the f_n_q function, that mirrors the logical conjunctions from the t-SDH-
      game for the stronger bind reduction. And we show that we can split this f_n_q function into 
      the conjunction of f and q.\<close>
      let ?f_n_q = "\<lambda>(C, \<phi>, \<phi>') . \<lambda>\<alpha>. \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
            \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>'))"
      let ?f = "\<lambda>(C, \<phi>, \<phi>') . \<lambda>\<alpha>. \<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>'
            \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>'))"
      let ?q = "\<lambda>(C, \<phi>, \<phi>') . \<lambda>\<alpha>. 
          (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')"
      text \<open>We show that the "f \<and> q" definition is equal to the conjuncted definitions of f and q.
      (Basically "f \<and> q" = "f" \<and> "q")\<close>
      have f_n_q_conv : "\<forall>C \<phi> \<phi>' \<alpha>. ?f_n_q (C,\<phi>,\<phi>') \<alpha> \<longleftrightarrow> ?f (C,\<phi>,\<phi>') \<alpha> \<and> ?q (C,\<phi>, \<phi>') \<alpha>"
      proof (intro allI)
        fix C::'a
        fix \<phi> \<phi>':: "'e polynomial"
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

      text \<open>Show the advantage for the t-SDH-game for the stronger reduction(sr_game) is less equal the 
      advantage for the t-SDH-game for the "normal" reduction(r_game).
      sr_game and r_game differ only in their logical expressions in the assert_spmf statement, where 
      the sr_game asserts additional properties to those of the r_game. We chose f and q such that 
      q mirrors these additional properties and f mirros the properties of r_game. Hence sr_game 
      asserts f \<and> q and r_game asserts only f. Therefore we can apply the spmf_reduction lemma to 
      show adv. (sr_game) \<le> adv. (r_game).\<close>
      have "t_SDH_G\<^sub>p.advantage (stronger_bind_reduction \<A>) = spmf (
       TRY do { 
       \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
       (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);      
         _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>' 
            \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
            \<and> (g_pow_PK_Prod (?PK \<alpha>) \<phi> = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
            \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))   
            \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/?\<alpha> \<alpha>) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
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
        using spmf_reduction[of "\<lambda>\<alpha>. \<A> (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0..<max_deg + 1])"
             "\<lambda>(C, \<phi>, _, \<phi>', _). ?f (C,\<phi>,\<phi>')" "\<lambda>(C, \<phi>, _, \<phi>', _). ?q (C,\<phi>,\<phi>')"]
        by force
      also have "\<dots> =  t_SDH_G\<^sub>p.advantage (bind_reduction \<A>)"
        using br_game_ref[symmetric] by fast
      finally show ?thesis .
    qed
  qed

subsection \<open>show the advantage of the binding game less or equal to the advantage of bind reduction\<close>

text \<open>Pull the equivalence theorem (bind_game = t-SDH.game for stronger reduction) and 
the less equal reduction theorem (adv. (t-SDH.game for stronger reduction) \<le> 
adv. (t-SDH.game for "normal" reduction) ) together to show 
adv. (bind_game) \<le> adv. (t-SDH.game for "normal" reduction)\<close>
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
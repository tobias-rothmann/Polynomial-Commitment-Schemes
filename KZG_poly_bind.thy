theory KZG_poly_bind

imports KZG_correct CryptHOL_ext "tDL_assumption"
 "Berlekamp_Zassenhaus.Finite_Field_Factorization" "Elimination_Of_Repeated_Factors.ERF_Algorithm"

begin

section \<open>polynomial binding\<close>
text \<open>We show that the KZG is polynomial binding for every polynomial of degree <= max_deg.
We use the Sigma_Commit_Crypto template to prove the binding game.
The proof is adapted from the Appendix C.1 in the original paper:
A. Kate, G. Zaverucha, and I. Goldberg. Polynomial commitments. Technical report, 2010. 
CACR 2010-10, Centre for Applied Cryptographic Research, University of Waterloo 
(available at https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf)\<close>

locale KZG_CS_binding = KZG_PCS_correct
begin

subsection \<open>t-Dl game\<close>
text \<open>We reduce the polynomial binding to the t-DL assumption\<close>

sublocale t_DL_G\<^sub>p: t_DL G\<^sub>p max_deg "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding t_DL_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

text \<open>Intuetively what we want to show is that if we have an adversary that can compute two 
polynomials such that they have the same commitment in polynomial time, we can construct an 
algorithm, using that adversary, that can solve the t-DL in polynomial time, thus breaking the 
t-DL assumption.\<close>

text \<open>This functions purpose is to extract \<alpha> based on the inputs g^\<alpha> and \<phi>, where \<phi> has a root at \<alpha>. 
The function factorizes \<phi> and filters for all roots. Since \<alpha>'s mod_ring is of the same cardinality 
as g's group's order, we can conclude that if g^r = g^\<alpha> then r=\<alpha>\<close>
fun find_\<alpha>_square_free :: "'a \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring" where
  "find_\<alpha>_square_free g_pow_\<alpha> \<phi> = (let (c, polys) = finite_field_factorization \<phi>;
    deg1_polys = filter (\<lambda>f. degree f = 1) polys;
    root_list = map (\<lambda>p. poly.coeff p 0) deg1_polys;
    \<alpha>_roots = filter (\<lambda>r. g_pow_\<alpha> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> -r) root_list
in -\<alpha>_roots!0)"

text \<open>The radical is executable via the formalization of the 
'Elimination of Repeated Factors Algorithm' in the AFP 
(see https://www.isa-afp.org/entries/Elimination_Of_Repeated_Factors.html)\<close>
fun find_\<alpha> :: "'a \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring" where
  "find_\<alpha> g_pow_\<alpha> \<phi> = find_\<alpha>_square_free g_pow_\<alpha> (radical \<phi>)"

text \<open>The reduction: 
An adversary for the KZG polynomial binding can output two polynomials \<phi> and \<phi>' that have the same 
commitment, i.e g^\<phi>(\<alpha>) = g^\<phi>(\<alpha>), which is equivalent to \<phi>(\<alpha>) = \<phi>'(\<alpha>) (same argument as in the 
function above). Hence (\<phi>-\<phi>')(\<alpha>) = 0, so (\<phi>-\<phi>') has a root at \<alpha>. Furthermore we have g^\<alpha> in the 
public key at position 1. Hence we can use the find_\<alpha> function to compute \<alpha> in 
polynomial time. Given \<alpha> we can easily compute a c and a g' such that g^(1/((\<alpha>+c))) = g'.
E.g. c=0 and g' = g^(1/\<alpha>)
Hence we can break the t-DL assumption, as we have a polynomial-time algorithm to compute (c,g).
\<close>
fun bind_reduction
  :: "('a ck, 'e mod_ring poly, 'a commit, unit) bind_adversary \<Rightarrow> ('a,'e) t_DL.adversary"                     
where
  "bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  let \<alpha> = find_\<alpha> (PK!1) (\<phi> - \<phi>');
  return_spmf \<alpha>}"

text \<open>This function captures the bind_reduction with the asserts from the binding game, essentially 
allowing us to prove the equivalence of binding game to t-DL game with stronger_bind_reduction. 
From this equivalence it is easy to proof the theorem winnnng the binding game is less than or equal 
to breaking the t-DL assumption\<close>
fun stronger_bind_reduction
  :: "('a ck, 'e mod_ring poly, 'a commit, unit)  bind_adversary \<Rightarrow> ('a,'e) t_DL.adversary"                     
where
  "stronger_bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' 
    \<and> valid_poly \<phi> 
    \<and> valid_poly \<phi>' 
    \<and> (C = g_pow_PK_Prod PK \<phi>) 
    \<and> (C = g_pow_PK_Prod PK \<phi>'));
  let \<alpha> = find_\<alpha> (PK!1) (\<phi> - \<phi>');
  return_spmf \<alpha>}"


subsection \<open>helping lemmas\<close>

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

text \<open>show find_\<alpha> correctly finds(factorizes) \<alpha>, if \<alpha> is a root and \<phi> is not a zero-polynomial.\<close>
lemma poly_eq0_imp_find_\<alpha>_eq_\<alpha>: "\<phi> \<noteq> 0 \<Longrightarrow> poly \<phi> \<alpha> = 0 \<Longrightarrow> find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>"
proof -
  assume \<phi>_ne_0: "\<phi> \<noteq> 0"
  assume \<alpha>_root: "poly \<phi> \<alpha> = 0"
  have "(radical \<phi>) \<noteq> 0"
    by (simp add: \<phi>_ne_0)
  moreover have "poly (radical \<phi>) \<alpha> = 0" 
    using \<alpha>_root same_zeros_radical by blast
  moreover have "square_free (radical \<phi>)" 
    using \<open>(radical \<phi>) \<noteq> 0\<close> \<phi>_ne_0 squarefree_radical squarefree_square_free by blast
  ultimately show "find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>"
    unfolding find_\<alpha>.simps using poly_eq0_is_find_\<alpha>_sf_eq_\<alpha> by blast
qed

subsubsection \<open>literal helping lemmas\<close>

text \<open>From here on we define literal helping lemmas, with name-pattern: helping_*number*_*content-reference*. 
These lemmas are literal logic blocks that are used in the actual equivalence proof. 
They all capture one step in the transition (from poly_bind game to t-DL reduction game logic), that is either 
too complicated for Isabelle to prove in the monadic/game-based form or requires some additional proving steps 
that would complicate the equivalence proof.
Basically extracted logical reasoning.\<close>

text \<open>The logical addition of (\<phi>-\<phi>')(\<alpha>)=0, which is implied by \<phi>(\<alpha>)=\<phi>'(\<alpha>), which we derive from C=g^\<phi>(\<alpha>) \<and> C=g^\<phi>'(\<alpha>)\<close>
lemma helping_1_add_poly_\<phi>_m_\<phi>': "(\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')) 
        = (\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (poly (\<phi> - (\<phi>')) (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0))"
  unfolding valid_poly_def 
  using commit_eq_is_poly_diff_\<alpha>_eq_0 by fast

text\<open>\<close>
lemma helping_2_factorize_\<alpha>: "\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (poly (\<phi> - \<phi>') (of_int_mod_ring (int \<alpha>)::'e mod_ring) = 0)
        \<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs using poly_eq0_imp_find_\<alpha>_eq_\<alpha>
    by (meson right_minus_eq)
next 
  assume ?rhs
  then show ?lhs 
    unfolding valid_poly_def
    using commit_eq_is_poly_diff_\<alpha>_eq_0 by fast
qed
                                
text \<open>\<close>
lemma helping_3_\<alpha>_is_found: "\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring)) 
\<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
          \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>) \<and> (C = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1]) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring))) (\<phi> - \<phi>') = (of_int_mod_ring (int \<alpha>)::'e mod_ring)) 
          \<and> of_int_mod_ring (int \<alpha>) = find_\<alpha> ((map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1])!1) (\<phi> - \<phi>')"
  (is "?lhs = ?rhs")
proof -
  have "map (\<lambda>t::nat. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0::nat..<max_deg + (1::nat)] ! (1::nat) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>)"
    using PK_i d_pos by force
  then show ?thesis by metis

qed

subsection \<open>KZG poly bind game to strong reduction game - equivalence theorem\<close>

text \<open>showing the equivalence of the KZG poly bind game to the stronger bind_reduction game, which we 
show to be at least as hard as the real reduction game in the next subsection.\<close>

theorem poly_bind_game_eq_t_DL_strong_red: 
  shows "cs.bind_game \<A> = t_DL_G\<^sub>p.game (stronger_bind_reduction \<A>)"
proof -
  note [simp] = Let_def split_def

  text \<open>abbreviations for the mod_ring version of sample uniform nat 
  and the public key\<close>
  let ?\<alpha> = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>)^t)) [0..<max_deg+1])"

  text \<open>We start with the poly bind game and perform logical 
  transitions until we obtain the t-DL game with the (stronger-)reduction\<close>
  have "cs.bind_game \<A> = TRY do {
    (ck,vk) \<leftarrow> key_gen;
    (c, m, d, m', d') \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf(m \<noteq> m' \<and> valid_poly m \<and> valid_poly m'); 
    let b = verify_poly vk m c d;
    let b' = verify_poly vk m' c d';
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True} ELSE return_spmf False" 
    by (simp add: abstract_commitment.bind_game_alt_def) 
    also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'e mod_ring)^t)) [0..<max_deg+1];
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>'); 
    _ :: unit \<leftarrow> assert_spmf ((C = g_pow_PK_Prod PK \<phi>) \<and> (C = g_pow_PK_Prod PK \<phi>'));
    return_spmf True} ELSE return_spmf False"
      unfolding key_gen_def verify_poly_def Setup_def by simp
    also have "\<dots> = TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
         _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>'); 
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
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    by (presburger add: assert_collapse)
  also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
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
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"    
   using helping_2_factorize_\<alpha> by presburger
 also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>))
        \<and> ((?\<alpha> \<alpha>) = find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>')));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False" 
   using helping_3_\<alpha>_is_found
   by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
       TRY do {
       _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
          \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
          \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));   
      _::unit \<leftarrow> assert_spmf ((?\<alpha> \<alpha>) = find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>'));
      return_spmf True } ELSE return_spmf False
      } ELSE return_spmf False 
    } ELSE return_spmf False"
    by (presburger add: assert_collapse)
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
     _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?\<alpha> \<alpha>))) (\<phi> - \<phi>') = (?\<alpha> \<alpha>)));   
    _::unit \<leftarrow> assert_spmf ((?\<alpha> \<alpha>) = find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>'));
    return_spmf True } ELSE return_spmf False " 
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
        \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>')
        \<and> (poly (\<phi> - \<phi>') (?\<alpha> \<alpha>) = 0));    
  _::unit \<leftarrow> assert_spmf ((?\<alpha> \<alpha>) = find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>'));
    return_spmf True } ELSE return_spmf False"
    using helping_2_factorize_\<alpha> by presburger
   also have "\<dots>  = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
      \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
    _::unit \<leftarrow> assert_spmf ((?\<alpha> \<alpha>) = find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>'));
    return_spmf True } ELSE return_spmf False "
     using helping_1_add_poly_\<phi>_m_\<phi>' by presburger
  also have "\<dots>= TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    \<alpha>' \<leftarrow>  do {
      (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (?PK \<alpha>);
      _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> valid_poly \<phi> \<and> valid_poly \<phi>' 
      \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>) \<and> (C = g_pow_PK_Prod (?PK \<alpha>) \<phi>'));
      let \<alpha> = find_\<alpha> ((?PK \<alpha>)!1) (\<phi> - \<phi>');
      return_spmf \<alpha> };
    _::unit \<leftarrow> assert_spmf ((?\<alpha> \<alpha>) = \<alpha>');
    return_spmf True } ELSE return_spmf False"
    by fastforce
  also have "\<dots> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    \<alpha>' \<leftarrow> (stronger_bind_reduction \<A>) (?PK \<alpha>);
    _::unit \<leftarrow> assert_spmf ((?\<alpha> \<alpha>) = \<alpha>');
    return_spmf True } ELSE return_spmf False"
    unfolding stronger_bind_reduction.simps 
    using g_pow_to_int_mod_ring_of_int_mod_ring_pow_t by presburger
   also have "\<dots>= t_DL_G\<^sub>p.game (stronger_bind_reduction \<A>)"
    using t_DL_G\<^sub>p.game_alt_def[of "(stronger_bind_reduction \<A>)"] by simp
  finally show ?thesis .
qed

lemma t_DL_advantage_stronger_red_le_red: 
"t_DL_G\<^sub>p.advantage (stronger_bind_reduction \<A>) \<le> t_DL_G\<^sub>p.advantage (bind_reduction \<A>)"
  apply (simp only: t_DL_G\<^sub>p.advantage_def t_DL_G\<^sub>p.game_def 
        bind_reduction.simps stronger_bind_reduction.simps)
    apply (rule try_spmf_le)
    apply (simp only: bind_spmf_assoc)
    apply (rule bind_spmf_le)+
    apply (auto split: prod.splits simp del: find_\<alpha>.simps g_pow_PK_Prod.simps indicator_simps pmf_return)
    apply (rule del_assert)
    done

theorem polynomial_binding: 
  "poly_bind_advantage \<A>  \<le> t_DL_G\<^sub>p.advantage (bind_reduction \<A>)"
  apply (simp add: poly_bind_advantage_def cs.bind_advantage_def)
  apply (simp add: poly_bind_game_eq_t_DL_strong_red)
  apply (insert t_DL_advantage_stronger_red_le_red)
  apply (simp add: t_DL_G\<^sub>p.advantage_def)
  done

end

end
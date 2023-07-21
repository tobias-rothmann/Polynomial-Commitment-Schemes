theory Commitment_Scheme

imports "CryptHOL.CryptHOL" "CryptHOL.Cyclic_Group" "CRYSTALS-Kyber.Kyber_spec" "Sigma_Commit_Crypto.Commitment_Schemes"
  "Berlekamp_Zassenhaus.Finite_Field_Factorization" "Sigma_Commit_Crypto.Cyclic_Group_Ext" Complex_Main


begin
section \<open>Type Class for Factorial Ring $\mathbb{Z}_p[x]/(x^d-1)$.\<close>
text \<open>Quotient ring $\mathbb{Z}_p[x]/(x^d-1) \equiv (\mathbb{Z}_p[x])^{<d}$
where $p$ is a prime and $d>0$.
We encode this quotient ring as a type. In order to do so, we first look at the
finite field $\mathbb{Z}_p$ implemented by \<open>('a::prime_card) mod_ring\<close>. 
Then we define polynomials using the constructor \<open>poly\<close>.
For factoring out $x^d-1$, we define an equivalence relation on the polynomial ring
$\mathbb{Z}_p[x]$ via the modulo operation with modulus $x^d-1$.
Finally, we build the quotient of the equivalence relation using the construction 
\<open>quotient_type\<close>.\<close>

text \<open>Modulo relation between two polynomials. \<close>

text \<open>Type class \<open>qr_spec\<close> for quotient ring $\mathbb{Z}_q[x]/(p)$. 
  The polynomial p is represented as \<open>qr_poly'\<close> (an polynomial over the integers).\<close>


text \<open>We define a modulo relation \<open>qr_rel\<close> for polynomials modulo a polynomial $p=$\<open>qr_poly\<close>.\<close>

text \<open>Using this equivalence relation, we can define the quotient ring as a \<open>quotient_type\<close>.
The modulo type we get is the quotiet ring \<open>'a qr\<close>\<close>

text \<open>Defining the conversion functions.
 to_qr :: "'a :: qr_spec mod_ring poly \<Rightarrow> 'a qr" 
 of_qr :: "'a qr \<Rightarrow> 'a :: qr_spec mod_ring poly" 
\<close>

(*
Vorsicht! der Einfachkeit halber, sind alle Polynome bis Grad einschließlich d-1 im Typen qr!

ein Element k aus (Z_p)[x]^{<d} : "k :: 'a qr"
*)

section \<open>Assumptions\<close>

subsection \<open>t-Strong Diffie Hellmann Assumption (t-SDH)\<close>

locale t_SDH = G\<^sub>p : cyclic_group G
for G (structure)
begin

(*type_synonym 'grp' t_SDH_adversary = "'grp' list \<Rightarrow> ('q mod_ring *'grp') spmf"*)
type_synonym 'grp adversary = "'grp list \<Rightarrow> (nat *'grp) spmf"


text \<open>TODO ändere to setup function\<close>
definition game :: "nat \<Rightarrow> 'a adversary \<Rightarrow> bool spmf" where 
  "game t \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G);
    (c, g) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g [^] (int \<alpha>^t')) [0..<t+1]);
    return_spmf (\<^bold>g [^] (1/((\<alpha>+c))) = g) 
  } ELSE return_spmf False"


definition advantage :: "nat \<Rightarrow> 'a adversary \<Rightarrow> real"
  where "advantage t \<A> = spmf (game t \<A>) True" \<comment>\<open>subtract Pr random (\<alpha>+c)\<close>

(* adapted proof from Sigma_Commit_Crypto.Commitment_Schemes bind_game_alt_def  *)
lemma game_alt_def:
  "game t \<A> = TRY do { 
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

section \<open>commitment scheme spec\<close>

locale commit_scheme_spec =
G\<^sub>p : cyclic_group G\<^sub>p + G\<^sub>T : cyclic_group G\<^sub>T 
for G\<^sub>p  (structure) and G\<^sub>T  (structure) +
fixes "type_a" :: "('q :: qr_spec) itself" 
  and d p::int
  and e
and deg_t::nat
assumes
p_gr_two: "p > 2" and
p_prime : "prime p" and
(* Bilinear Group Assumptions *)
CARD_G\<^sub>p: "int (order G\<^sub>p) = p" and
CARD_G\<^sub>T: "int (order G\<^sub>T) = p" and
e_symmetric: "e \<in> carrier G\<^sub>p \<rightarrow> carrier G\<^sub>p \<rightarrow> carrier G\<^sub>T" and 
e_bilinear: "\<forall>a b::'q mod_ring . \<forall>P Q. P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p \<longrightarrow> 
   e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a)) (Q [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
= (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a*b))" and 
(*$(\mathbb{Z}_p[x])^{<d}$ Assumptions*)
d_pos: "d > 0" and
CARD_q: "int (CARD('q)) = p" and
qr_poly'_eq: "qr_poly' TYPE('q) = Polynomial.monom 1 (nat d) - 1" and
t_SDH_GP: "t_SDH G\<^sub>p" and
deg_t_le_p: "deg_t \<le> p" 
\<comment>\<open>and t_SDH_GP: "t_SDH GP"\<close>
begin

sublocale t_SDH_G\<^sub>p: t_SDH G\<^sub>p using t_SDH_GP by blast

subsection \<open>Additional group lemmas\<close>

lemma e_linear_in_fst: 
  assumes "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
  shows "e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) (Q) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)"
proof -
  have "e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) Q = e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (1::'q mod_ring))" using assms by simp
  also have "... = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a*(1::'q mod_ring)))" using assms e_bilinear by fast
  also have "\<dots>=(e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" by simp
  ultimately show "e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a)) Q = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" by argo
qed

lemma e_linear_in_snd: 
assumes "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
shows "e (P) (Q [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)"
proof -
have "e P (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) = e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (1::'q mod_ring)) (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a)" using assms by simp
  also have "... = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring ((1::'q mod_ring)*a))" using assms e_bilinear by fast
  also have "\<dots>=(e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" by simp
  ultimately show "e P (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) = e P Q [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring a" by argo
qed  
  

subsubsection\<open>mod_ring operations on pow for Gp\<close>

lemma pow_mod_order_G\<^sub>p: "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod p)" 
proof -
  have "p=(order G\<^sub>p)" by (simp add: CARD_G\<^sub>p)
  also have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)"
  proof -
    have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x \<in> carrier G\<^sub>p" by simp
    let ?d = "x div (order G\<^sub>p)"
    have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (?d * order G\<^sub>p + x mod order G\<^sub>p)" 
      using div_mult_mod_eq by presburger
    also have "\<dots>= \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (?d * order G\<^sub>p) \<otimes>\<^bsub>G\<^sub>p\<^esub>  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)"
      using G\<^sub>p.int_pow_mult by blast
    also have "\<dots>=\<one>\<^bsub>G\<^sub>p\<^esub> \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)"
      by (metis G\<^sub>p.generator_closed G\<^sub>p.int_pow_closed G\<^sub>p.int_pow_pow G\<^sub>p.pow_order_eq_1 int_pow_int)
    ultimately show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)" by fastforce
  qed
  ultimately show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod p)" 
    by auto
qed

lemma mod_ring_pow_mult_G\<^sub>p[symmetric]:" (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
  =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a+b))"
proof -
  have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a + to_int_mod_ring b)"
    by (simp add: G\<^sub>p.int_pow_mult)
  also have "\<dots>=  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> ((to_int_mod_ring a + to_int_mod_ring b) mod (CARD ('q)))" 
    using pow_mod_order_G\<^sub>p CARD_q by blast
  also have "\<dots>=  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a + b)"
    by (simp add: plus_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  finally show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a + b)"
    by blast
qed

lemma mod_ring_pow_pow_G\<^sub>p[symmetric]: "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (b::'q mod_ring)) 
                       = \<^bold>g\<^bsub>G\<^sub>p\<^esub>[^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a*b::'q mod_ring))"
proof -
  have "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a * to_int_mod_ring b))"
    using G\<^sub>p.int_pow_pow by auto
  also have "\<dots> = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> ((to_int_mod_ring a * to_int_mod_ring b) mod CARD ('q)))"
    using CARD_q pow_mod_order_G\<^sub>p by blast
  also have "\<dots>=  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a * b)"
    by (simp add: times_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  finally show "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b 
               = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a * b)"
    by blast
qed

lemma mod_ring_pow_mult_inv_G\<^sub>p[symmetric]:" (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>p\<^esub> inv\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
  =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a-b))"
proof -
  have "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>p\<^esub> inv\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
        = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (- to_int_mod_ring b))"
    by (simp add: G\<^sub>p.int_pow_neg)
  also have "\<dots>=(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> ((to_int_mod_ring a + -to_int_mod_ring b) mod CARD ('q)))"
    using pow_mod_order_G\<^sub>p CARD_q G\<^sub>p.generator_closed G\<^sub>p.int_pow_mult by presburger
  also have "\<dots>=(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> ((to_int_mod_ring a - to_int_mod_ring b) mod CARD ('q)))"
    by fastforce
  also have "\<dots>=  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a - b)"
    by (simp add: minus_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  finally show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>p\<^esub> inv\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a - b)"
    by blast
qed

subsubsection\<open>mod_ring operations on pow for GT\<close>

lemma pow_mod_order_G\<^sub>T: "g \<in> carrier G\<^sub>T \<Longrightarrow> g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod p)" 
proof -
  assume asmpt: "g \<in> carrier G\<^sub>T"
  have "p=(order G\<^sub>T)" by (simp add: CARD_G\<^sub>T)
  also have "g[^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
  proof -
    have "g [^]\<^bsub>G\<^sub>T\<^esub> x \<in> carrier G\<^sub>T" using asmpt by simp
    let ?d = "x div (order G\<^sub>T)"
    have "g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (?d * order G\<^sub>T + x mod order G\<^sub>T)" 
      using div_mult_mod_eq by presburger
    also have "\<dots>=g [^]\<^bsub>G\<^sub>T\<^esub> (?d * order G\<^sub>T) \<otimes>\<^bsub>G\<^sub>T\<^esub>  g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
      using G\<^sub>T.int_pow_mult asmpt by fast
    also have "\<dots>=\<one>\<^bsub>G\<^sub>T\<^esub> \<otimes>\<^bsub>G\<^sub>T\<^esub> g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
      by (metis G\<^sub>T.int_pow_one G\<^sub>T.int_pow_pow G\<^sub>T.pow_order_eq_1 int_pow_int mult.commute asmpt)
    ultimately show "g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
      using asmpt by fastforce
  qed
  ultimately show "g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod p)" 
    by auto
qed

lemma mod_ring_pow_mult_G\<^sub>T[symmetric]:" x \<in> carrier G\<^sub>T \<Longrightarrow> (x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>T\<^esub> (x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring b)) 
  =  x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a+b))"
proof -
  assume asmpt: "x \<in> carrier G\<^sub>T"
  have "x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>T\<^esub> x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring b =  x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a + to_int_mod_ring b)"
    by (simp add: G\<^sub>T.int_pow_mult asmpt)
  also have "\<dots>=  x [^]\<^bsub>G\<^sub>T\<^esub> ((to_int_mod_ring a + to_int_mod_ring b) mod (CARD ('q)))" 
    using pow_mod_order_G\<^sub>T CARD_q asmpt by blast
  also have "\<dots>=  x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring (a + b)"
    by (simp add: plus_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  finally show "x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>T\<^esub> x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring b = x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring (a + b)"
    by blast
qed

subsection \<open>other locale derived lemmas\<close>

lemma [simp]: "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> p = \<one>\<^bsub>G\<^sub>p\<^esub>"
  using CARD_G\<^sub>p G\<^sub>p.pow_order_eq_1 by (metis G\<^sub>p.generator_closed int_pow_int)

lemma [simp]: "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x*p) =  \<one>\<^bsub>G\<^sub>p\<^esub>"
  by (metis CARD_G\<^sub>p G\<^sub>p.generator_closed G\<^sub>p.int_pow_one G\<^sub>p.int_pow_pow G\<^sub>p.pow_order_eq_1 int_pow_int mult.commute)

subsection \<open>pow mod_ring and lemmas\<close>

(*  TODO dirty  *)
abbreviation pow_mod_ring_G\<^sub>p :: "'a \<Rightarrow>'q mod_ring \<Rightarrow> 'a" (infixr "^\<^bsub>G\<^sub>p\<^esub>" 75)
  where "x ^\<^bsub>G\<^sub>p\<^esub> q \<equiv> x [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring q)"

lemma "finite (carrier G\<^sub>p)"
  using G\<^sub>p.finite_carrier by auto

(*TODO delete nat and import for ext_cyclic_group*)
fun to_nat_mod_ring :: "'q mod_ring \<Rightarrow> nat" where
  "to_nat_mod_ring x = nat (to_int_mod_ring x)"

fun of_nat_mod_ring :: "nat \<Rightarrow> 'q mod_ring" where
  "of_nat_mod_ring x = of_int_mod_ring (int x)"

lemma of_nat_mod_ring_to_nat_mod_ring[simp]: "of_nat_mod_ring (to_nat_mod_ring x) = x"
proof -
  have "to_int_mod_ring x \<ge> 0" using range_to_int_mod_ring by fastforce
  then have "int (nat (to_int_mod_ring x)) = to_int_mod_ring x" by presburger
  then show "of_nat_mod_ring (to_nat_mod_ring x) = x" 
    using of_int_mod_ring_to_int_mod_ring by auto
qed
(*TODO nat delete until here*)

lemma to_int_mod_ring_ge_0: "to_int_mod_ring x \<ge> 0" 
  using range_to_int_mod_ring by fastforce

lemma pow_on_eq_card: "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) = (x=y)"
proof 
  assume assm: "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y"
  then have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring y"
    using assm by blast
  then have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> nat (to_int_mod_ring x) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> nat (to_int_mod_ring y)" 
    using to_int_mod_ring_ge_0[of "x"] to_int_mod_ring_ge_0[of "y"] by fastforce
  then have "[nat (to_int_mod_ring x) = nat (to_int_mod_ring y)] (mod order G\<^sub>p)"
    using G\<^sub>p.pow_generator_eq_iff_cong G\<^sub>p.finite_carrier by fast
  then have "[to_int_mod_ring x = to_int_mod_ring y] (mod order G\<^sub>p)" 
    using to_int_mod_ring_ge_0[of "x"] to_int_mod_ring_ge_0[of "y"]
    by (metis cong_int_iff int_nat_eq)
  then have "[to_int_mod_ring x = to_int_mod_ring y] (mod p)" 
    using CARD_G\<^sub>p by fast
  then have "to_int_mod_ring x = to_int_mod_ring y" using range_to_int_mod_ring CARD_q
    by (metis cong_def of_int_mod_ring.rep_eq of_int_mod_ring_to_int_mod_ring to_int_mod_ring.rep_eq)
  then show "x = y" by force
next 
  assume "x = y"
  then show "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y" by fast
qed


section \<open>KZG functions\<close>
text \<open>for reference see section 3.2 Construction: PolyCommitDL in the 
extended Paper "Constant-Size Commitments to Polynomials and
Their Applications" 
(https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf)\<close>

subsection \<open>Setup(1^k,t) ==> PK = (g,g^\<alpha>,g^(\<alpha>^2),...,g^(\<alpha>^t)) group G is globally fixed\<close>

fun Setup :: "'q mod_ring \<Rightarrow> nat \<Rightarrow> 'a list" where 
  "Setup \<alpha> t = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<t+1]"

lemma Setup_append[symmetric, simp]:"Setup \<alpha> t @ [\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^(Suc t))] = Setup \<alpha> (Suc t)"
  by force

lemma Setup_i: "i\<le>t \<Longrightarrow> Setup \<alpha> t ! i =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^i)"
proof (induction t)
  case 0
  then show ?case by force
next
  case (Suc t)
  then show ?case 
  proof (cases "i\<le>t")
    case True
    then show ?thesis 
      by (metis Setup.simps Suc.prems Suc_eq_plus1 less_Suc_eq_le minus_nat.diff_0 nth_map_upt plus_nat.add_0)
  next
    case False
    then show ?thesis
      by (metis Setup.simps Suc.prems Suc_eq_plus1 linorder_not_less minus_nat.diff_0 not_less_eq nth_map_upt plus_nat.add_0)
  qed
qed

corollary Setup_i_lengthSetup: "i<length (Setup \<alpha> t) \<Longrightarrow> Setup \<alpha> t ! i = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^i)"
proof (rule Setup_i)
  show "i < length (Setup \<alpha> t) \<Longrightarrow> i \<le> t"
    by force
qed

subsection \<open>Commit(PK, \<phi>) ==> C = g^\<phi>(\<alpha>)\<close>

(*  this abstraction allows reuse for the CreateWitness function  *)
fun g_pow_PK_Prod :: "'a list \<Rightarrow>'q mod_ring poly \<Rightarrow> 'a" where
  "g_pow_PK_Prod PK \<phi> = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!pk ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"

fun Commit :: "'a list \<Rightarrow>'q qr \<Rightarrow> 'a" where 
  "Commit PK \<phi> = g_pow_PK_Prod PK (of_qr \<phi>)"

lemma g_pow_PK_Prod_inserted[simp]: "degree \<phi> \<le> t \<Longrightarrow> g_pow_PK_Prod (Setup \<alpha> t) \<phi> = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^pk)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
proof -
  assume asmpt: "degree \<phi> \<le> t"
  have "g_pow_PK_Prod (Setup \<alpha> t) \<phi> = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (Setup \<alpha> t)!pk ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>" 
    by auto
  also have "fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (Setup \<alpha> t)!pk ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>
           = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^pk)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>" 
  proof(rule List.fold_cong)
    show "\<one>\<^bsub>G\<^sub>p\<^esub> = \<one>\<^bsub>G\<^sub>p\<^esub>" by simp
    show "[0..<Suc (degree \<phi>)] = [0..<Suc (degree \<phi>)]" by blast
    show "\<And>x. x \<in> set [0..<Suc (degree \<phi>)] \<Longrightarrow>
         (\<lambda>g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> Setup \<alpha> t ! x       ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> x) 
       = (\<lambda>g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> x)"
    proof 
      fix x::nat
      fix g::'a
      assume "x \<in> set [0..<Suc (degree \<phi>)]"
      then have "Setup \<alpha> t ! x = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x)" 
        using Setup_i asmpt by auto
      then show "g \<otimes>\<^bsub>G\<^sub>p\<^esub> Setup \<alpha> t ! x ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> x = g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> x" 
        by presburger
    qed
  qed
  ultimately show "g_pow_PK_Prod (Setup \<alpha> t) \<phi> = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ pk) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> pk) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
    by argo
qed

lemma poly_altdef_to_fold[symmetric]: "n\<le>degree \<phi>  \<Longrightarrow> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>n. poly.coeff \<phi> i * \<alpha> ^ i) 
                          = fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc n] \<one>\<^bsub>G\<^sub>p\<^esub>"
proof (induction n)
  case 0
  have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>0. poly.coeff \<phi> i * \<alpha> ^ i) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> 0 * \<alpha> ^ 0)"
    by force
  moreover have "fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc 0] \<one>\<^bsub>G\<^sub>p\<^esub> 
    =  \<one>\<^bsub>G\<^sub>p\<^esub> \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (0::nat) * \<alpha> ^ (0::nat))" by force
  moreover have "\<one>\<^bsub>G\<^sub>p\<^esub> \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (0::nat) * \<alpha> ^ (0::nat)) 
      = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (0::nat) * \<alpha> ^ (0::nat))" using G\<^sub>p.generator_closed G\<^sub>p.generator G\<^sub>p.l_one by simp 
  ultimately show ?case by argo
next
  case (Suc n)
  have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>Suc n. poly.coeff \<phi> i * \<alpha> ^ i) 
      = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<Sum>i\<le>n. poly.coeff \<phi> i * \<alpha> ^ i) 
      + poly.coeff \<phi> (Suc n) * \<alpha> ^ (Suc n))" by force
  also have "\<dots>= \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>n. poly.coeff \<phi> i * \<alpha> ^ i) 
     \<otimes>\<^bsub>G\<^sub>p\<^esub>  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (Suc n) * \<alpha> ^ (Suc n))" 
    using mod_ring_pow_mult_G\<^sub>p by fastforce
  also have "\<dots> = fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc n] \<one>\<^bsub>G\<^sub>p\<^esub>
                \<otimes>\<^bsub>G\<^sub>p\<^esub>  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (Suc n) * \<alpha> ^ (Suc n))" 
    using Suc by auto
  also have "\<dots>=fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc (Suc n)] \<one>\<^bsub>G\<^sub>p\<^esub>"
    by simp
  finally show ?case .
qed

lemma g_pow_PK_Prod_correct: "degree \<phi> \<le> t \<Longrightarrow> g_pow_PK_Prod (Setup \<alpha> t) \<phi> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi> \<alpha> )"
proof -
  assume asmpt: "degree \<phi> \<le> t"
  have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly \<phi> \<alpha> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * \<alpha> ^ i)"
    by (simp add: poly_altdef)
  moreover have "g_pow_PK_Prod (Setup \<alpha> t) \<phi> = fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
  proof -
    have "g_pow_PK_Prod (Setup \<alpha> t) \<phi> = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^pk)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
      using g_pow_PK_Prod_inserted asmpt by blast
    moreover have "\<forall>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^n)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n) 
              = g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)"
      by (simp add: mod_ring_pow_pow_G\<^sub>p mult.commute G\<^sub>p.int_pow_pow)
    ultimately show "g_pow_PK_Prod (Setup \<alpha> t) \<phi> 
    = fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
      by presburger
  qed
  ultimately show "g_pow_PK_Prod (Setup \<alpha> t) \<phi> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly \<phi> \<alpha>" 
    using poly_altdef_to_fold[of "degree \<phi>" \<phi> \<alpha>] by fastforce
qed

corollary Commit_correct: "degree (of_qr \<phi>) \<le> t \<Longrightarrow> Commit (Setup \<alpha> t) \<phi> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha> )"
  using g_pow_PK_Prod_correct by force

subsection \<open>Open(PK, C, \<phi>) => \<phi>\<close>

fun Open :: "'a list \<Rightarrow> 'a \<Rightarrow> 'q mod_ring poly \<Rightarrow> 'q mod_ring poly" where
  "Open PK C \<phi> = \<phi>"

subsection \<open>VerifyPoly(PK, C, \<phi>)\<close>

fun VerifyPoly :: "'a list \<Rightarrow> 'a \<Rightarrow>  'q qr \<Rightarrow> bool" where
  "VerifyPoly PK C \<phi> = (C = Commit PK \<phi>)"

lemma VerifyPoly_correct: "degree (of_qr \<phi>)\<le>t \<Longrightarrow> VerifyPoly (Setup \<alpha> t) C \<phi> \<equiv> (C=Commit (Setup \<alpha> t) \<phi>)"
  by fastforce

subsection \<open>CreateWitness(PK, \<phi>, i)==> (i,\<phi>(i),w_i)\<close>
text \<open>w_i is \<psi>(\<alpha>) in  \<phi>(x)-\<phi>(u)=(x-u)\<psi>(x)\<close>

subsubsection \<open>\<psi> extractor : \<phi>(x)-\<phi>(u)=(x-u)\<psi>(x) for w_i=\<psi>(\<alpha>)\<close>

(*
Defining and proving-correct a extractor for the polynomial q in f(x)-f(u)=(x-u)q(x), namely 
"compute_q f u" with f being a polynomial and x being a variable and u being a "known variable
/parameter".

Basic proof outline:

1. Convert f in sum-form:
f(x)-f(u) = (\<Sum>i\<le>degree f. coeff f i * x^i) - (\<Sum>i\<le>degree f. coeff f i * x^i)
from that one easily reduces to (x-u)(\<Sum>i\<le>degree f. coeff f i * (\<Sum>j<i. u^(i - Suc j)*x^j)) 
(see power_diff_sumr2)

2. Ordering the summation:
One can imagine the summation to be horizontal, in the sense that it computes the coeffs 
form 0 to degree f, and adds (or could add) to each coeff in every iteration:
0: 0 +
1: f\<^sub>1 +
2: f\<^sub>2*u + f\<^sub>2*x +
3: f\<^sub>3*u^2 + f\<^sub>3*u*x + f\<^sub>3*x^2
...
n: f\<^sub>n*u^(n-1) + ... f\<^sub>n*u^((n-1)-i)*x^i ...  + f\<^sub>n*x^(n-1)
we order it to compute coeffs one by one (to compute vertical)
1: 0 + f\<^sub>1          + ... + f\<^sub>n*u^(n-1)         +
2: 0 + f\<^sub>2 * x      + ... + f\<^sub>n*u^((n-1)-1) * x +
...
n: 0 + f\<^sub>n * x^(n-1)
In formulas:
(\<Sum>i\<le>degree f. coeff f i * (\<Sum>j<i. u^(i - Suc j)*x^j)) =
(\<Sum>i\<le>degree f. (\<Sum>j\<in>{i<..<Suc (degree f)}. coeff f j * u^(j-Suc i)) * x^i)

3. build the extractor: 
We build the polynomial q from a list of coefficients, that are computed 
from the coefficients of f and the known variable u to mirror the sum.

4. We show for every i\<le>degree f that the vertical sum is equal to the extracted q as 
sum 
In formulas :
(\<Sum>i\<le>degree f. (\<Sum>j\<in>{i<..<Suc (degree f)}. coeff f j * u^(j-Suc i)) * x^i) = poly extracted_q x

*)


definition coeffs_n :: "'q mod_ring poly \<Rightarrow> 'q mod_ring \<Rightarrow> 'q mod_ring list \<Rightarrow> nat \<Rightarrow> 'q mod_ring list"
  where "coeffs_n \<phi> u = (\<lambda>q_coeffs. \<lambda>n. map (\<lambda>(i::nat). (nth_default 0 q_coeffs i + poly.coeff \<phi> n * u ^ (n - Suc i))) [0..<n])"

lemma coeffs_n_length[simp]: "length (coeffs_n \<phi> u q_co n) = n"
  unfolding coeffs_n_def by fastforce

lemma coeffs_n_add_nth[simp]: "\<forall>i<n. coeffs_n \<phi> u l n ! i = nth_default 0 l i + poly.coeff \<phi> n * u ^ (n - Suc i)"
  unfolding coeffs_n_def by auto

definition extract_q_coeffs :: "'q mod_ring poly \<Rightarrow> 'q mod_ring \<Rightarrow> nat \<Rightarrow> 'q mod_ring list"
  where "extract_q_coeffs \<phi> u n = foldl (coeffs_n \<phi> u) [] [0..<Suc n]" 

lemma extract_q_coeffs_length[simp]: "length (extract_q_coeffs \<phi> u n) = n"
  unfolding extract_q_coeffs_def by simp

lemma extract_q_coeffs_nth_sum: "i<n \<Longrightarrow> foldl (coeffs_n \<phi> u) [] [0..<Suc n] ! i
                                        = (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i))"
proof (induction n arbitrary: i)
  case 0
  then show ?case by blast
next
  case (Suc n)
  then show ?case
  proof (cases "i<n")
    case True
    have "foldl (coeffs_n \<phi> u) [] [0..<Suc (Suc n)] 
      = map (\<lambda>i. nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i))
     [0..<Suc n]"
      unfolding coeffs_n_def by force
    then have "foldl (coeffs_n \<phi> u) [] [0..<Suc (Suc n)] ! i 
        = nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i)"
      by (metis (lifting) Suc.prems add_0 diff_zero nth_map_upt)
    also have "\<dots>=(\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i)"
      using Suc.IH[of i] by (simp add: True nth_default_def)
    also have "\<dots>=(\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i))"
    proof -
      have "\<forall>x y f. x<y \<longrightarrow> (\<Sum>j\<in>{x<..<y}. f j) + f y = (\<Sum>j\<in>{x<..<Suc y}. f j)"
        by (metis Suc_le_eq atLeastSucLessThan_greaterThanLessThan sum.atLeastLessThan_Suc)
      then show "(\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i) =
    (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i))" using Suc.prems by blast
    qed
    ultimately show ?thesis by argo
  next
    case False
    then have i_eq_n: "i=n" using Suc.prems by simp
    have "foldl (coeffs_n \<phi> u) [] [0..<Suc (Suc n)]
        = coeffs_n \<phi> u (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) (Suc n)" by simp
    also have "\<dots>=map (\<lambda>(i::nat). (nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i 
                       + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i))) [0..<Suc n]" 
      unfolding coeffs_n_def by blast 
    ultimately have "foldl (coeffs_n \<phi> u) [] [0..<Suc (Suc n)] ! i
                   = map (\<lambda>(i::nat). (nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i 
                       + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i))) [0..<Suc n] ! i"
      by argo
    also have "\<dots>= (nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i 
                       + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i))" 
      using Suc.prems calculation by auto
    also have "\<dots>=poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)"
      by (simp add: nth_default_eq_dflt_iff i_eq_n)
    also have "(\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) 
             = poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)"
    proof -
      have "{i<..<Suc (Suc n)} = {Suc n}"
      proof 
        show "{i<..<Suc (Suc n)} \<subseteq> {Suc n}"
          by (simp add: greaterThanLessThan_upt i_eq_n)
        show "{Suc n} \<subseteq> {i<..<Suc (Suc n)}"
          by (simp add: i_eq_n)
      qed
      then show "(\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) 
             = poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)"
        by simp
    qed
    ultimately show ?thesis by argo
  qed
qed

corollary extract_q_nth_sum: "i<n \<Longrightarrow> extract_q_coeffs \<phi> u n ! i = (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i))"
  unfolding extract_q_coeffs_def using extract_q_coeffs_nth_sum .

lemma lessThan_upTo_sum_extension:"i<n \<Longrightarrow> (\<Sum>j\<in>{i<..<n}. f j) + f n = (\<Sum>j\<in>{i<..<Suc n}. f j)"
proof (induction n)
  case 0
  then show ?case by fast
next
  case (Suc n)
  then show ?case
    by (metis Suc_leI atLeastSucLessThan_greaterThanLessThan sum.atLeastLessThan_Suc)
qed

lemma sum_horiz_to_vert: "n\<le>degree (\<phi>::'q mod_ring poly) \<Longrightarrow> (\<Sum>i\<le>n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) 
     = (\<Sum>i\<le>n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x^i)"
proof (induction n arbitrary: \<phi>)
  case 0
  have "(\<Sum>i\<le>0. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) = 0" by fastforce
  also have "(\<Sum>i\<le>0. (\<Sum>j\<in>{i<..<Suc 0}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) = 0"
    by (simp add: greaterThanLessThan_upt)
  ultimately show ?case by argo
next
  case (Suc n)
  have "(\<Sum>i\<le>Suc n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) 
      = (\<Sum>i\<le>n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) 
      + poly.coeff \<phi> (Suc n) * (\<Sum>j<(Suc n). u ^ (Suc n - Suc j) * x ^ j)" by auto
  also have "\<dots> = (\<Sum>i\<le>n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) 
                + poly.coeff \<phi> (Suc n) * (\<Sum>j<(Suc n). u ^ (Suc n - Suc j) * x ^ j)"
    using Suc.IH Suc.prems Suc_leD by presburger
  also have "\<dots>=(\<Sum>i\<le>n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) 
                + (\<Sum>j<(Suc n). poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc j) * x ^ j)"
    by (metis (mono_tags, lifting) mult.assoc mult_hom.hom_sum sum.cong)
  also have "\<dots>=(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) 
                + (\<Sum>j<Suc n. poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc j) * x ^ j)"
    using lessThan_Suc_atMost by presburger
  also have "\<dots>=(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i 
                + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i) * x ^ i)"
    by (simp add: sum.distrib)
  also have "\<dots>=(\<Sum>i<Suc n. ((\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i))* x ^ i)"
    by (simp add: distrib_left mult.commute)
  also have "\<dots>=(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)" 
  proof -
    have "\<forall>(i::nat)<Suc n. ((\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i))
                   = (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i))"
    proof 
      fix i 
      show "i < Suc n \<longrightarrow>
         (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i) =
         (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i))"
      proof 
      let ?f = "(\<lambda>j. poly.coeff \<phi> j * u ^ (j - Suc i))"
      assume asmp: "i < Suc n"
      then show "(\<Sum>j\<in>{i<..<Suc n}. ?f j) + ?f (Suc n) = (\<Sum>j\<in>{i<..<Suc (Suc n)}. ?f j)"
        using lessThan_upTo_sum_extension by blast
      qed
    qed
    then show "(\<Sum>i<Suc n. ((\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i)) * x ^ i) =
    (\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)"
      by fastforce
  qed
  also have "\<dots>=(\<Sum>i\<le>Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)"
  proof -
    have "(\<Sum>j\<in>{Suc n<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc (Suc n))) * x ^ (Suc n) = 0"
      by (simp add: greaterThanLessThan_upt)
    then have "(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)
              = (\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) 
              + (\<Sum>j\<in>{Suc n<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc (Suc n))) * x ^ (Suc n)"
      by force
    also have "\<dots>=(\<Sum>i\<le>Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)"
      by (simp add: lessThan_Suc_atMost)
    ultimately show "(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)
             = (\<Sum>i\<le>Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)"
      by argo
  qed
  ultimately show ?case using Suc.prems Suc_leD by argo
qed


definition extract_q :: "'q mod_ring poly \<Rightarrow> 'q mod_ring \<Rightarrow> nat \<Rightarrow> 'q mod_ring poly"
  where "extract_q \<phi> u n = Poly (extract_q_coeffs \<phi> u n)"


lemma pcoeffs_eq_ecoeffs: "i<n \<Longrightarrow> poly.coeff (extract_q \<phi> u n) i = extract_q_coeffs \<phi> u n ! i"
  unfolding extract_q_def 
proof -
  assume "i<n"
  then show "poly.coeff (Poly (extract_q_coeffs \<phi> u n)) i = extract_q_coeffs \<phi> u n ! i"
    by (simp add: nth_default_eq_dflt_iff nth_default_nth)
qed

lemma degree_q_le_\<phi>: "n\<le> degree \<phi> \<Longrightarrow> degree (extract_q \<phi> u n) \<le> n"
  unfolding extract_q_def
  by (metis degree_Poly extract_q_coeffs_length)
 
lemma sum_gr_deg: "(n::nat)>degree (q::'q mod_ring poly) \<Longrightarrow> (\<Sum>i<n. poly.coeff q i * x ^ i) 
                                               = (\<Sum>i\<le>degree q. poly.coeff q i * x ^ i)"
proof (induction n arbitrary: q)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases "degree q<n")
    case True
    then show ?thesis
      using Suc True coeff_eq_0 by fastforce
  next
    case False
    then have deg_q: "degree q = n" using Suc by linarith
    show ?thesis using deg_q lessThan_Suc_atMost by presburger
  qed
qed

lemma sum_split: "m\<le>n \<Longrightarrow> (\<Sum>i\<le>n. f i) = (\<Sum>i\<le>m. f i) + (\<Sum>i\<in>{m<..<Suc n}. f i)"
proof -
  assume "m\<le>n"
  then show "(\<Sum>i\<le>n. f i) = (\<Sum>i\<le>m. f i) + (\<Sum>i\<in>{m<..<Suc n}. f i)"
  proof (induction n arbitrary: m)
    case 0
    then show ?case
      using greaterThanLessThan_upt by fastforce
  next
    case (Suc n)
    then show ?case
      using greaterThanLessThan_upt
      by (metis Suc_le_mono atLeast0AtMost atLeastLessThanSuc_atLeastAtMost atLeastSucLessThan_greaterThanLessThan less_eq_nat.simps(1) sum.atLeastLessThan_concat)
  qed
qed


theorem f_eq_xu_extrqx: "\<forall>\<phi>::'q mod_ring poly. poly \<phi> x - poly \<phi> u = (x-u) * poly (extract_q \<phi> u (degree \<phi>)) x"
proof
  fix \<phi>::"'q  mod_ring poly"
  fix u x :: "'q mod_ring"
  show "poly \<phi> x - poly \<phi> u = (x-u) * poly (extract_q \<phi> u (degree \<phi>)) x"
  proof -
    let ?q_dirty ="(\<lambda>x. (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j)))"
    let ?q_vert  ="(\<lambda>x. (\<Sum>i\<le>degree \<phi>. (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x^i))"
    let ?q = "extract_q \<phi> u (degree \<phi>)"
    (*idee: über endl. Summen, see: poly_as_sum *)
    have "(\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * x ^ i) - (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * u ^ i) 
      = (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * (x ^ i - u ^ i))"
      by (simp add: sum_subtractf right_diff_distrib')
    also have "\<dots> = (\<Sum>i\<le>degree \<phi>. (x - u) * poly.coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j))"
      by (simp add: mult.assoc mult.left_commute power_diff_sumr2)
    also have "\<dots> = (x - u) * (?q_dirty x)" 
      by (metis (mono_tags, lifting) mult.assoc mult_hom.hom_sum sum.cong)
    also have "\<dots>= (x-u) * (?q_vert x)" using sum_horiz_to_vert by auto
    also have "?q_vert x = poly ?q x"
    proof -
      (*  connect degree \<phi> sum and degree q sum  *)
      have "(\<Sum>i\<le>degree \<phi>. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i) 
          = (\<Sum>i\<le>degree ?q. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i)"
      proof -
        have "degree ?q \<le> degree \<phi>" by (simp add: degree_q_le_\<phi>)
        also have "\<forall>n. n\<ge>degree ?q \<and> n\<le>degree \<phi> \<longrightarrow>  (\<Sum>i\<le>n. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i)
                                              = (\<Sum>i\<le>degree ?q. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i)"
        proof
          fix n
          show "n\<ge>degree ?q \<and> n\<le>degree \<phi> \<longrightarrow>  (\<Sum>i\<le>n. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i)
                                              = (\<Sum>i\<le>degree ?q. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i)"
          proof 
            let ?f = "nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>))"
            assume asmp: "n\<ge>degree ?q \<and> n\<le>degree \<phi>"
            have "\<forall>i>degree ?q. ?f i = 0"
              using coeff_eq_0 extract_q_def by fastforce
            then have "(\<Sum>i\<in>{degree ?q <..<Suc n}. ?f i * x^i) = 0"
              by fastforce
            also have "(\<Sum>i\<le>n. ?f i * x ^ i) = (\<Sum>i\<le>degree ?q. ?f i * x ^ i) + (\<Sum>i\<in>{degree ?q <..<Suc n}. ?f i * x^i)"
              using sum_split asmp by blast
            ultimately show "(\<Sum>i\<le>n. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x ^ i) 
                     = (\<Sum>i\<le>degree ?q. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x ^ i)"
              using asmp by auto
          qed
        qed
        ultimately show "(\<Sum>i\<le>degree \<phi> . nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i) 
                 = (\<Sum>i\<le>degree ?q. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i)"
          by blast
      qed
      also have "?q_vert x = (\<Sum>i\<le>degree \<phi>. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i)"
      proof -
        have "\<forall>i\<le>degree \<phi>. (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) 
                          = nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i"
        proof 
          fix i
          show "i \<le> degree \<phi> \<longrightarrow>
           (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) =
           nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i"
          proof 
            assume asmp: "i \<le> degree \<phi>"
            then show "(\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) =
              nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i"
            proof (cases "i<degree \<phi>")
              case True
              have "length (extract_q_coeffs \<phi> u (degree \<phi>)) = degree \<phi>" by simp
              then have "nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i 
                  = extract_q_coeffs \<phi> u (degree \<phi>) ! i"
                by (simp add: True nth_default_nth)
              then show ?thesis using True extract_q_nth_sum by presburger
            next
              case False
              then have "i=degree \<phi>" using asmp by fastforce
              have "length (extract_q_coeffs \<phi> u (degree \<phi>)) = degree \<phi>" by simp
              then have "nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i = 0"
                by (simp add: \<open>i = degree \<phi>\<close> nth_default_beyond)
              also have "(\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) 
                        = 0"  using False greaterThanLessThan_upt by auto
              ultimately show ?thesis by argo
            qed
          qed
        qed
        then show "?q_vert x = (\<Sum>i\<le>degree \<phi>. nth_default 0 (extract_q_coeffs \<phi> u (degree \<phi>)) i * x^i)"
          by force
      qed
      ultimately show "?q_vert x = poly ?q x" 
        unfolding extract_q_def by (simp add: poly_altdef)
    qed
    ultimately show "poly \<phi> x - poly \<phi> u = (x-u) * poly (extract_q \<phi> u (degree \<phi>)) x"
      by (simp add: poly_altdef)
  qed
qed

definition compute_\<psi> :: "'q qr \<Rightarrow> 'q mod_ring \<Rightarrow> 'q mod_ring poly"
  where "compute_\<psi> \<phi> u = extract_q (of_qr \<phi>) u (degree (of_qr \<phi>))"

lemma compute_\<psi>_deg: "degree (compute_\<psi> \<phi> u) \<le> degree (of_qr \<phi>)"
  by (simp add: compute_\<psi>_def degree_q_le_\<phi>)

corollary f_eq_xu_compute_qx: "\<forall>\<phi>::'q qr. poly (of_qr \<phi>) x - poly (of_qr \<phi>) u = (x-u) * poly (compute_\<psi> \<phi> u ) x"
  unfolding compute_\<psi>_def using f_eq_xu_extrqx by blast



subsubsection \<open>actual CreateWitness with compute_q: CreateWitness(PK, \<phi>, i) ==> (i, \<phi>(i), g^(\<psi>(\<alpha>)))
 where PK is Setup t \<alpha>\<close>

fun CreateWitness :: "'a list \<Rightarrow> 'q qr \<Rightarrow> 'q mod_ring \<Rightarrow> 'q mod_ring * 'q mod_ring * 'a" where 
  "CreateWitness PK \<phi> i = (i, poly (of_qr \<phi>) i, g_pow_PK_Prod PK (compute_\<psi> \<phi> i))"

lemma CreateWitness_correct: "degree (of_qr \<phi>) \<le>t \<Longrightarrow> CreateWitness (Setup \<alpha> t) \<phi> i = (i, poly (of_qr \<phi>) i, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (compute_\<psi> \<phi> i) \<alpha>))"
proof 
  assume asmpt: "degree (of_qr \<phi>) \<le>t"
  show "fst (CreateWitness (Setup \<alpha> t) \<phi> i) = fst (i, poly (of_qr \<phi>) i, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (compute_\<psi> \<phi> i) \<alpha>)"
    by force
  show "snd (CreateWitness (Setup \<alpha> t) \<phi> i) = snd (i, poly (of_qr \<phi>) i, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (compute_\<psi> \<phi> i) \<alpha>)"
  proof 
    show "fst (snd (CreateWitness (Setup \<alpha> t) \<phi> i)) = fst (snd (i, poly (of_qr \<phi>) i, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (compute_\<psi> \<phi> i) \<alpha>))"
      by force
    have "g_pow_PK_Prod (Setup \<alpha> t) (compute_\<psi> \<phi> i) =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (compute_\<psi> \<phi> i) \<alpha>"
    proof (rule g_pow_PK_Prod_correct)
      show "degree (compute_\<psi> \<phi> i) \<le> t"
        using asmpt compute_\<psi>_deg order.trans by blast
    qed
    then show "snd (snd (CreateWitness (Setup \<alpha> t) \<phi> i)) = snd (snd (i, poly (of_qr \<phi>) i, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (compute_\<psi> \<phi> i) \<alpha>))"
      by auto
  qed
qed

subsection \<open>VerifyEval(PK, C, i, \<phi>(i), w_i) ==> bool\<close>

fun div_in_grp (infixr "\<div>\<index>" 70)
  where "x \<div>\<index> y = x \<otimes>\<index> inv\<index> y"

fun pow_mod_ring_G\<^sub>T :: "'c \<Rightarrow>'q mod_ring \<Rightarrow> 'c" (infixr "^\<^bsub>G\<^sub>T\<^esub>" 75)
  where "x ^\<^bsub>G\<^sub>T\<^esub> q = x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring q)"

(*  Condition is: e(w_i,g^\<alpha>/g^i)e(g,g)^\<phi>(i) = e(C,g)  *)
fun VerifyEval :: "'a list \<Rightarrow> 'a \<Rightarrow> 'q mod_ring \<Rightarrow> 'q mod_ring \<Rightarrow> 'a \<Rightarrow> bool" where
  "VerifyEval PK C i \<phi>_of_i w_i = 
  (e w_i (PK!1  \<div>\<^bsub>G\<^sub>p\<^esub> (PK!0 ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e (PK!0) (PK!0)) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i) = e C (PK!0))"

(*  lemma on "why VerifyEval is correct", as described in the paper at the definition of VerifyEval  *)
lemma eq_on_e: "(e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (compute_\<psi> \<phi> i) \<alpha>))  (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) 
      \<otimes>\<^bsub>G\<^sub>T\<^esub> (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>)^\<^bsub>G\<^sub>T\<^esub> (poly (of_qr \<phi>) i) 
      = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha>)) \<^bold>g\<^bsub>G\<^sub>p\<^esub>"
proof -
  have e_in_carrier: "(e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ) \<in> carrier G\<^sub>T" using e_symmetric by blast
  have "e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (compute_\<psi> \<phi> i) \<alpha>) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly (of_qr \<phi>) i 
      = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (compute_\<psi> \<phi> i) \<alpha>) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha> - i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly (of_qr \<phi>) i"
    using mod_ring_pow_mult_inv_G\<^sub>p by force
  also have "\<dots>= (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ) ^\<^bsub>G\<^sub>T\<^esub> ((poly (compute_\<psi> \<phi> i) \<alpha>) * (\<alpha>-i))  \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly (of_qr \<phi>) i"
    by (simp add: e_bilinear)
  also have "\<dots>= (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ) ^\<^bsub>G\<^sub>T\<^esub> ((poly (compute_\<psi> \<phi> i) \<alpha>) * (\<alpha>-i) + poly (of_qr \<phi>) i)"
    using mod_ring_pow_mult_G\<^sub>T e_in_carrier by simp
  also have "\<dots>= (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ) ^\<^bsub>G\<^sub>T\<^esub> (poly (of_qr \<phi>) \<alpha>)"
    by (metis diff_add_cancel f_eq_xu_compute_qx mult.commute)
  also have "\<dots>= e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha>)) \<^bold>g\<^bsub>G\<^sub>p\<^esub>"
    by (simp add: e_linear_in_fst)
  finally show "e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (compute_\<psi> \<phi> i) \<alpha>) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly (of_qr \<phi>) i =
    e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (of_qr \<phi>) \<alpha>) \<^bold>g\<^bsub>G\<^sub>p\<^esub>"
    .
qed

lemma VerifyEval_correct: 
  assumes t_ge_2: "t\<ge>2"
  and deg_\<phi>_let: "degree (of_qr \<phi>) \<le> t"
  and PK: "PK = Setup \<alpha> t"
  and C: "C = Commit PK \<phi>"
  and Witness: "(i, \<phi>_of_i, w_i) = CreateWitness PK \<phi> i"
shows "VerifyEval PK C i \<phi>_of_i w_i"
proof -
  have "VerifyEval PK C i \<phi>_of_i w_i 
  = (e w_i (( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i) = e C \<^bold>g\<^bsub>G\<^sub>p\<^esub>)"
    using PK Setup_i t_ge_2 by force
  also have "\<dots> = (e w_i (( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i) 
                   = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha> )) \<^bold>g\<^bsub>G\<^sub>p\<^esub>)"
    using C Commit_correct PK VerifyEval.simps assms(2) by presburger
  also have "\<dots>= (e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (compute_\<psi> \<phi> i) \<alpha>)) (( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> (poly (of_qr \<phi>) i )) 
                   = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha> )) \<^bold>g\<^bsub>G\<^sub>p\<^esub>)"
    using CreateWitness_correct[OF deg_\<phi>_let, of \<alpha> i] Witness PK by force
  also have "\<dots>=True" using eq_on_e by fast
  finally show "VerifyEval PK C i \<phi>_of_i w_i" by blast
qed

section \<open>Soundness\<close>
  

subsection \<open>Polynomial Binding\<close>

(*  TODO delete die beiden lemmas *)
lemma "t_SDH G\<^sub>p = True" by (simp add: t_SDH_G\<^sub>p.t_SDH_axioms)
lemma "poly.coeff (Poly [1::nat,2]) 0 = 1"
  by simp     

lemma commit_eq_is_poly_diff_\<alpha>_eq_0: "degree (of_qr \<phi>) \<le> deg_t \<Longrightarrow> degree (of_qr \<phi>') \<le> deg_t \<Longrightarrow> 
  Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<deg_t+1]) \<phi> 
= Commit ( map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<deg_t+1]) \<phi>'
  \<longleftrightarrow> poly (of_qr \<phi> - of_qr \<phi>') \<alpha> = 0"
proof 
  assume deg_\<phi>: "degree (of_qr \<phi>) \<le> deg_t"
  assume deg_\<phi>': "degree (of_qr \<phi>') \<le> deg_t"
  assume commit_eq: "Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<deg_t + 1]) \<phi> = Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<deg_t + 1]) \<phi>'"
  have acc_\<phi>: "Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<deg_t + 1]) \<phi> =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha> )"
    by (metis Commit_correct Setup.simps deg_\<phi>)
  moreover have acc_\<phi>': "Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<deg_t + 1]) \<phi>' =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>') \<alpha> )"
    by (metis Commit_correct Setup.simps deg_\<phi>')
  ultimately show "(poly (of_qr \<phi> - of_qr \<phi>') \<alpha> = 0)"
    using pow_on_eq_card commit_eq by fastforce
next
  assume deg_\<phi>: "degree (of_qr \<phi>) \<le> deg_t"
  assume deg_\<phi>': "degree (of_qr \<phi>') \<le> deg_t"
  assume poly_eq_0: "poly (of_qr \<phi> - of_qr \<phi>') \<alpha> = 0"
  have acc_\<phi>: "Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<deg_t + 1]) \<phi> =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>) \<alpha> )"
    by (metis Commit_correct Setup.simps deg_\<phi>)
  moreover have acc_\<phi>': "Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<deg_t + 1]) \<phi>' =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (of_qr \<phi>') \<alpha> )"
    by (metis Commit_correct Setup.simps deg_\<phi>')
  ultimately show "Commit (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<deg_t + 1]) \<phi> = Commit (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<deg_t + 1]) \<phi>'" 
    using poly_eq_0 by fastforce 
qed

subsubsection \<open>Factorization of \<alpha> if poly (\<phi> - \<psi>) \<alpha> = 0\<close>

fun elimination_of_repeated_factors :: "'q mod_ring poly \<Rightarrow> 'q mod_ring poly list" where
  "elimination_of_repeated_factors f = (let u = gcd f (pderiv f) in 
    if u=1 then [u] else                         
      let v = Polynomial.divide_poly_inst.divide_poly f u;
          w = Polynomial.divide_poly_inst.divide_poly u (gcd u (v^(degree f)));
          z = w ^ (nat p)  \<comment>\<open>TODO should be 1/p\<close>
 in [z])"

lemma "monic (f::'q mod_ring poly) \<Longrightarrow> \<exists>ls. prod_list ls = f \<and> (\<forall>i. irreducible (ls!i))"
  sorry

declare [[show_types]]
lemma "(x::'q mod_ring)^y =  (x::'q mod_ring)^(y mod CARD ('q))"
proof -
  obtain y_qcard y_mod where y_split: "y=CARD ('q)*y_qcard + y_mod"
    by (metis mult_hom.hom_zero plus_nat.simps(1))
  then have "x^y = x^(CARD ('q)*y_qcard) * x^y_mod" using power_add by blast
  moreover have "x^(CARD ('q)*y_qcard) = 1" (*False*) sorry 
  moreover have "y_mod = y mod CARD ('q)" using y_split sorry
  ultimately show ?thesis by auto
qed

fun find_\<alpha>_square_free :: "'a \<Rightarrow> 'q mod_ring poly \<Rightarrow> 'q mod_ring" where
  "find_\<alpha>_square_free g_pow_\<alpha> \<phi> = (let (c, polys) = finite_field_factorization \<phi>;
    deg1_polys = filter (\<lambda>f. degree f = 1) polys;
    root_list = map (\<lambda>p. poly.coeff p 0) deg1_polys;
    \<alpha>_roots = filter (\<lambda>r. g_pow_\<alpha> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> r) root_list
in \<alpha>_roots!0)"

declare [[show_types]]
lemma poly_eq0_is_find_\<alpha>_eq_\<alpha>: "poly \<phi> \<alpha>=0 \<longleftrightarrow> find_\<alpha>_square_free (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = -\<alpha>"
proof 
  assume "poly \<phi> \<alpha> = 0"
  then show "find_\<alpha>_square_free (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = -\<alpha>"
    
    sorry
next 
  assume "find_\<alpha>_square_free (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = -\<alpha>"
  obtain c polys where "finite_field_factorization \<phi> = (c,polys)"
    by (metis prod.exhaust)
  moreover have "square_free \<phi>" sorry
  ultimately have "\<phi> = Polynomial.smult c (prod_list polys)"
    using finite_field_factorization_explicit by blast
  then show "poly \<phi> \<alpha> = 0"
    sorry
qed

definition bind_key_gen :: "('a list * 'a list) spmf"
 where 
  "bind_key_gen = do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'q mod_ring)^t)) [0..<deg_t+1];
    return_spmf (PK, PK) 
  }" 

definition bind_commit :: "'a list \<Rightarrow> 'q qr \<Rightarrow> ('a \<times> 'q qr) spmf"
where 
  "bind_commit PK \<phi> = do {
    let c = Commit PK \<phi>;
    return_spmf (c,\<phi>) 
  }"

definition bind_verify :: "'a list \<Rightarrow> 'q qr \<Rightarrow> 'a \<Rightarrow> 'q qr \<Rightarrow> bool"
where 
  "bind_verify PK \<phi> C _ = (C = Commit PK \<phi>)"

definition bind_valid_msg :: "'q qr \<Rightarrow> bool"
  where "bind_valid_msg \<phi> \<equiv> (degree (of_qr \<phi>) \<le> deg_t)"

sublocale bind_commit: abstract_commitment bind_key_gen bind_commit bind_verify bind_valid_msg .

(* "('a list, 'q qr, 'a, 'q qr)  bind_adversary \<Rightarrow> 'a t_SDH.adversary" *)
fun bind_reduction
  :: "('a list, 'q qr, 'a, 'q qr)  bind_adversary \<Rightarrow> 'a t_SDH.adversary"                     
where
  "bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>');
  let \<alpha> = find_\<alpha>_square_free (PK!1) (of_qr \<phi> - of_qr \<phi>');
  return_spmf (0::nat, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))}"

type_synonym 'grp poly_bind_adversary = "'grp list \<Rightarrow> (nat *'grp) spmf"

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

lemma "\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>' 
  \<and> (C = Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'q mod_ring)^t)) [0..<deg_t+1]) \<phi>) 
  \<and> (C = Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'q mod_ring)^t)) [0..<deg_t+1]) \<phi>') 
  \<longleftrightarrow> \<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>' \<and> poly (of_qr \<phi> - of_qr \<phi>') (of_int_mod_ring (int \<alpha>)::'q mod_ring) = 0"
proof 
  assume "\<phi> \<noteq> \<phi>' \<and>
    bind_valid_msg \<phi> \<and>
    bind_valid_msg \<phi>' \<and>
    C = Commit (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0..<deg_t + 1]) \<phi> \<and>
    C = Commit (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0..<deg_t + 1]) \<phi>'"
   then show "\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>' \<and> poly (of_qr \<phi> - of_qr \<phi>') (of_int_mod_ring (int \<alpha>)) = 0"
     unfolding bind_valid_msg_def using commit_eq_is_poly_diff_\<alpha>_eq_0 by blast
 next 
   assume "\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>' \<and> poly (of_qr \<phi> - of_qr \<phi>') (of_int_mod_ring (int \<alpha>)) = 0"
   then show " \<phi> \<noteq> \<phi>' \<and>
    bind_valid_msg \<phi> \<and>
    bind_valid_msg \<phi>' \<and>
    C = Commit (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0..<deg_t + 1]) \<phi> \<and>
    C = Commit (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring (int \<alpha>) ^ t) [0..<deg_t + 1]) \<phi>'"
     unfolding bind_valid_msg_def using commit_eq_is_poly_diff_\<alpha>_eq_0 sorry
 qed

lemma poly_bind_game_eq_t_SDH: "bind_commit.bind_game \<A> = t_SDH_G\<^sub>p.game deg_t (bind_reduction \<A>)"
proof -
  note [simp] = Let_def split_def
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'q mod_ring)^t)) [0..<deg_t+1])"
  have "bind_commit.bind_game \<A> = TRY do {
    (ck,vk) \<leftarrow> bind_key_gen;
    (c, m, d, m', d') \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf(m \<noteq> m' \<and> bind_valid_msg m \<and> bind_valid_msg m'); 
    let b = bind_verify vk m c d;
    let b' = bind_verify vk m' c d';
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True} ELSE return_spmf False" 
    by(simp add: abstract_commitment.bind_game_alt_def) 
  also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'q mod_ring)^t)) [0..<deg_t+1];
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> PK;
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>'); 
    _ :: unit \<leftarrow> assert_spmf ((C = Commit PK \<phi>) \<and> (C = Commit PK \<phi>'));
    return_spmf True} ELSE return_spmf False"
    by (simp add: bind_key_gen_def bind_verify_def)
 also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int \<alpha>)::'q mod_ring)^t)) [0..<deg_t+1];
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> PK;
  do {
    _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>'); 
    _ :: unit \<leftarrow> assert_spmf ((C = Commit PK \<phi>) \<and> (C = Commit PK \<phi>'));
    return_spmf True}
  } ELSE return_spmf False"
   by blast
  also have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
      _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>'); 
        _ :: unit \<leftarrow> assert_spmf ((C = Commit (?PK \<alpha>) \<phi>) \<and> (C = Commit (?PK \<alpha>) \<phi>'));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding split_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  moreover have "\<dots>= TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>' \<and> (C = Commit (?PK \<alpha>) \<phi>) \<and> (C = Commit (?PK \<alpha>) \<phi>'));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    using assert_anding by presburger 
  moreover have "\<dots>=TRY do {
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    TRY do {
    (C, \<phi>, d, \<phi>', d') \<leftarrow> \<A> (?PK \<alpha>);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>' \<and> poly (of_qr \<phi> - of_qr \<phi>') (of_int_mod_ring (int \<alpha>)::'q mod_ring) = 0);
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding bind_valid_msg_def using commit_eq_is_poly_diff_\<alpha>_eq_0  sorry
  (*  t_SDH reduction game  *)
    (*idea :
  verify \<phi> =C \<and> verify \<phi>'=C
  \<longleftrightarrow> poly (of_qr \<phi> - of_qr \<phi>') \<alpha> = 0 (commit_eq_is_poly_diff_\<alpha>_eq_0) (\<and> verify \<phi> =C \<and> verify \<phi>'=C)
  \<longleftrightarrow> find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> \<alpha>) (of_qr \<phi> - of_qr \<phi>') = \<alpha> (poly_eq0_is_find_\<alpha>_eq_\<alpha>) (\<and> verify \<phi> =C \<and> verify \<phi>'=C)
*)
  have "
  TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> (map (\<lambda>t'. \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (int \<alpha>^t')) [0..<deg_t+1]);
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>');
  let \<alpha>' = find_\<alpha>_square_free ((map (\<lambda>t'. \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (int \<alpha>^t')) [0..<deg_t+1])!1) (of_qr \<phi> - of_qr \<phi>');
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (1/((\<alpha>+0))) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>'));
    return_spmf (True) } ELSE return_spmf False
  = 
  TRY do { 
    \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
    (c, g) \<leftarrow> (bind_reduction \<A>) (map (\<lambda>t'. \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (int \<alpha>^t')) [0..<deg_t+1]);
    _::unit \<leftarrow> assert_spmf (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (1/((\<alpha>+c))) = g);
    return_spmf (True) } ELSE return_spmf False"
    by simp  
  moreover have "\<dots> = t_SDH_G\<^sub>p.game deg_t (bind_reduction \<A>)"
    by (simp add: t_SDH_G\<^sub>p.game_alt_def t_SDH_G\<^sub>p.game_def)
  ultimately show ?thesis sorry
qed

fun stronger_bind_reduction
  :: "('a list, 'q qr, 'a, 'q qr)  bind_adversary \<Rightarrow> 'a t_SDH.adversary"                     
where
  "stronger_bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> bind_valid_msg \<phi> \<and> bind_valid_msg \<phi>' \<and> (C=Commit PK \<phi>) \<and> (C=Commit PK \<phi>'));
  let \<alpha> = find_\<alpha>_square_free (PK!1) (of_qr \<phi> - of_qr \<phi>');
  return_spmf (0::nat, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))}"

lemma lossless_bind:"lossless_spmf (t_SDH_G\<^sub>p.game deg_t (bind_reduction \<A>))"
  using bind_commit.lossless_binding_game poly_bind_game_eq_t_SDH by auto

lemma "t_SDH_G\<^sub>p.advantage deg_t (stronger_bind_reduction \<A>) \<le> t_SDH_G\<^sub>p.advantage deg_t (bind_reduction \<A>)"
  unfolding t_SDH_G\<^sub>p.advantage_def stronger_bind_reduction.simps bind_reduction.simps t_SDH_G\<^sub>p.game_def sorry
  sorry

lemma poly_binding:"bind_commit.bind_advantage \<A> = t_SDH_G\<^sub>p.advantage deg_t (bind_reduction \<A>)"
  unfolding abstract_commitment.bind_advantage_def t_SDH_G\<^sub>p.advantage_def 
    using poly_bind_game_eq_t_SDH by simp

subsection \<open>Evaluation Binding\<close>

subsection \<open>Hiding\<close>

end 

end
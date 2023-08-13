theory KZG_Def

imports "CryptHOL.CryptHOL" "CryptHOL.Cyclic_Group" "CRYSTALS-Kyber.Kyber_spec" 

begin

locale crypto_primitives = 
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
deg_t_le_p: "deg_t \<le> p" 
\<comment>\<open>and t_SDH_GP: "t_SDH GP"\<close>
begin

abbreviation pow_mod_ring_G\<^sub>p :: "'a \<Rightarrow>'q mod_ring \<Rightarrow> 'a" (infixr "^\<^bsub>G\<^sub>p\<^esub>" 75)
  where "x ^\<^bsub>G\<^sub>p\<^esub> q \<equiv> x [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring q)"

abbreviation pow_mod_ring_G\<^sub>T :: "'c \<Rightarrow>'q mod_ring \<Rightarrow> 'c" (infixr "^\<^bsub>G\<^sub>T\<^esub>" 75)
  where "x ^\<^bsub>G\<^sub>T\<^esub> q \<equiv> x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring q)"

abbreviation div_in_grp (infixr "\<div>\<index>" 70)
  where "x \<div>\<index> y \<equiv> x \<otimes>\<index> inv\<index> y"

subsubsection \<open>mod_ring operations on pow of Gp\<close>

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
    finally show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)" by fastforce
  qed
  finally show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod p)" .
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
  finally show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>p\<^esub> inv\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a - b)" .
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
  finally show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a + b)" .
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
               = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a * b)" .
qed

subsubsection\<open>mod_ring operations on pow of GT\<close>

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
    finally show "g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
      using asmpt by fastforce
  qed
  finally show "g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod p)" .
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
  finally show "x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>T\<^esub> x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring b = x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring (a + b)" .
qed

subsubsection \<open>bilinearity operations for mod_ring elements\<close>

lemma e_linear_in_fst: 
  assumes "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
  shows "e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) (Q) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)"
proof -
  have "e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) Q = e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (1::'q mod_ring))" using assms by simp
  also have "... = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a*(1::'q mod_ring)))" using assms e_bilinear by fast
  also have "\<dots>=(e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" by simp
  finally show "e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a)) Q = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" .
qed

lemma e_linear_in_snd: 
assumes "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
shows "e (P) (Q [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)"
proof -
have "e P (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) = e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (1::'q mod_ring)) (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a)" using assms by simp
  also have "... = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring ((1::'q mod_ring)*a))" using assms e_bilinear by fast
  also have "\<dots>=(e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" by simp
  finally show "e P (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) = e P Q [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring a" .
qed

end

section \<open>KZG function definitions\<close>

locale KZG_Def = crypto_primitives
begin

text\<open>The definitions of the KZG functions are from the section 3.2 of the original paper 
"Constant-Size Commitments to Polynomials and Their Applications" and mirror the construction of 
PolyCommitDL.
I strongly recommend having the section 3.2 of the paper ready for look-up when trying to 
understand this formalization.\<close>

type_synonym 'q' sk = "'q' mod_ring"
type_synonym 'a' pk = "'a' list"

type_synonym 'e' polynomial = "'e' qr"
type_synonym 'a' commit = "'a'"

type_synonym 'e' eval_position = "'e' mod_ring"
type_synonym 'e' eval_value = "'e' mod_ring"
type_synonym 'a' eval_witness = "'a'"

subsection\<open>Setup: 
we do not compute the Groups for the bilinear pairing but assume them and compute 
a uniformly random secret key \<alpha> and from that the public key PK = (g, g^\<alpha>, ... , g^(\<alpha>^t) ).
Setup is a trusted Setup function, which generates the shared public key for both parties 
(prover and verifier).\<close>
definition Setup :: "nat \<Rightarrow> ('e sk \<times> 'a pk) spmf"
where 
  "Setup t = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x) in
    return_spmf (\<alpha>, map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<t+1]) 
  }" 

subsection\<open>Commit\<close>

text\<open>This function computes g^\<phi>(\<alpha>), given the by Setup generated public key. 
(\<alpha> being the from Setup generated private key)

The function is basically a Prod of public key!i ^ coeff \<phi> i, which computes g^\<phi>(a), given the 
public key:
\<Prod>[0...degree \<phi>]. PK!i^coeff \<phi> i 
= \<Prod>[0...degree \<phi>]. g^(\<alpha>^i)^coeff \<phi> i
= \<Prod>[0...degree \<phi>]. g^(coeff \<phi> i * \<alpha>^i)
= g^(\<Sum>[0...degree \<phi>]. coeff \<phi> i * \<alpha>^i)
= g^\<phi>(\<alpha>)
\<close>
fun g_pow_PK_Prod :: "'a list \<Rightarrow>'e mod_ring poly \<Rightarrow> 'a" where
  "g_pow_PK_Prod PK \<phi> = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!pk ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"

subsubsection\<open>actual Commit definition is basically computing g^\<phi>(a) from the public key\<close>
definition Commit :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> ('a commit) spmf"
where 
  "Commit PK \<phi> = do {
    return_spmf (g_pow_PK_Prod PK (of_qr \<phi>)) 
  }" 

subsection \<open>Open: opens the commitment\<close>
definition Open :: "'a pk \<Rightarrow> 'a commit \<Rightarrow> 'e polynomial \<Rightarrow> 'e polynomial spmf"
where 
  "Open PK C \<phi> = do {
    return_spmf \<phi> 
  }" 


subsection \<open>VerifyPoly: verify the commitment
Recomputes the commitment and checks the equality\<close>
definition VerifyPoly :: "'a pk \<Rightarrow> 'a commit \<Rightarrow> 'e polynomial \<Rightarrow> bool spmf"
where 
  "VerifyPoly PK C \<phi> = do {
    return_spmf (C = g_pow_PK_Prod PK (of_qr \<phi>)) 
  }" 

subsection \<open>CreateWitness: creates a witness for a commitment to an evaluation of a polynomial 
at position i\<close>

text\<open>To create a witness we have to compute \<psi> in \<phi> x - \<phi> u = (x-u) * \<psi> x\<close>

subsubsection \<open>extract \<psi> in \<phi> x - \<phi> u = (x-u) * \<psi> x\<close>
text \<open>Idea:
the polynomial \<phi> can be represented as a sum, hence:
\<phi> x - \<phi> u 
= (\<Sum>i\<le>degree \<phi>. coeff \<phi> i * x^i) - (\<Sum>i\<le>degree \<phi>. coeff \<phi> i * x^i)
= (x-u)(\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j)) 
(for the last step see the lemma power_diff_sumr2)
Hence: \<psi> x = (\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j))
However, to build a polynomial \<psi> in Isabelle, we need the individual coefficients for every power 
of x (i.e. bring the sum into a form of (\<Sum>i\<le>degree \<phi>. coeff_i*x^i) where coeff_i is the individual
coefficients for every power i of x. This translation is the main-purpose of the extractor function. 
The key idea is reordering the summation obtained from the power_diff_sumr2 lemma:

One can imagine the summation of power_diff_sumr2 to be horizontal, in the sense that it computes 
the coefficients from 0 to degree \<phi> = n, and adds (or could add) to each coefficient in every iteration:
0: 0 +
1: f1 +
2: f2*u + f2*x +
3: f3*u^2 + f3*u*x + f3*x^2
...
n: fn*u^(n-1) + ... fn*u^((n-1)-i)*x^i ...  + fn*x^(n-1)
we order it to compute the coefficients one by one (to compute vertical)
1: 0 + f1          + ... + fn*u^(n-1)         +
2: 0 + f2 * x      + ... + fn*u^((n-1)-1) * x +
...
n: 0 + fn * x^(n-1)

In formulas:
(\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j)) =
(\<Sum>i\<le>degree \<phi>. (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. coeff \<phi> j * u^(j-Suc i)) * x^i)
\<close>

text \<open>q_coeffs is a accumulator for the fold function.
fold coeffs_n creates a vertical summation by going through the power_diff_sumr2 and instead of 
adding the horizontal row, mapping it into a list, which is added onto the previous list of 
coefficients, hence summing the coefficients vertical in a list. Illustration:

0: [0                     ]  
=> map (+)
1: [f1                    ]
=> map(+)
2: [f1 + f2*u             , f2*x        ] 
=> map(+)
3: [f1 + f2*u + f3*u^2    , f2*x+f3*u*x , f3*x^2]
...
n: [f1 + ... + fn*u^(n-1) , ... , f(i-1)*x^i +...+fn*u^((n-1)-i)*x^i , ... , fn*x^(n-1)]

Hence the resulting list represents the vertical sum with coefficient i at position (i-1).
The correctness proof is to be found in the correctness theory KZG_correct.
\<close>
definition coeffs_n :: "'e mod_ring poly \<Rightarrow> 'e mod_ring \<Rightarrow> 'e mod_ring list \<Rightarrow> nat \<Rightarrow> 'e mod_ring list"
  where "coeffs_n \<phi> u = (\<lambda>q_coeffs. \<lambda>n. map (\<lambda>(i::nat). (nth_default 0 q_coeffs i + poly.coeff \<phi> n * u ^ (n - Suc i))) [0..<n])"

definition \<psi>_of :: "'e qr \<Rightarrow> 'e mod_ring \<Rightarrow> 'e mod_ring poly" 
  where "\<psi>_of \<phi> u = (let 
     \<psi>_coeffs = foldl (coeffs_n (of_qr \<phi>) u) [] [0..<Suc (degree (of_qr \<phi>))] \<comment>\<open>coefficients of \<psi>\<close>
    in Poly \<psi>_coeffs) \<comment>\<open>\<psi>\<close>"

subsubsection \<open>actual CreateWitness:
computes the evalutation at position i, \<phi>(i), and the witness g^\<psi>(\<alpha>)\<close>
definition CreateWitness :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> 'e eval_position 
  \<Rightarrow> ('e eval_position \<times> 'e eval_value \<times> 'a eval_witness) spmf"
where 
  "CreateWitness PK \<phi> i = do { 
    let \<phi>_of_i = poly (of_qr \<phi>) i; \<comment>\<open>\<phi>(i)\<close>
        \<psi> = \<psi>_of \<phi> i; \<comment>\<open>\<psi> in \<phi>(x) - \<phi>(i) = (x-i) * \<psi>(x)\<close>
        w_i = g_pow_PK_Prod PK \<psi> \<comment>\<open>g^\<psi>(\<alpha>)\<close>
    in
    return_spmf (i, \<phi>_of_i,w_i) \<comment>\<open>(i, \<phi>(i), g^\<psi>(\<alpha>))\<close>
  }" 


definition VerifyEval :: "'a pk \<Rightarrow> 'a commit \<Rightarrow> 'e eval_position \<Rightarrow> 'e eval_value \<Rightarrow> 'a eval_witness \<Rightarrow> bool spmf"
where 
  "VerifyEval PK C i \<phi>_of_i w_i =
    return_spmf (e w_i (PK!1  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> \<phi>_of_i) = e C \<^bold>g\<^bsub>G\<^sub>p\<^esub>) 
    \<comment>\<open>e(g^\<psi>(\<alpha>), g^\<alpha> / g^i) \<otimes> e(g,g)^\<phi>(i) = e(C, g)\<close>" 

thm Setup_def[simp]
thm Commit_def[simp]
thm Open_def[simp]
thm VerifyPoly_def[simp]
thm CreateWitness_def[simp]
thm VerifyEval_def[simp]

end

end
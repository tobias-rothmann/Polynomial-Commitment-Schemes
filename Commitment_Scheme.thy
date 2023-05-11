theory Commitment_Scheme

imports "CRYSTALS-Kyber.Kyber_spec" "CryptHOL.Cyclic_Group" 

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

(* 

mögliche Gruppen für bilinear pairing:
CryptHOL.cyclic_group
- kompatibilität mit Berlekamp-Zassenhaus?

 *)

section \<open>commitment scheme spec\<close>

locale commit_scheme_spec = 
fixes "type_a" :: "('a :: qr_spec) itself" 
  and d p::int
  and G\<^sub>p :: "'grp cyclic_group"
  and G\<^sub>T :: "'tgrp cyclic_group"
  and e :: "'grp \<Rightarrow> 'grp \<Rightarrow> 'tgrp"
assumes
p_gr_two: "p > 2" and
p_prime : "prime p" and

(* Bilinear Group Assumptions *)
CARD_grp: "int (order G\<^sub>p) = p" and
gen_G: "g = generator G\<^sub>p" and
bilinearity: "\<forall>a b::'a mod_ring . \<forall>P Q ::'grp.  e (P [^]\<^bsub>G\<^sub>p\<^esub> a) (Q [^]\<^bsub>G\<^sub>p\<^esub> b) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (a*b)" and 
(*$(\mathbb{Z}_p[x])^{<d}$ Assumptions*)
d_pos: "d > 0" and
CARD_a: "int (CARD('a :: qr_spec)) = p" and
qr_poly'_eq: "qr_poly' TYPE('a) = Polynomial.monom 1 (nat d) - 1"

begin

section \<open>q extractor : f(x)-f(u)=(x-u)q(x)\<close>

(*  Ein extractor für das Polynom q (extract_q) und der Beweis der Korrektheit 
    (f_eq_xu_extrqx). 
    Dokumentation folgt.
*)


definition coeffs_n :: "'a mod_ring poly \<Rightarrow> 'a mod_ring \<Rightarrow> 'a mod_ring list \<Rightarrow> nat \<Rightarrow> 'a mod_ring list"
  where "coeffs_n \<phi> u = (\<lambda>q_coeffs. \<lambda>n. map (\<lambda>(i::nat). (nth_default 0 q_coeffs i + poly.coeff \<phi> n * u ^ (n - Suc i))) [0..<n])"

lemma coeffs_n_length[simp]: "length (coeffs_n \<phi> u q_co n) = n"
  unfolding coeffs_n_def by fastforce

lemma coeffs_n_add_nth[simp]: "\<forall>i<n. coeffs_n \<phi> u l n ! i = nth_default 0 l i + poly.coeff \<phi> n * u ^ (n - Suc i)"
  unfolding coeffs_n_def by auto

lemma list_length_sum_ext[simp]: "length (xs@[x]) = Suc n \<Longrightarrow> (\<Sum>i<Suc n. (xs@[x])!i) = (\<Sum>i<n. xs!i) + x"
proof -
  assume asmp: "length (xs@[x]) = Suc n"
  then have xsn_eq_x: "(xs @ [x]) ! n = x" by auto
  have "(\<Sum>i<n. xs!i) = (\<Sum>i<n. (xs@[x])!i)"
  proof -
    have "length xs = n" using asmp by simp
    then have "\<forall>i<n. xs!i = (xs@[x])!i"
      by (simp add: append_Cons_nth_left)
    then show "(\<Sum>i<n. xs!i) = (\<Sum>i<n. (xs@[x])!i)" by auto
  qed
  then show "(\<Sum>i<Suc n. (xs@[x])!i) = (\<Sum>i<n. xs!i) + x"
    using xsn_eq_x by force    
qed

definition extract_q_coeffs :: "'a mod_ring poly \<Rightarrow> 'a mod_ring \<Rightarrow> nat \<Rightarrow> 'a mod_ring list"
  where "extract_q_coeffs \<phi> u n = foldl (coeffs_n \<phi> u) [] [0..<Suc n]" 

lemma fold_q_coeffs_length[simp]:"length (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) = n"
  by simp

corollary extract_q_coeffs_length[simp]: "length (extract_q_coeffs \<phi> u n) = n"
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

lemma sum_horiz_to_vert: "n\<le>degree (\<phi>::'a mod_ring poly) \<Longrightarrow> (\<Sum>i\<le>n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) 
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


definition extract_q :: "'a mod_ring poly \<Rightarrow> 'a mod_ring \<Rightarrow> nat \<Rightarrow> 'a mod_ring poly"
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
 
lemma sum_gr_deg: "(n::nat)>degree (q::'a mod_ring poly) \<Longrightarrow> (\<Sum>i<n. poly.coeff q i * x ^ i) 
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


theorem f_eq_xu_extrqx: "\<forall>\<phi>::'a :: qr_spec mod_ring poly. poly \<phi> x - poly \<phi> u = (x-u) * poly (extract_q \<phi> u (degree \<phi>)) x"
proof
  fix \<phi>::"'a :: qr_spec mod_ring poly"
  fix u x :: "'a mod_ring"
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



end

end
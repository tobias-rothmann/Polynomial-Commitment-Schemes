theory Commitment_Scheme

imports "CRYSTALS-Kyber.Kyber_spec"

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

locale commit_scheme_spec = 
fixes "type_a" :: "('a :: qr_spec) itself" 
  and d p::int
assumes
p_gr_two: "p > 2" and
p_prime : "prime p" and
d_pos: "d > 0" and
CARD_a: "int (CARD('a :: qr_spec)) = p" and
qr_poly'_eq: "qr_poly' TYPE('a) = Polynomial.monom 1 (nat d) - 1"

begin

(*
Vorsicht! der Einfachkeit halber, sind alle Polynome bis Grad einschließlich d-1 im Typen qr!

ein Element k aus (Z_p)[x]^{<d} : "k :: 'a qr"


*)

(*  \<exists>q. \<phi>(x)-\<phi>(u) = (x-u)*q(x)  *)
theorem f_eq_xu_qx: "\<forall>\<phi>::'a qr.  \<exists>q. poly (of_qr \<phi>) x - poly (of_qr \<phi>) u = (x-u) * q x"
proof
  fix \<phi>::"'a qr"
  fix u x :: "'a mod_ring"
  obtain d where d: "d= deg_qr (TYPE('a))" by blast
  obtain p_\<phi> where p_\<phi>: "(p_\<phi>::'a :: qr_spec mod_ring poly) = (of_qr \<phi>)" by blast
  show "\<exists>q. poly (of_qr \<phi>) x - poly (of_qr \<phi>) u = (x - u) * q x"
  proof 
    let ?q ="(\<lambda>x. (\<Sum>i\<le>degree p_\<phi>. poly.coeff p_\<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j)))"
    (*idee: über endl. Summen, see: poly_as_sum *)
    have "(\<Sum>i\<le>degree p_\<phi>. poly.coeff p_\<phi> i * x ^ i) - (\<Sum>i\<le>degree p_\<phi>. poly.coeff p_\<phi> i * u ^ i) 
      = (\<Sum>i\<le>degree p_\<phi>. poly.coeff p_\<phi> i * (x ^ i - u ^ i))"
      by (simp add: sum_subtractf right_diff_distrib')
    also have "\<dots> = (\<Sum>i\<le>degree p_\<phi>. (x - u) * poly.coeff p_\<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j))"
      by (simp add: mult.assoc mult.left_commute power_diff_sumr2)
    also have "\<dots> = (x - u) * (\<Sum>i\<le>degree p_\<phi>. poly.coeff p_\<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j))" 
      by (metis (no_types, lifting) mult_hom.hom_sum mult.assoc sum.cong)
    then show "poly (of_qr \<phi>) x - poly (of_qr \<phi>) u = (x - u) * ?q x"
      by (metis (no_types, lifting) calculation mult.commute p_\<phi> poly_as_sum sum.cong)
  qed
qed

end

end
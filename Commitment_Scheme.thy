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
(*                                   (of_qr q)::('a mod_ring poly)   *)
theorem f_eq_xu_qx: "\<forall>\<phi>::'a qr.  \<exists>q::'a qr. poly (of_qr \<phi>) x - poly (of_qr \<phi>) u = (x-u) * (poly (of_qr q) x)"
proof
  fix \<phi>
  fix u x
  show "\<exists>q. poly (of_qr \<phi>) x - poly (of_qr \<phi>) u = (x - u) * poly (of_qr q) x"
      sorry
qed

end

end
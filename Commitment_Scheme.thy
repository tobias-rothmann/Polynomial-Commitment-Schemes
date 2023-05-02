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

(* 

mögliche Gruppen für bilinear pairing:
CryptHOL.cyclic_group
- kompatibilität mit Berlekamp-Zassenhaus?

 *)

thm right_diff_distrib'

(*  \<exists>q. \<phi>(x)-\<phi>(u) = (x-u)*q(x) for q(x) as a Isabelle function, no poly   *)
theorem f_eq_xu_qx: "\<forall>\<phi>::'a :: qr_spec mod_ring poly.  \<exists>q. poly \<phi> x - poly \<phi> u = (x-u) * q x"
proof
  fix \<phi>::"'a :: qr_spec mod_ring poly"
  fix u x :: "'a mod_ring"
  obtain d where d: "d= deg_qr (TYPE('a))" by blast
  show "\<exists>q. poly \<phi> x - poly \<phi> u = (x - u) * q x"
  proof 
    let ?q ="(\<lambda>x. (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j)))"
    (*idee: über endl. Summen, see: poly_as_sum *)
    have "(\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * x ^ i) - (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * u ^ i) 
      = (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * (x ^ i - u ^ i))"
      by (simp add: sum_subtractf right_diff_distrib')
    also have "\<dots> = (\<Sum>i\<le>degree \<phi>. (x - u) * poly.coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j))"
      by (simp add: mult.assoc mult.left_commute power_diff_sumr2)
    also have "\<dots> = (x - u) * (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j))" 
      by (metis (mono_tags, lifting) mult.assoc mult_hom.hom_sum sum.cong)
    then show "poly \<phi> x - poly \<phi> u = (x - u) * ?q x"
      by (metis (no_types, lifting) calculation mult.commute poly_as_sum sum.cong)
  qed
qed

(*  change for poly    *)
lemma f_eq_xu_qx_for_qr: "\<forall>\<phi>::'a qr.  \<exists>q. poly (of_qr \<phi>) x - poly (of_qr \<phi>) u = (x-u) * q x"
  using f_eq_xu_qx by simp

(*  als nächstes der Verusch ein extractor für das Polynom q zu definieren (extract_q) und zu 
    beweisen (extract_q_correct).
    Es fehlt ein Schritt beid er Korrektheit mit (*TODO*) gekennzeichnet *)


definition zero_list :: "nat \<Rightarrow>'a mod_ring list"
  where "zero_list n = map (\<lambda>i. 0) [0..<Suc n]"

lemma "i<n \<Longrightarrow> zero_list n ! (i::nat) = 0"
  unfolding zero_list_def
  by (metis diff_zero less_Suc_eq nth_map_upt)


definition coeffs_n :: "'a mod_ring poly \<Rightarrow> 'a mod_ring \<Rightarrow> 'a mod_ring list \<Rightarrow> nat \<Rightarrow> 'a mod_ring list"
  where "coeffs_n \<phi> u = (\<lambda>q_coeffs. \<lambda>n. map (\<lambda>(i::nat). (q_coeffs!i + poly.coeff \<phi> n * u ^ (n - Suc i))) [0..<n])"

lemma coeffs_n_length[simp]: "length (coeffs_n \<phi> u q_co n) = n"
  unfolding coeffs_n_def by fastforce

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
  where "extract_q_coeffs \<phi> u n = foldl (coeffs_n \<phi> u) (zero_list (n)) [0..<Suc n]" 
   

lemma extract_q_coeffs_long_zerol: "\<forall>i>n. foldl (coeffs_n \<phi> u) (zero_list i) [0..<Suc n] 
                                  = extract_q_coeffs \<phi> u n"
  unfolding extract_q_coeffs_def coeffs_n_def
proof (induction n)
  case 0
  then show ?case by force
next
  case (Suc n)
  let ?mapf = "(\<lambda>q_coeffs n. map (\<lambda>i. q_coeffs ! i + poly.coeff \<phi> n * u ^ (n - Suc i)) [0..<n])"
  have "foldl ?mapf (zero_list (Suc (Suc n))) [0..<Suc (Suc n)]
      = ?mapf (foldl ?mapf (zero_list (Suc (Suc n))) [0..<Suc n]) (Suc n)"
    by force
  also have "\<dots> = ?mapf (foldl ?mapf (zero_list n) [0..<Suc n]) (Suc n)"
    using Suc lessI less_SucI by presburger
  also have "\<dots>=?mapf (extract_q_coeffs \<phi> u n) (Suc n)" 
    unfolding extract_q_coeffs_def coeffs_n_def by blast
  also have "\<dots>= map (\<lambda>i. (extract_q_coeffs \<phi> u n) ! i 
                      + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)) [0..<Suc n]"
    by blast
  show ?case  sorry
qed

lemma extract_q_coeffs_length[simp]: "length (extract_q_coeffs \<phi> u n) = n" 
  unfolding extract_q_coeffs_def coeffs_n_def by fastforce

definition extract_q :: "'a mod_ring poly \<Rightarrow> 'a mod_ring \<Rightarrow> nat \<Rightarrow> 'a mod_ring poly"
  where "extract_q \<phi> u n = Poly (extract_q_coeffs \<phi> u n)"


lemma pcoeffs_eq_ecoeffs[simp]: "i<n \<Longrightarrow> poly.coeff (extract_q \<phi> u n) i = extract_q_coeffs \<phi> u n ! i"
  unfolding extract_q_def 
proof -
  assume "i<n"
  then show "poly.coeff (Poly (extract_q_coeffs \<phi> u n)) i = extract_q_coeffs \<phi> u n ! i"
    by (simp add: nth_default_eq_dflt_iff nth_default_nth)
qed

lemma split_map_sum: "(\<Sum>i<n. map (\<lambda>i. f i + g i) l ! i * x^i) = (\<Sum>i<n. map (\<lambda>i. f i) l ! i * x^i) + (\<Sum>i<n. map (\<lambda>i. g i) l ! i * x^i)"
  sorry

lemma extract_q_correct: "n\<le>degree \<phi> \<Longrightarrow> (\<Sum>i\<le>n. poly.coeff (\<phi>::'a :: qr_spec mod_ring poly) i * (\<Sum>j<i. u^(i - Suc j) * x^j)) 
  = (\<Sum>i<n. poly.coeff (extract_q \<phi> u (n)) i * x^i)"
proof (induction n arbitrary: \<phi>)
  case 0
  then show ?case unfolding extract_q_def coeffs_n_def extract_q_coeffs_def by force
next
  case (Suc n)
  then have IH_valid: "(\<Sum>i\<le>n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) =
    (\<Sum>i<n. poly.coeff (extract_q \<phi> u n) i * x ^ i)" by force
  show ?case
  proof -
    have "(\<Sum>i\<le>Suc n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j))
        = (\<Sum>i\<le>n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j))
        + poly.coeff \<phi> (Suc n) * (\<Sum>j<(Suc n). u ^ ((Suc n) - Suc j) * x ^ j)"
      by fastforce
    also have "\<dots>= (\<Sum>i<n. poly.coeff (extract_q \<phi> u n) i * x ^ i)
                 + poly.coeff \<phi> (Suc n) * (\<Sum>j<(Suc n). u ^ ((Suc n) - Suc j) * x ^ j)"
      using IH_valid by presburger
    also have "\<dots>= (\<Sum>i<Suc n. poly.coeff (extract_q \<phi> u (Suc n)) i * x ^ i)"
    proof -
      have "(\<Sum>i<n. poly.coeff (extract_q \<phi> u n) i * x ^ i)
          + poly.coeff \<phi> (Suc n) * (\<Sum>j<Suc n. u ^ (Suc n - Suc j) * x ^ j) 
          = (\<Sum>i<n. extract_q_coeffs \<phi> u n ! i * x ^ i)
          + poly.coeff \<phi> (Suc n) * (\<Sum>j<Suc n. u ^ (Suc n - Suc j) * x ^ j)"
        by auto
      (*  TODO  *)
      also have "\<dots>= (\<Sum>i<Suc n. extract_q_coeffs \<phi> u (Suc n) ! i * x ^ i)"
        unfolding extract_q_coeffs_def coeffs_n_def
        sorry        
   (* alter Versuch der sich als ineffizient/nicht leichter/schwerer herausgestellt hat
    proof -
        (*prep*)
        let ?mapf = "(\<lambda>q_coeffs n. map (\<lambda>i. q_coeffs ! i + poly.coeff \<phi> n * u ^ (n - Suc i)) [0..<n])"
        let ?q_coeffs = "(foldl ?mapf (zero_list (Suc n)) [0..<Suc n])"
        have "foldl ?mapf (zero_list (Suc n)) [0..<Suc (Suc n)] 
            = ?mapf (foldl ?mapf (zero_list (Suc n)) [0..<Suc n]) (Suc n)" by fastforce
        also have "\<dots>=map (\<lambda>i. ?q_coeffs ! i + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)) [0..<Suc n]"
          by blast
        (*start*)
        have "(\<Sum>i<Suc n. (extract_q_coeffs \<phi> u (Suc n)) ! i * x^i) 
            = (\<Sum>i<Suc n. foldl ?mapf (zero_list (Suc n)) [0..<Suc (Suc n)] ! i * x^i)"
          unfolding extract_q_coeffs_def coeffs_n_def by blast
        have "\<dots>= (\<Sum>i<Suc n. map (\<lambda>i. ?q_coeffs ! i + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)) [0..<Suc n] ! i * x^i)" 
          by simp 
        have "\<dots>= (\<Sum>i<Suc n. map (\<lambda>i. ?q_coeffs ! i) [0..<Suc n] ! i * x^i)
                + (\<Sum>i<Suc n. map (\<lambda>i. poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)) [0..<Suc n] ! i * x^i)"
          using split_map_sum by fast
        
        
          (*first part same as \<Sum>i<n because i \<in> [0..<Suc n]*)
              (*TODO*)
        show "(\<Sum>i<n.
        foldl (\<lambda>q_coeffs n. map (\<lambda>i. q_coeffs ! i + poly.coeff \<phi> n * u ^ (n - Suc i)) [0..<n]) (zero_list n)
         [0..<Suc n] !
        i *
        x ^ i) +
    poly.coeff \<phi> (Suc n) * (\<Sum>j<Suc n. u ^ (Suc n - Suc j) * x ^ j) =
    (\<Sum>i<Suc n.
        foldl (\<lambda>q_coeffs n. map (\<lambda>i. q_coeffs ! i + poly.coeff \<phi> n * u ^ (n - Suc i)) [0..<n]) (zero_list (Suc n))
         [0..<Suc (Suc n)] !
        i *
        x ^ i)" sorry
      qed *)
      also have "(\<Sum>i<Suc n. extract_q_coeffs \<phi> u (Suc n) ! i * x ^ i) 
                = (\<Sum>i<Suc n. poly.coeff (extract_q \<phi> u (Suc n)) i * x ^ i)" by force
      ultimately show  "(\<Sum>i<n. poly.coeff (extract_q \<phi> u n) i * x ^ i)
           + poly.coeff \<phi> (Suc n) * (\<Sum>j<(Suc n). u ^ ((Suc n) - Suc j) * x ^ j)
           = (\<Sum>i<Suc n. poly.coeff (extract_q \<phi> u (Suc n)) i * x ^ i)"
        by argo       
    qed
    ultimately show "(\<Sum>i\<le>Suc n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j))
        = (\<Sum>i<Suc n. poly.coeff (extract_q \<phi> u (Suc n)) i * x ^ i)"
      by argo
  qed
qed
end

end
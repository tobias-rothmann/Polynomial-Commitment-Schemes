theory Factorization_Over_Finite_Field_Poly

imports "Berlekamp_Zassenhaus.Finite_Field_Factorization" KZG_Def
"Mason_Stothers.Mason_Stothers"

Root_Power_Poly_Finite_Field

begin

text \<open>Lemmas for polys (re-arrange placements!)\<close>

text \<open>A polynomial can be uniquely decomposed into a monic part and a coefficient 
(which is exactly the lead_coefficient).\<close>

lemma lead_coeff_is_coeff_for_monic_part:
assumes "f = smult a g" "monic g" "a\<noteq>0"
shows "lead_coeff f = (a::'a ::field)"
  using assms by auto

lemma decompose_monic_part_and_coefficient:
assumes "monic f" "monic g" "smult a f = smult b g" "a\<noteq>0" "b\<noteq>0"
shows "a=(b::'a ::field)" "f = g"
by (metis assms lead_coeff_is_coeff_for_monic_part)
   (metis assms lead_coeff_is_coeff_for_monic_part smult_eq_iff)

text \<open>If all factors are monic, the product is monic as well (ie the normalization is itself).\<close>
lemma normalize_prod_monics:
assumes "\<forall>x\<in>A. monic x"
shows "normalize (\<Prod>x\<in>A. x^(e x)) = (\<Prod>x\<in>A. x^(e x))"
by (simp add: assms monic_power monic_prod normalize_monic)


text \<open>Update function for multisets. 
Example: The factorization of a polynomial is represented by a multiset m where for every factor f
\<open>count m f\<close> represents the exponent of f in the polynomial. The polynomial can be represented
as $\Prod_{i\in \{1\dots n\}} f_i^{e_i}$, which translates to \<open>\<Prod>\<^sub># m\<close> (prod_mset) in Isabelle.\<close>

definition multiset_update :: "'a multiset \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a multiset" where 
"multiset_update fs f val = Abs_multiset ((count fs)(f:=val))"


text \<open>If we know the factorization of a polynomial, we can explicitly characterize the derivative 
of said polynomial.\<close>

lemma pderiv_exp_prod_monic: 
assumes "p = prod_mset fs" 
shows "pderiv p = (sum (\<lambda> fi. let ei = count fs fi in
    smult (of_nat ei) (pderiv fi) * fi^(ei-1) * prod (\<lambda> fj. fj^(count fs fj)) ((set_mset fs) - {fi})) 
    (set_mset fs))"
proof -
  have pderiv_fi: "pderiv (fi ^ count fs fi) = 
    smult (of_nat (count fs fi)) (pderiv fi * (fi ^ (count fs fi - Suc 0)))" 
    if "fi \<in># fs" for fi
  proof -
    obtain i where i: "Suc i = count fs fi" by (metis \<open>fi \<in># fs\<close> in_countE)
    show ?thesis unfolding i[symmetric] by (subst pderiv_power_Suc) (auto simp add: algebra_simps)
  qed
  show ?thesis unfolding assms prod_mset_multiplicity pderiv_prod sum_distrib_left Let_def
    by (rule sum.cong[OF refl]) (auto simp add: algebra_simps pderiv_fi)
qed


text \<open>Any element that divides a prime is either congruent to the prime (ie \<open>p dvd c\<close>) or 
a unit itself. Careful: this does not mean that $p=c$ since there could be another unit $u$ such 
that $p = u*c$.\<close>

lemma prime_factors_prime:
assumes "c dvd p" "prime p"
shows "is_unit c \<or> p dvd c"
using assms unfolding normalization_semidom_class.prime_def
by (meson prime_elemD2)

text \<open>A prime polynomial does not divide its derivative.\<close>
lemma not_dvd_pderiv_prime:
  fixes p :: "'a::{idom_divide,semidom_divide_unit_factor} poly"
  assumes "degree p \<noteq> 0" "pderiv p \<noteq> 0" "prime p"
  shows "\<not> p dvd pderiv p"
proof
  assume dvd: "p dvd pderiv p"
  then obtain q where p: "pderiv p = p * q"
    unfolding dvd_def by auto
  from dvd have le: "degree p \<le> degree (pderiv p)"
    by (simp add: assms dvd_imp_degree_le pderiv_eq_0_iff)
  from assms and this and degree_pderiv_le[of p]
    show False by auto
qed

text \<open>The derivative of a normalized linear polynomial is one. Similarly, we can say that
the derivative of a linear polynomial is exactly the lead coefficient.\<close>
lemma pderiv_linear:
fixes f:: "'a ::{idom_divide,semidom_divide_unit_factor,field,normalization_semidom} poly"
assumes "degree f = 1"
shows "pderiv (normalize f) = 1"
proof -
  obtain a b where ab: "f = [:b,a:]" "a\<noteq>0" using degree1_coeffs[OF assms] by blast
  then have lead_coeff: "lead_coeff f = a" unfolding ab by auto
  have lead_a: "unit_factor (lead_coeff f) = a" unfolding lead_coeff unit_factor_field by auto
  have "normalize f = [:b/a,1:]" unfolding normalize_poly_eq_map_poly lead_a by (simp add: ab)
  then show ?thesis by (simp add: pderiv_pCons) 
qed

lemma pderiv_linear':
fixes f:: "'a ::{idom_divide,semidom_divide_unit_factor,field,normalization_semidom} poly"
assumes "degree f = 1"
shows "pderiv f = [: lead_coeff f :]"
proof -
  obtain a b where ab: "f = [:b,a:]" "a\<noteq>0" using degree1_coeffs[OF assms] by blast
  then show ?thesis using ab by (simp add: pderiv_pCons) 
qed


text \<open>A prime polynomial has degree greater than zero. This is clear since any polynomial of 
degree 0 is constant and thus also a unit.\<close>

lemma prime_degree_gt_zero:
fixes p::"'a::{idom_divide,semidom_divide_unit_factor,field} poly"
assumes "prime p"
shows "degree p > 0"
proof (rule ccontr)
  assume "\<not> 0 < degree p"
  then have "degree p = 0" by auto
  moreover have "p\<noteq> 0" using assms unfolding normalization_semidom_class.prime_def prime_elem_def 
    by auto
  ultimately have "is_unit p" by (subst is_unit_iff_degree, auto)
  then show False using assms unfolding normalization_semidom_class.prime_def prime_elem_def 
    by auto
qed

(*Auswertungshomomorphismus mit poly *)
(*Hintereinanderausführen von Polynomen mit pcompose *)

text \<open>Polynomials can be split into a constant plus $x$ times the rest.\<close>

lemma pCons_add:
fixes a :: "'a::{comm_semiring_1}"
shows "pCons a p = [:a:] + Polynomial.monom 1 1 * p" 
proof (rule poly_eqI, goal_cases)
  case (1 n)
  have ?case if "n = 0" using that by (auto simp add: monom_Suc)
  moreover 
  have ?case if "n = Suc m" for m
  proof -
    have "poly.coeff p m = poly.coeff (Polynomial.monom 1 (Suc 0) * p) (Suc m)"
    unfolding coeff_monom_Suc by auto
    then show ?thesis using that by auto
  qed
  ultimately show ?case by (cases n, auto)
qed


text \<open>This lemma helps to reason that if a sum is zero, under some conditions we can follow that 
the summands must also be zero.\<close>
lemma one_summand_zero:
fixes a2::"'a ::field poly"
assumes "smult a1 a2 + b = 0" "a2\<noteq>0" "c dvd b" "\<not> c dvd a2"
shows "a1 = 0"
proof (rule ccontr)
  assume "a1\<noteq>0"
  then have "a2 = smult (- inverse a1) b" using assms(1)
    by (metis add.commute assms(3) assms(4) dvd_0_right dvd_add_triv_left_iff dvd_smult_cancel dvd_trans)
  then have "b dvd a2" using smult_dvd_cancel by (metis dvd_refl)
  then have "c dvd a2" using assms(3) by auto
  then show False using assms(4) by auto
qed








text \<open>Now, we are in the context of polynomials over finite fields of prime cardinality, 
ie. $\mathbb{F}_p[x]$ for $p$ prime.\<close>
context
assumes "SORT_CONSTRAINT('e::prime_card)"
begin


lemma CHAR_mod_ring [simp]: "CHAR('e mod_ring) = CARD('e)"
by (rule CHAR_eqI, simp, use of_nat_0_mod_ring_dvd in \<open>blast\<close>)


text \<open>The Frobenius homomorphism for polynomials.
$$f (x^p) = f^p$$ \<close>

lemma Frobenius_power_poly:
fixes p ::"'e mod_ring poly"
shows "pcompose p (Polynomial.monom 1 CARD('e)) = p^CARD('e)"
proof (induct p)
  case (pCons a p)
  have a: "[:a:] ^ CARD('e) = [:a:]" using fermat_theorem_power_poly[of a 1] by auto
  have monom: "Polynomial.monom 1 1 ^ CARD('e) = Polynomial.monom 1 CARD('e)"
    using x_pow_n by blast
  show ?case (is "?l = ?r") unfolding pcompose_pCons pCons(2)
    by (subst (2) pCons_add, subst add_power_poly_mod_ring, subst power_mult_distrib)
       (unfold a monom, simp)
qed auto

lemma irred_pderiv_nonzero:
assumes "irreducible (p::'e mod_ring poly)"
shows "pderiv p \<noteq> 0"
proof (rule ccontr)
  define e where "e = CARD('e)"
  have "e\<noteq>0" unfolding e_def by auto
  assume "\<not> pderiv p \<noteq> 0"
  then have ass: "pderiv p = 0" by auto
  then have "of_nat n * poly.coeff p n = 0" for n 
    using coeff_pderiv by (metis Num.of_nat_simps(1) arith_extra_simps(18) coeff_0 nth_item.cases)
  then have "e dvd n" if "poly.coeff p n \<noteq> 0" for n
    using of_nat_0_mod_ring_dvd that e_def by auto
  then have *: "poly.coeff p n = 0" if "0 < n mod e" for n using that
    using mod_greater_zero_iff_not_dvd by blast
  define h where "h = root_poly' e p"
  have "p = h \<circ>\<^sub>p (Polynomial.monom 1 e)" 
  proof (intro poly_eqI, goal_cases)
    case (1 n)
    have "n mod e < e" using \<open>e \<noteq> 0\<close> by force
    have left: "poly.coeff (h \<circ>\<^sub>p Polynomial.monom 1 e) n = 
      (if n mod e = 0 then poly.coeff h (n div e) else 0)"
    by (subst coeff_pcompose_monom[of _ e, symmetric]) (auto simp add: \<open>n mod e < e\<close>)
    show ?case unfolding left using * coeff_root_poly'[unfolded e_def[symmetric]] h_def
      e_def by auto
  qed 
  moreover have "h \<circ>\<^sub>p (Polynomial.monom 1 e) = h ^ e"
    unfolding e_def CARD_mod_ring by (rule Frobenius_power_poly)
  ultimately have "p = h^e" by auto
  then show False using assms
    by (metis Suc_pred' e_def irreducible_def is_unit_power_iff less_not_refl2 nontriv 
      numeral_nat(7) power.simps(2) zero_less_card_finite)
qed

lemma irred_deriv_coprime: 
fixes x ::"'e mod_ring poly"
assumes "irreducible x" "prime x"
shows"algebraic_semidom_class.coprime x (pderiv x)" 
unfolding coprime_def proof(safe, goal_cases)
  case (1 c)
  have "pderiv x \<noteq> 0" by (rule irred_pderiv_nonzero[OF assms(1)])
  have "degree x > degree (pderiv x)" by (metis \<open>prime x\<close> degree_0 degree_pderiv_less 
    is_unit_iff_degree not_prime_0 not_prime_unit zero_order(5))
  then have three: "degree x \<noteq> 0" by auto
  have "\<not> (x dvd pderiv x)" by (intro not_dvd_pderiv_prime)
    (auto simp add: \<open>prime x\<close> \<open>pderiv x \<noteq> 0\<close> three)
  then show "is_unit c" using prime_factors_prime[OF 1(1) \<open>prime x\<close>] 1 by auto
qed

end

end
theory Root_Power_Poly_Finite_Field

imports "Berlekamp_Zassenhaus.Finite_Field_Factorization" KZG_Def
"Mason_Stothers.Mason_Stothers"

begin
text \<open>Over the finite field $\mathbb{F}_p[x]$ where $p$ is prime, powers of polynomials 
behave very interestingly.
Especially for the $p$-th power of polynomials, the Frobenius Homomorphism ($(a+b)^p = a^p + b^p$) 
allows us to take the p-th power over the coefficients instead.
$$f = \sum_{i=0}^(\deg f) f_i x^i$$
$$f^p = \sum_{i=0}^(\deg f) f_i^p x^{i*p}$$

Similarly, the $p$-the root of a polynomial is easily described as
$$\sqrt{p}{f} = \sum_{i=0}^(\deg f) \sqrt{p}{f_i} x^{i\ div\ p}$$
where $f = g^p$ for some polynomial $g$.
\<close>


definition root_poly :: "( 'a :: zero \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "root_poly rt n p = Abs_poly (\<lambda>i. rt (poly.coeff p (i * n)))"

lemma coeff_root_poly [simp]: 
assumes "\<forall>\<^sub>\<infinity>na. rt (poly.coeff p (na * n)) = 0"
shows "poly.coeff (root_poly rt n p) i = rt (poly.coeff p (i * n))"
unfolding root_poly_def using assms by (subst Abs_poly_inverse, auto)


definition root_poly' :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> _ poly" where
  "root_poly' n p = Abs_poly (\<lambda>i. poly.coeff p (i * n))"

text \<open>We also need an executable version of the root poly function.\<close>
(*TODO
fun root_poly'_impl :: "nat \<Rightarrow> 'a :: zero list \<Rightarrow> 'a list" where
  "root_poly'_impl n [] = []" |
  "root_poly'_impl n (c#cs) = (if n dvd (length cs + 1) 
      then c#root_poly'_impl n cs else root_poly'_impl n cs)"

lemma root_poly'_code [code]:
  "coeffs (root_poly' n p) = root_poly'_impl n (coeffs p)"
unfolding root_poly'_impl_def sorry
*)


text \<open>For prime cardinality of the finite field, we get the following lemmas.\<close>
context
assumes "SORT_CONSTRAINT('e::prime_card)"
begin


lemma coeff_of_power[simp]:
fixes y :: "'e mod_ring poly"
shows "poly.coeff (y ^ CARD('e)) (i * CARD('e)) = poly.coeff y i"
by (subst poly_power_card_as_sum_of_monoms, subst coeff_sum) (auto intro: le_degree)


lemma root_poly'_power:
  fixes p :: "'e mod_ring poly"
  assumes "is_nth_power CARD('e) p"
  shows   "root_poly' CARD('e) p ^ CARD('e) = p"
proof -
  obtain y where p: "p = y ^ CARD('e)" using assms unfolding is_nth_power_def by auto
  show ?thesis unfolding p root_poly'_def by(auto simp add: coeff_inverse)
qed


lemma coeff_root_poly':
assumes  "CARD('e) dvd n" 
shows "poly.coeff p n = poly.coeff (root_poly' CARD('e) p) (n div CARD('e))"
proof -
  let ?A = "{x. poly.coeff p (x * CARD('e)) \<noteq> 0}"
  let ?f = "(\<lambda>x. if CARD('e) dvd x then x div CARD('e) else degree p + 1)"
  have card: "degree p < CARD('e) + degree p * CARD('e)" 
  by (metis add_gr_0 arithmetic_simps(79) bot_nat_0.not_eq_extremum 
    linordered_comm_semiring_strict_class.comm_mult_strict_left_mono nontriv trans_less_add2 
    zero_less_card_finite)
  have "?f -` ?A \<subseteq> {x. poly.coeff p x \<noteq> 0}" using coeff_eq_0[OF card] by auto
  then have f1: "finite (?f -` ?A)" if "finite {x. poly.coeff p x \<noteq> 0}"
    using finite_subset that by blast 
  have surj: "surj ?f"
    by (smt (verit) div_mult_self1_is_m dvd_triv_left surjI zero_less_card_finite)
  have "\<forall>\<^sub>\<infinity>n. poly.coeff p (n * CARD('e)) = 0" using MOST_coeff_eq_0[of p] 
    unfolding MOST_iff_cofinite by (intro finite_vimageD[of ?f ?A]) (use f1 surj in \<open>auto\<close>)
 then show ?thesis unfolding root_poly'_def by (subst Abs_poly_inverse) (use assms in \<open>auto\<close>)
qed

lemma root_poly'_power': 
fixes p :: "'e mod_ring poly"
shows "root_poly' (CARD('e)) (p^(CARD('e))) = p"
proof -
  have is_power: "is_nth_power CARD('e) (p^CARD('e))" by auto
  have "(root_poly' CARD('e) (p^CARD('e)))^CARD('e) = p^CARD('e)" 
    using root_poly'_power[OF is_power] by auto
  then show ?thesis by (metis coeff_of_power poly_eq_iff)
qed

(*
definition root_poly' :: "'e mod_ring poly \<Rightarrow> 'e mod_ring poly" where
  "root_poly' = root_poly (\<lambda>_ x. x) CARD('e)"
*)


end

end
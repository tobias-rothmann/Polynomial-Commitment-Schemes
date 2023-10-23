theory Root_Power_Poly_Finite_Field

imports "Berlekamp_Zassenhaus.Finite_Field_Factorization" 
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

lemma coeff_root_poly' [simp]:
assumes "n>1"
shows "poly.coeff (root_poly' n p) i = poly.coeff p (i * n)"
proof -
  let ?A = "{x. poly.coeff p (x * n) \<noteq> 0}"
  let ?f = "(\<lambda>x. if n dvd x then x div n else degree p + 1)"
  have card: "degree p < n + degree p * n" using assms by (simp add: add_strict_increasing)
  have "?f -` ?A \<subseteq> {x. poly.coeff p x \<noteq> 0}" using coeff_eq_0[OF card] by auto
  then have f1: "finite (?f -` ?A)" if "finite {x. poly.coeff p x \<noteq> 0}"
    using finite_subset that by blast 
  have surj: "surj ?f"
  by (smt (verit, best) Groups.mult_ac(2) arith_simps(62) card dvd_triv_left mult_Suc_right 
    nonzero_mult_div_cancel_left not_less0 surj_def)
  have "\<forall>\<^sub>\<infinity>m. poly.coeff p (m * n) = 0" using MOST_coeff_eq_0[of p] 
    unfolding MOST_iff_cofinite by (intro finite_vimageD[of ?f ?A]) (use f1 surj in \<open>auto\<close>)
 then show ?thesis unfolding root_poly'_def by (subst Abs_poly_inverse)(auto)
qed

lemma root_poly'_0 [simp]: "root_poly' n 0 = 0" 
unfolding root_poly'_def using zero_poly.abs_eq by auto

text \<open>We also need an executable version of the root poly function.\<close>
fun root_poly'_impl :: "nat \<Rightarrow> 'a :: zero list \<Rightarrow> 'a list" where
  "root_poly'_impl n [] = []" |
  "root_poly'_impl n (c # cs) = (if n dvd length cs
      then c#(root_poly'_impl n cs) else root_poly'_impl n cs)"

lemma length_root_poly'_impl_null:
"length (root_poly'_impl n []) = 0"
by auto

lemma length_root_poly'_impl:
assumes "n>1"
shows"length (root_poly'_impl n cs) = 
  (if n dvd length cs then length cs div n else Suc (length cs div n))" 
by (induct cs) (auto simp add: div_Suc)

lemma root_poly'_imple_one_elem:
assumes "n>1"
shows "root_poly'_impl n [a] = [a]"
by auto

lemma root_poly'_impl_nth_length:
assumes "n>1" "m*n < length cs"
shows "(root_poly'_impl n cs) ! (length (root_poly'_impl n cs) - Suc m) = cs ! (length cs - Suc (m*n))"
using assms(2) proof (induct cs)
  case Nil
  then show ?case by auto
next
  case (Cons a cs)
  have "(a # root_poly'_impl n cs) ! (length (root_poly'_impl n cs) - m) =
    (a # cs) ! (length cs - m * n)" if "n dvd length cs" using that Cons assms(1)
    by (smt (verit, best) Suc_mult_cancel1 bot_nat_0.not_eq_extremum diff_Suc_eq_diff_pred 
      diff_commute diff_mult_distrib dvd_div_mult_self length_root_poly'_impl mult.commute 
      nat_neq_iff nonzero_mult_div_cancel_right not_less_eq nth_Cons_0 nth_Cons_pos zero_less_diff)
  moreover have "root_poly'_impl n cs ! (length (root_poly'_impl n cs) - Suc m) =
    (a # cs) ! (length cs - m * n)" if "\<not> n dvd length cs" 
  proof -
    have not_eq: "length cs \<noteq> m*n" using that by auto
    then have less: "m * n < length cs" using Cons(2) by auto
    have "\<not> length cs - m * n = 0" 
    proof (rule ccontr)
      assume "\<not> length cs - m * n \<noteq> 0" 
      then have "length cs \<le> m*n" by simp
      then show False using Cons not_eq by auto
    qed
    then show ?thesis unfolding Cons(1)[OF less] nth_Cons' using that assms by auto
  qed
  ultimately show ?case by auto
qed

lemma root_poly'_impl_nth:
assumes "n>1" "m < length (root_poly'_impl n cs)"
shows "(root_poly'_impl n cs) ! m = cs ! (length cs - Suc ((length (root_poly'_impl n cs) - Suc m)*n))"
proof -
  let ?l = "length (root_poly'_impl n cs)"
  have ass: "(length (root_poly'_impl n cs) - Suc m)*n < length cs" using assms 
  by (smt (verit, ccfv_threshold) diff_less div_mult_self_is_m dvd_triv_right length_root_poly'_impl 
    less_Suc_eq_le less_eq_div_iff_mult_less_eq nless_le order_le_less_trans zero_less_Suc)
  have *: "?l - Suc (?l - Suc m) = m" by (subst Suc_diff_Suc[OF \<open>m<?l\<close>], intro diff_diff_cancel) 
    (use assms(2) in \<open>auto\<close>)
  show ?thesis unfolding root_poly'_impl_nth_length[OF assms(1) ass, symmetric] unfolding * by auto
qed

text \<open>Correctness of code implementation.\<close>
(*Lemma for [code]*)
lemma root_poly'_code:
assumes "n>1"
shows "coeffs (root_poly' n p) = strip_while ((=) 0) (rev (root_poly'_impl n (rev (coeffs p))))"
proof (rule coeffs_eqI, goal_cases)
  case (1 m)
  have *: "poly.coeff (root_poly' n p) m = poly.coeff p (m*n)" by (rule coeff_root_poly'[OF assms])
  have p0: ?case if "p =0" using that by auto

  have nth: "rev (root_poly'_impl n (rev (coeffs p))) ! m = poly.coeff p (m*n)" 
    if "m*n < length (coeffs p)" "p\<noteq>0" using that 
  proof -
    have one: "m < length (root_poly'_impl n (rev (coeffs p)))" 
    by (smt (verit, best) One_nat_def Suc_lessD assms div_less_iff_less_mult div_mult_self_is_m 
      dvdE length_rev length_root_poly'_impl mult.commute not_less_eq that(1))
    have two: "m * n < length (rev (coeffs p))" using that by auto
    have three: "length (rev (coeffs p)) - Suc (m * n) < length (coeffs p)" using that(1) by auto
    have index: "length (coeffs p) - Suc (length (rev (coeffs p)) - Suc (m * n)) = m*n"
      by (simp add: Suc_diff_Suc order_less_imp_le that(1))
    show ?thesis by (subst rev_nth[OF one], subst root_poly'_impl_nth_length[OF \<open>1<n\<close> two], 
      subst rev_nth[OF three], subst index, intro nth_coeffs_coeff) (use that in \<open>auto\<close>)
  qed

  have not_p0: ?case if "p\<noteq>0" unfolding * nth_default_strip_while_dflt
  unfolding nth_default_def proof (split if_splits, safe, goal_cases)
    case 1
    then have mn_len: "m*n < length (coeffs p)"
    by (smt (verit) assms div_less_iff_less_mult div_mult_self_is_m dvd_triv_right length_rev 
      length_root_poly'_impl less_numeral_extra(1) linorder_neqE_nat not_less_eq order_less_not_sym 
      order_less_trans)
    then show ?case using nth[OF mn_len that, symmetric] 1 by auto
  next
    case 2
    then have mn_len: "m*n \<ge> length (coeffs p)"
    by (smt (verit, ccfv_SIG) assms div_less_iff_less_mult dvd_div_mult_self length_rev 
      length_root_poly'_impl less_numeral_extra(1) linorder_not_le nat_neq_iff not_less_eq 
      order_less_trans)
    then show ?case using that by (simp add: coeff_eq_0 length_coeffs_degree)
  qed

  show ?case by (cases "p =0")(use p0 not_p0 in \<open>auto\<close>)
qed auto





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


lemma coeff_root_poly'_CARD_e:
assumes  "CARD('e) dvd n" 
shows "poly.coeff p n = poly.coeff (root_poly' CARD('e) p) (n div CARD('e))"
proof -
  let ?A = "{x. poly.coeff p (x * CARD('e)) \<noteq> 0}"
  let ?f = "(\<lambda>x. if CARD('e) dvd x then x div CARD('e) else degree p + 1)"
  have card: "degree p < CARD('e) + degree p * CARD('e)"
  by (metis One_nat_def Suc_lessI antisym_conv3 less_add_same_cancel2 less_zeroE 
    n_less_n_mult_m nat_mult_1_right pos_add_strict zero_less_card_finite)
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
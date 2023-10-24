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

(* remastered version by Manuel Eberl *)

lift_definition root_poly' :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> 'a poly" is
  "\<lambda>n p i. if n = 0 then p i else p (i * n)"
proof goal_cases
  case (1 n f)
  show ?case
  proof (cases "n > 0")
    case True
    from 1 obtain N where N: "f i = 0" if "i \<ge> N" for i
      using cofinite_eq_sequentially eventually_sequentially by auto
    have "f (i * n) = 0" if "i \<ge> N" for i
    proof (rule N)
      show "N \<le> i * n"
        using that True 
        by (metis One_nat_def Suc_leI le_trans mult.right_neutral mult_le_mono2)
    qed
    thus ?thesis using True
      unfolding cofinite_eq_sequentially eventually_sequentially by auto
  qed (use 1 in auto)
qed

lemma coeff_root_poly' [simp]:
  assumes "n > 0"
  shows "poly.coeff (root_poly' n p) i = poly.coeff p (i * n)"
  using assms by transfer auto

lemma root_poly'_0 [simp]: "root_poly' n 0 = 0"
  by transfer auto

lemma root_poly'_0_left [simp]: "root_poly' 0 p = p"
  by transfer auto

lemma degree_root_poly'_le:
  assumes "n > 0"
  shows   "degree (root_poly' n p) \<le> degree p div n"
proof (intro degree_le allI impI)
  fix i assume "degree p div n < i"
  hence "i * n > degree p"
    using assms div_less_iff_less_mult by blast
  thus "coeff (root_poly' n p) i = 0"
    using assms by (simp add: coeff_eq_0)
qed




text \<open>We also need an executable version of the root poly function.\<close>
(* The executable version is thanks to Manuel Eberl *)

fun take_every :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take_every _ [] = []"
| "take_every n (x # xs) = x # take_every n (drop (n - 1) xs)"

lemma take_every_0 [simp]: "take_every 0 xs = xs"
  by (induction xs) auto

lemma take_every_1 [simp]: "take_every (Suc 0) xs = xs"
  by (induction xs) auto

lemma int_length_take_every: "n > 0 \<Longrightarrow> int (length (take_every n xs)) = ceiling (length xs / n)"
proof (induction n xs rule: take_every.induct)
  case (2 n x xs)
  show ?case
  proof (cases "Suc (length xs) \<ge> n")
    case True
    thus ?thesis using 2
      by (auto simp: dvd_imp_le of_nat_diff diff_divide_distrib split: if_splits)
  next
    case False
    hence "\<lceil>(1 + real (length xs)) / real n\<rceil> = 1"
      by (intro ceiling_unique) auto
    thus ?thesis using False
      by auto
  qed
qed auto

lemma length_take_every:
  "n > 0 \<Longrightarrow> length (take_every n xs) = nat (ceiling (length xs / n))"
  using int_length_take_every[of n xs] by simp

lemma take_every_nth [simp]:
  "n > 0 \<Longrightarrow> i < length (take_every n xs) \<Longrightarrow> take_every n xs ! i = xs ! (n * i)"
proof (induction n xs arbitrary: i rule: take_every.induct)
  case (2 n x xs i)
  show ?case
  proof (cases i)
    case (Suc j)
    have "n - Suc 0 \<le> length xs"
      using Suc "2.prems" nat_le_linear by force
    hence "drop (n - Suc 0) xs ! (n * j) = xs ! (n - 1 + n * j)"
      using Suc by (subst nth_drop) auto
    also have "n - 1 + n * j = n + n * j - 1"
      using \<open>n > 0\<close> by linarith
    finally show ?thesis
      using "2.IH"[of j] "2.prems" Suc by simp
  qed auto
qed auto

lemma coeffs_eq_strip_whileI:
  assumes "\<And>i. i < length xs \<Longrightarrow> coeff p i = xs ! i"
  assumes "p \<noteq> 0 \<Longrightarrow> length xs > degree p"
  shows   "coeffs p = strip_while ((=) 0) xs"
proof (rule coeffs_eqI)
  fix n :: nat
  show "coeff p n = nth_default 0 (strip_while ((=) 0) xs) n"
    using assms
    by (metis coeff_0 coeff_Poly_eq coeffs_Poly le_degree nth_default_coeffs_eq 
      nth_default_eq_dflt_iff nth_default_nth order_le_less_trans)
qed auto

lemma root_poly'_code [code]:
  "coeffs (root_poly' n p) = (if n = 0 then coeffs p else strip_while ((=) 0) (take_every n (coeffs p)))"
     (is "_ = If _ _ ?rhs")
proof (cases "n = 0 \<or> p = 0")
  case False
  hence "n > 0" "p \<noteq> 0"
    by auto
  have "coeffs (root_poly' n p) = ?rhs"
  proof (rule coeffs_eq_strip_whileI)
    fix i
    show "coeff (root_poly' n p) i = take_every n (coeffs p) ! i"
      if i: "i < length (take_every n (coeffs p))" for i
    proof -
      note \<open>i < length (take_every n (coeffs p))\<close>
      also have "length (take_every n (coeffs p)) = nat \<lceil>(degree p + 1) / real n\<rceil>"
        using False by (simp add: length_take_every length_coeffs)
      finally have "i < real (degree p + 1) / real n"
        by linarith
      hence "real i * real n < real (degree p + 1)"
        using False by (simp add: field_simps)
      hence "i * n \<le> degree p"
        unfolding of_nat_mult [symmetric] by linarith
      hence "coeffs p ! (i * n) = coeff p (i * n)"
        using False by (intro coeffs_nth) (auto simp: length_take_every)
      thus ?thesis using False i
        by (auto simp: nth_default_def nth_strip_while mult.commute)
    qed
  next
    assume nz: "root_poly' n p \<noteq> 0"
    have "degree (root_poly' n p) \<le> degree p div n"
      by (rule degree_root_poly'_le) fact
    also have "\<dots> < nat \<lceil>(real (degree p) + 1) / real n\<rceil>"
      using \<open>n > 0\<close>
      by (metis div_less_iff_less_mult linorder_not_le nat_le_real_less of_nat_0_less_iff
                of_nat_ceiling of_nat_mult pos_less_divide_eq)
    also have "\<dots> = length (take_every n (coeffs p))"
      using \<open>n > 0\<close> \<open>p \<noteq> 0\<close> by (simp add: length_take_every length_coeffs add_ac)
    finally show "length (take_every n (coeffs p)) > degree (root_poly' n p)"
      by - simp_all
  qed
  thus ?thesis
    using False by metis
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
 then show ?thesis by (simp add: assms)
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



end

end
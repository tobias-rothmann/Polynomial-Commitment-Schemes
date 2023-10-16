theory Find_Root

imports "Berlekamp_Zassenhaus.Finite_Field_Factorization" KZG_Def
"Mason_Stothers.Mason_Stothers"

begin


definition root_poly :: "( 'a :: zero \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "root_poly rt n p = Abs_poly (\<lambda>i. rt (poly.coeff p (i * n)))"

lemma coeff_root_poly [simp]: 
assumes "\<forall>\<^sub>\<infinity>na. rt (poly.coeff p (na * n)) = 0"
shows "poly.coeff (root_poly rt n p) i = rt (poly.coeff p (i * n))"
unfolding root_poly_def using assms by (subst Abs_poly_inverse, auto)


definition root_poly' :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> _ poly" where
  "root_poly' n p = Abs_poly (\<lambda>i. poly.coeff p (i * n))"


(*TODO
fun root_poly'_impl :: "nat \<Rightarrow> 'a :: zero list \<Rightarrow> 'a list" where
  "root_poly'_impl n [] = []" |
  "root_poly'_impl n (c#cs) = (if n dvd (length cs + 1) 
      then c#root_poly'_impl n cs else root_poly'_impl n cs)"

lemma root_poly'_code [code]:
  "coeffs (root_poly' n p) = root_poly'_impl n (coeffs p)"
unfolding root_poly'_impl_def sorry
*)

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

(*
definition root_poly' :: "'e mod_ring poly \<Rightarrow> 'e mod_ring poly" where
  "root_poly' = root_poly (\<lambda>_ x. x) CARD('e)"
*)

lemma CHAR_mod_ring [simp]: "CHAR('e mod_ring) = CARD('e)"
by (rule CHAR_eqI, simp, use of_nat_0_mod_ring_dvd in \<open>blast\<close>)



text \<open>Lemmas for polys (re-arrange placements!)\<close>

lemma lead_coeff_is_coeff_for_monic_part:
assumes "f = smult a g" "monic g" "a\<noteq>0"
shows "lead_coeff f = (a::'a ::field)"
  using assms by auto

lemma decompose_monic_part_and_coefficient:
assumes "monic f" "monic g" "smult a f = smult b g" "a\<noteq>0" "b\<noteq>0"
shows "a=(b::'a ::field)" "f = g"
by (metis assms lead_coeff_is_coeff_for_monic_part)
   (metis assms lead_coeff_is_coeff_for_monic_part smult_eq_iff)

definition multiset_update :: "'a multiset \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a multiset" where 
"multiset_update fs f val = Abs_multiset ((count fs)(f:=val))"

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


lemma normalize_prod_monics:
assumes "\<forall>x\<in>A. monic x"
shows "normalize (\<Prod>x\<in>A. x^(e x)) = (\<Prod>x\<in>A. x^(e x))"
by (simp add: assms monic_power monic_prod normalize_monic)

lemma all_summands_zero:
assumes "sum f A = 0" "\<forall>y z. (y\<in>A \<and> z\<in>A \<and> y\<noteq>z \<longrightarrow> f y \<noteq> f z)" "x\<in>A"
shows "f x = 0"
using assms  oops


lemma prime_factors_prime:
assumes "c dvd p" "prime p"
shows "is_unit c \<or> p dvd c"
using assms unfolding normalization_semidom_class.prime_def
by (meson prime_elemD2)


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
    show ?case unfolding left using * coeff_root_poly'[unfolded e_def[symmetric]] h_def by auto
  qed 
  moreover have "h \<circ>\<^sub>p (Polynomial.monom 1 e) = h ^ e"
    unfolding e_def CARD_mod_ring by (rule Frobenius_power_poly)
  ultimately have "p = h^e" by auto
  then show False using assms
    by (metis Suc_pred' e_def irreducible_def is_unit_power_iff less_not_refl2 nontriv 
      numeral_nat(7) power.simps(2) zero_less_card_finite)
qed

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

(*
lemma dvd_prod_mset:
assumes "\<And>x::'e mod_ring poly. x\<in># fs \<Longrightarrow> (irreducible x \<and> monic x)" "e dvd \<Prod>\<^sub># fs"
shows "\<exists>es. (es \<subseteq># fs \<and> e = \<Prod>\<^sub># es)"
proof -
  have "monic (\<Prod>\<^sub># fs)" sorry
  have "monic e" sorry
using assms proof (induct fs rule: multiset_induct)
  case empty

  then show ?case apply auto sorry
next
case (add x M)
then show ?case sorry
qed


proof -
  obtain g where "e*g = \<Prod>\<^sub># fs" using assms by fastforce
  then have "e = (\<Prod>\<^sub># fs) div g" 
(*
  by (metis assms(1) mult_zero_right nonzero_mult_div_cancel_right not_prime_0 prod_mset_zero_iff) *)
  then have "e = (\<Prod>fi\<in># fs. (fi^(count fs fi) div g))"  sorry
  
  then show ?thesis
qed*)





term normalize

definition aux ::"'e mod_ring poly \<Rightarrow> _" where
  "aux f = (if degree f = 0 then None else (let
     f_mono = normalize f;
     p = CARD ('e);
     u = gcd f_mono (pderiv f_mono);
     n = degree f
  in (if u = 1 then None else let
    v = f_mono div u;
    w = u div gcd u (v^n);
    z = root_poly' p w
    in Some (v, z)
  )
))"


lemma square_free_part_of_correct_aux:
  assumes "aux f = Some (v, z)"                                
  shows   "radical f = v * radical z"
          "squarefree v"
          "z ^ CARD('e) dvd f"
          (* "prime_factors f = prime_factors v \<union> prime_factors z" (* alt. form of "radical f = v * radical z"; probably unnecessary *)*)
proof -
  define fm where "fm = normalize f"
  define p where "p = CARD('e)"
  define u where "u = gcd fm (pderiv fm)"
  define n where "n = degree f"
  define w where "w = u div (gcd u (v^n))"

  have [simp]: "degree f \<noteq> 0" using assms unfolding aux_def by (metis not_None_eq)
  have [simp]: "degree f > 0" using assms unfolding aux_def by (metis gr0I not_None_eq)
  have [simp]: "u \<noteq> 1" using assms unfolding aux_def 
    by (smt (verit, del_insts) fm_def option.simps(3) u_def)

  define fac where "fac = prime_factorization fm"
  define fac_set where "fac_set = prime_factors fm"

  define ex where "ex = (\<lambda>p. multiplicity p fm)"

  define P1 where "P1 = {f\<in>fac_set. \<not> p dvd ex f}"
  define P2 where "P2 = {f\<in>fac_set. p dvd ex f}"



  have [simp]: "fac_set \<noteq> {}" unfolding fac_set_def
  by (metis \<open>0 < degree f\<close> degree_0 degree_1 degree_normalize fm_def nat_less_le prod_mset.empty 
    prod_mset_prime_factorization_weak set_mset_eq_empty_iff)
  have "fac_set = P1 \<union> P2" unfolding P1_def P2_def by auto
  have [simp]: "P1 \<inter> P2 = {}" unfolding P1_def P2_def by auto
  have [simp]: "finite fac_set" "finite P1" "finite P2" unfolding P1_def P2_def fac_set_def by auto
  
  have fac_set_monic[simp]: "monic x" if "x\<in>fac_set" for x 
    by (metis fac_set_def in_prime_factors_iff 
    monic_normalize normalize_prime that zero_not_in_prime_factors)

  have nonzero[simp]: "fj \<noteq> 0" if "fj\<in> fac_set" for fj 
    using fac_set_def that zero_not_in_prime_factors by blast

  have nonzero_deriv[simp]: "pderiv fj \<noteq> 0" if "fj\<in> fac_set" for fj by (intro irred_pderiv_nonzero)
      (use that fac_set_def in_prime_factors_imp_prime in \<open>auto\<close>)

  have P1_ex_nonzero: "of_nat (ex x) \<noteq> (0:: 'e mod_ring)" if "x\<in>P1" for x 
    using that unfolding P1_def ex_def p_def using of_nat_0_mod_ring_dvd by auto
  
  have deriv_coprime: "algebraic_semidom_class.coprime x (pderiv x)" 
    if "x\<in>fac_set" for x using irred_deriv_coprime that 
    using fac_set_def in_prime_factors_imp_prime by auto

  have f_fac: "fm = prod_mset fac"
  by (metis \<open>0 < degree f\<close> bot_nat_0.extremum_strict degree_0 fac_def fm_def in_prime_factors_iff 
    normalize_eq_0_iff normalize_prime normalized_prod_msetI prod_mset_prime_factorization_weak)

  have fm_P1_P2: "fm = (\<Prod>fj\<in>P1. fj^(ex fj)) * (\<Prod>fj\<in>P2. fj^(ex fj))"
  proof -
    have *: "fm = (\<Prod>fj\<in>fac_set. fj^(ex fj))" unfolding f_fac unfolding fac_def fac_set_def
    by (smt (verit, best) count_prime_factorization_prime ex_def in_prime_factors_imp_prime 
      prod.cong prod_mset_multiplicity)
    show ?thesis unfolding * using \<open>fac_set = P1 \<union> P2\<close>
    prod.union_disjoint[OF \<open>finite P1\<close> \<open>finite P2\<close> \<open>P1\<inter>P2={}\<close>] by blast
  qed

  let ?deriv = "(\<lambda>y. Polynomial.smult (of_nat (ex y)) (pderiv y * y ^ (ex y - Suc 0) *
                (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj)))"

  let ?deriv_monic = "(\<lambda>y. pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj))"

  have pderiv_fm: "pderiv fm = (\<Sum>f\<in>fac_set. ?deriv f)"
  unfolding pderiv_exp_prod_monic[OF f_fac] Let_def fac_set_def fac_def ex_def 
    count_prime_factorization by (intro sum.cong, simp) 
    (smt (verit) DiffD1 One_nat_def in_prime_factors_iff mult_smult_left prod.cong)

  have sumP2_deriv_zero: "(\<Sum>f\<in>P2. ?deriv f) = 0" 
  unfolding P2_def p_def by (intro sum.neutral, auto)

  have pderiv_fm': "pderiv fm = (\<Sum>f\<in>P1. ?deriv f)" 
    by (subst pderiv_fm, subst (2) \<open>fac_set = P1 \<union> P2\<close>, 
        subst sum.union_disjoint[OF _ _ \<open>P1 \<inter> P2 = {}\<close>]) 
       (use sumP2_deriv_zero in \<open>auto\<close>)

  let ?deriv_P1 = "(\<lambda>y. Polynomial.smult (of_nat (ex y)) (pderiv y * y ^ (ex y - Suc 0) *
                (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)))"

  have pderiv_fm'': "pderiv fm = (\<Prod>f\<in>P2. f^ex f) * (\<Sum>x\<in>P1. ?deriv_P1 x)"
  proof (subst pderiv_fm', subst sum_distrib_left, intro sum.cong, simp, goal_cases)
    case (1 x)
    have *: "fac_set -{x} = P2 \<union> (P1-{x})" unfolding \<open>fac_set = P1 \<union> P2\<close> 
      using 1 \<open>P1 \<inter> P2 = {}\<close> by blast
    have **: "P2 \<inter> (P1 - {x}) = {}" using 1 \<open>P1 \<inter> P2 = {}\<close> by blast
    have "(\<Prod>fj\<in>fac_set - {x}. fj ^ ex fj) = (\<Prod>f\<in>P2. f ^ ex f) * (\<Prod>fj\<in>P1 - {x}. fj ^ ex fj)"
      unfolding * by (intro prod.union_disjoint, auto simp add: **)
    then show ?case by (auto simp add: algebra_simps)
  qed 
  
(* no!  have "\<not> x dvd (\<Sum>x\<in>P1. ?deriv_P1 x)" if "x\<in>P2" for x sorry *)
  
  have P1_P2_coprime: "algebraic_semidom_class.coprime x (\<Prod>f\<in>P2. f^ex f)" if "x\<in>P1" for x
  by (smt (verit) P1_def P2_def as_ufd.prime_elem_iff_irreducible fac_set_def 
    in_prime_factors_imp_prime irreducible_dvd_prod mem_Collect_eq 
    normalization_semidom_class.prime_def prime_dvd_power prime_imp_coprime primes_dvd_imp_eq that)

  have P1_ex_P2_coprime: "algebraic_semidom_class.coprime (x^ex x) (\<Prod>f\<in>P2. f^ex f)" if "x\<in>P1" for x
    using P1_P2_coprime by (simp add: that)

  have ex_power_not_dvd: "\<not> y^ex y dvd ?deriv_monic y" if "y\<in>fac_set" for y
  proof (rule ccontr, safe)
    assume "y^ex y dvd ?deriv_monic y"
    then have "y * (y^(ex y-1)) dvd (pderiv y * (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj)) * (y^(ex y-1))"
    by (metis (no_types, lifting) count_prime_factorization_prime ex_def fac_set_def 
      in_prime_factors_imp_prime more_arith_simps(11) mult.commute not_in_iff numeral_nat(7) 
      power_eq_if that)
    then have *: "y dvd pderiv y * (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj)"
     unfolding dvd_mult_cancel_right dvd_smult_cancel by auto
    then have "y dvd (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj)" 
      using deriv_coprime[THEN coprime_dvd_mult_right_iff] \<open>y\<in>fac_set\<close> by auto
    then obtain fj where fj_def: "y dvd fj ^ ex fj" "fj\<in>fac_set - {y}" using prime_dvd_prod_iff
      by (metis (no_types, lifting) \<open>finite fac_set\<close> \<open>y \<in> fac_set\<close> fac_set_def finite_Diff 
      in_prime_factors_iff)
    then have "y dvd fj" using prime_dvd_power
      by (metis fac_set_def in_prime_factors_imp_prime that)
    then have "coprime y fj" using fj_def(2)
    by (metis DiffD1 DiffD2 fac_set_monic that coprime_iff_coprime 
      fac_set_def in_prime_factors_iff insertI1 is_unit_left_imp_coprime poly_dvd_antisym 
      prime_factors_prime) 
    then show False by (metis \<open>y dvd fj\<close> coprimeE dvd_refl fac_set_def in_prime_factors_imp_prime 
      not_prime_unit that)
  qed

  have P1_ex_power_not_dvd: "\<not> y^ex y dvd ?deriv y" if "y\<in>P1" for y
  proof (rule ccontr)
    assume ass: "\<not> \<not> y^ex y dvd ?deriv y"
    have "y^ex y dvd ?deriv_monic y"
      using P1_ex_nonzero ass dvd_smult_iff that by blast
    then show False using ex_power_not_dvd that unfolding P1_def by auto
  qed

  have P1_ex_power_not_dvd': "\<not> y^ex y dvd ?deriv_P1 y" if "y\<in>P1" for y
  proof (rule ccontr)
    assume "\<not> \<not> y^ex y dvd ?deriv_P1 y" 
    then have ass: "y^ex y dvd pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)"
      using P1_ex_nonzero dvd_smult_iff that by blast
    then have "y * (y^(ex y-1)) dvd (pderiv y * (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)) * (y^(ex y-1))"
    by (metis (no_types, lifting) Num.of_nat_simps(1) P1_ex_nonzero more_arith_simps(11) 
      mult.commute numeral_nat(7) power_eq_if that)
    then have *: "y dvd pderiv y * (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)"
     unfolding dvd_mult_cancel_right dvd_smult_cancel by auto
    then have "y dvd (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)" 
      using deriv_coprime[THEN coprime_dvd_mult_right_iff] \<open>y\<in>P1\<close> \<open>fac_set = P1 \<union> P2\<close> by blast
    then obtain fj where fj_def: "y dvd fj ^ ex fj" "fj\<in>P1 - {y}" using prime_dvd_prod_iff
    by (metis (no_types, lifting) P1_def \<open>finite P1\<close> \<open>y \<in> P1\<close> fac_set_def finite_Diff 
      in_prime_factors_iff mem_Collect_eq)
    then have "y dvd fj" using prime_dvd_power
      by (metis UnCI \<open>fac_set = P1 \<union> P2\<close> fac_set_def in_prime_factors_iff that)
    then have "coprime y fj" using fj_def(2) 
    by (metis (no_types, lifting) DiffD1 DiffD2 P1_def coprime_iff_coprime fac_set_def 
      fac_set_monic in_prime_factors_iff is_unit_left_imp_coprime mem_Collect_eq poly_dvd_antisym 
      prime_factors_prime singletonI that)
    then show False 
    by (metis UnCI \<open>fac_set = P1 \<union> P2\<close> \<open>y dvd fj\<close> coprime_absorb_left coprime_iff_coprime 
      fac_set_def in_prime_factors_iff not_prime_unit that)
  qed

  have deriv_different:"?deriv x \<noteq> ?deriv y" if "x\<in>P1" "y\<in>P1" "x\<noteq>y" for x y
  proof -
    have "pderiv y\<noteq> 0" using \<open>y\<in>P1\<close> unfolding P1_def by auto
    have "y^ex y dvd ?deriv x" using that 
      by (intro dvd_smult,intro dvd_mult, intro dvd_prodI) (auto simp add: P1_def)
    moreover have "\<not> y^ex y dvd ?deriv y" using P1_ex_power_not_dvd \<open>y\<in>P1\<close> by auto
    ultimately show ?thesis by auto
  qed

  have "fm \<noteq> 0" using \<open>degree f > 0\<close> f_fac fac_def fm_def by auto

  have pderiv0_p_dvd_count: "p dvd ex fj" if "fj\<in>fac_set" "pderiv fm = 0" for fj
  proof -
    have "(\<Sum>f\<in>fac_set. ?deriv f) = 0" using pderiv_fm \<open>pderiv fm = 0\<close> by auto
    then have zero:"?deriv fj + (\<Sum>f\<in>fac_set-{fj}. ?deriv f) = 0"
      by (metis (no_types, lifting) \<open>finite fac_set\<close> sum.remove that(1))
    have nonzero: "pderiv fj * fj ^ (ex fj - Suc 0) * (\<Prod>fj\<in>fac_set - {fj}. fj ^ ex fj) \<noteq> 0"
      by (intro no_zero_divisors, use that in \<open>auto\<close>)
    have dvd: "fj ^ ex fj dvd (\<Sum>f\<in>fac_set - {fj}. ?deriv f)" 
      by (intro dvd_sum,intro dvd_smult,intro dvd_mult) 
         (use \<open>finite fac_set\<close> that(1) in \<open>blast\<close>)
    have nondvd: "\<not> fj ^ ex fj dvd pderiv fj * fj ^ (ex fj - Suc 0) * 
      (\<Prod>fj\<in>fac_set - {fj}. fj ^ ex fj)"
    using ex_power_not_dvd[OF \<open>fj\<in>fac_set\<close>] by auto
    have "of_nat (ex fj) = (0::'e mod_ring)" by (rule one_summand_zero[OF zero nonzero dvd nondvd])
    then show ?thesis using of_nat_0_mod_ring_dvd p_def by blast
  qed


  have mult_fm[simp]: "count fac x = ex x" if "x\<in>fac_set" for x 
  by (metis count_prime_factorization ex_def fac_def fac_set_def in_prime_factors_imp_prime that)

  have mult_deriv1: "multiplicity x (pderiv fm) = ex x - 1"  
    if "x\<in>P1" "pderiv fm \<noteq> 0" for x
  proof (subst multiplicity_eq_Max[OF that(2)])
    show "\<not> is_unit x" using that(1) using P1_def fac_set_def not_prime_unit by blast
    then have fin: "finite {n. x ^ n dvd pderiv fm}"
      using is_unit_iff_infinite_divisor_powers that(2) by blast 
    show "Max {n. x ^ n dvd pderiv fm} = ex x - 1" 
    proof (subst Max_eq_iff, goal_cases)
      case 2 then show ?case by (metis empty_Collect_eq one_dvd power_0)
    next
      case 3
      have dvd: "x ^(ex x-1) dvd pderiv fm" unfolding pderiv_fm' by(intro dvd_sum)
        (metis (no_types, lifting) One_nat_def P1_def P1_ex_nonzero \<open>finite fac_set\<close> \<open>x \<in> P1\<close> 
        dvd_mult dvd_mult2 dvd_prod dvd_smult dvd_triv_right finite_Diff insert_Diff 
        insert_iff mem_Collect_eq power_eq_if semiring_1_class.of_nat_simps(1))
      have not :"\<not> x^ex x dvd pderiv fm"
      proof (rule ccontr,safe)
        assume ass: "x ^ ex x dvd pderiv fm"
        have coprime: "algebraic_semidom_class.coprime (x^ex x) (\<Prod>f\<in>P2. f ^ ex f)" 
          using P1_ex_P2_coprime that(1) by auto
        then have "x ^ ex x dvd (\<Sum>y\<in>P1. ?deriv_P1 y)" 
          using ass coprime_dvd_mult_right_iff[OF coprime] unfolding pderiv_fm'' by auto
        also have "(\<Sum>y\<in>P1. ?deriv_P1 y) = ?deriv_P1 x + (\<Sum>y\<in>P1-{x}. ?deriv_P1 y)" sorry
        also have "\<dots> = ?deriv_P1 x + (x^ex x) * (\<Sum>y\<in>P1 - {x}. smult (of_nat (ex y))
        (pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>(P1 - {x})- {y}. fj ^ ex fj)))" sorry
        finally have "x ^ ex x dvd ?deriv_P1 x + (x^ex x) * (\<Sum>y\<in>P1 - {x}. smult (of_nat (ex y))
        (pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>(P1 - {x})- {y}. fj ^ ex fj)))" by auto
        then have "x ^ ex x dvd ?deriv_P1 x" using dvd_add_times_triv_right_iff
        by (simp add: dvd_add_left_iff)
        then show False using P1_ex_power_not_dvd[OF that(1)]  sorry
      qed
      have less: "a \<le> ex x - 1" if "a\<in>{n. x ^ n dvd pderiv fm}" for a 
      proof -
        have "x ^ a dvd pderiv fm"
        show ?thesis using P1_ex_power_not_dvd
 sorry
      show ?case using dvd less by auto
    qed (use fin in \<open>auto\<close>)
  qed
  
  have mult_deriv2: "multiplicity x (pderiv fm) \<ge> ex x "  
    if "x\<in>P2" "pderiv fm \<noteq> 0" for x
  proof (subst multiplicity_eq_Max[OF that(2)])
    show "\<not> is_unit x" using that(1) using P2_def fac_set_def not_prime_unit by blast
    then have fin: "finite {n. x ^ n dvd pderiv fm}"
      using is_unit_iff_infinite_divisor_powers that(2) by blast
    show "Max {n. x ^ n dvd pderiv fm} \<ge> ex x"
    proof - 
      have dvd: "x ^ ex x dvd pderiv fm" unfolding pderiv_fm' by(intro dvd_sum)
       (metis (no_types, lifting) P1_def P2_def \<open>finite fac_set\<close> dvd_mult dvd_prod dvd_refl 
        dvd_smult finite_Diff insert_Diff insert_iff mem_Collect_eq that(1))
      then show ?thesis by (intro Max_ge, auto simp add: fin)
    qed
  qed


  have mult_deriv: "multiplicity x (pderiv fm) \<ge> (if p dvd ex x then ex x else ex x - 1)"  
    if "x\<in>fac_set" "pderiv fm \<noteq> 0" for x
  proof (subst multiplicity_eq_Max[OF that(2)])
    show "\<not> is_unit x" using that(1) using fac_set_def not_prime_unit by blast
    then have fin: "finite {n. x ^ n dvd pderiv fm}"
      using is_unit_iff_infinite_divisor_powers that(2) by blast 
    show "Max {n. x ^ n dvd pderiv fm} \<ge> (if p dvd ex x then ex x else ex x - 1)"  
    proof (split if_splits, safe, goal_cases)
      case 1
      then have "x\<in>P2" unfolding P2_def using that by auto
      have dvd: "x ^ ex x dvd pderiv fm" unfolding pderiv_fm' by(intro dvd_sum)
       (metis (no_types, lifting) "1" P1_def \<open>finite fac_set\<close> dvd_mult dvd_prod dvd_refl dvd_smult 
        finite_Diff insert_Diff insert_iff mem_Collect_eq that(1))
(*      moreover 
      have "\<not>x^(ex x+1) dvd pderiv fm" unfolding pderiv_fm'' sorry
      then have "a \<le> ex x" if "x ^ a dvd pderiv fm" for a using that
        by (metis add.commute not_less_eq_eq plus_1_eq_Suc power_le_dvd)
      moreover have "finite {n. x ^ n dvd pderiv fm}" 
        using \<open>\<not> is_unit x\<close> is_unit_iff_infinite_divisor_powers that(2) by blast
*)
      then show ?case by (intro Max_ge, auto simp add: fin)
 (* by (subst Max_eq_iff) auto*)
    next
      case 2
      then have "x\<in>P1" unfolding P1_def using that by auto
      have dvd: "x ^(ex x-1) dvd pderiv fm" unfolding pderiv_fm' by(intro dvd_sum)
        (metis (no_types, lifting) One_nat_def P1_def P1_ex_nonzero \<open>finite fac_set\<close> \<open>x \<in> P1\<close> 
        dvd_mult dvd_mult2 dvd_prod dvd_smult dvd_triv_right finite_Diff insert_Diff 
        insert_iff mem_Collect_eq power_eq_if semiring_1_class.of_nat_simps(1))
      then show ?case by (intro Max_ge, auto simp add: fin)
    qed
  qed

  have "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    if "pderiv fm = 0"
  proof -
    have "u = fm" unfolding u_def \<open>pderiv fm = 0\<close> using fm_def by auto
    moreover have "fm = (\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else 
      fj ^(ej-1)))"
      using pderiv0_p_dvd_count[OF _ that] unfolding Let_def
      using f_fac fac_def fac_set_def prod_mset_multiplicity
      by (smt (verit, del_insts) mult_fm prod.cong)
    ultimately show ?thesis by auto
  qed

  moreover have "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    if "pderiv fm \<noteq> 0"
  unfolding u_def proof (subst gcd_eq_factorial', goal_cases)
    case 3
    let ?prod_pow = "(\<Prod>p\<in>prime_factors fm \<inter> prime_factors (pderiv fm).
        p ^ min (ex p) (multiplicity p (pderiv fm)))"
    have norm: "normalize ?prod_pow = ?prod_pow" by (intro normalize_prod_monics)
      (metis Int_iff dvd_0_left_iff in_prime_factors_iff monic_normalize normalize_prime)
    have subset: "prime_factors fm \<inter> prime_factors (pderiv fm) \<subseteq> fac_set" 
      unfolding fac_set_def by auto
    show ?case unfolding norm proof (subst prod.mono_neutral_left[OF _ subset], goal_cases)
      case 2
      have "i \<in># prime_factorization (pderiv fm)"  if "i \<in> fac_set" "ei = count fac i"
           "i ^ min ei (multiplicity i (pderiv fm)) \<noteq> 1" for i ei
      proof (intro prime_factorsI)
        have "min ei (multiplicity i (pderiv fm)) \<noteq> 0" using that(3) by (metis power_0)
        then have "multiplicity i (pderiv fm) \<ge> 1" by simp
        then show "i dvd pderiv fm"
          using not_dvd_imp_multiplicity_0 by fastforce
        show "pderiv fm \<noteq> 0" "prime i" using \<open>pderiv fm \<noteq> 0\<close> \<open>i \<in> fac_set\<close> 
          unfolding fac_set_def by auto
      qed
      then show ?case  using mult_fm unfolding fac_set_def Let_def using ex_def by fastforce
    next
      case 3
      have "x ^ min (multiplicity x fm) (multiplicity x (pderiv fm)) = x ^ multiplicity x fm" 
        if "x \<in> fac_set" "p dvd multiplicity x fm" for x
        using \<open>pderiv fm \<noteq> 0\<close> ex_def mult_deriv that(1) that(2) by fastforce
      moreover have "x ^ min (multiplicity x fm) (multiplicity x (pderiv fm)) =
         x ^ (multiplicity x fm - Suc 0)" if "x \<in> fac_set" "\<not> p dvd multiplicity x fm" for x
        sledgehammer sorry
      ultimately show ?case by (subst normalize_prod_monics, simp) 
        (intro prod.cong, simp, unfold Let_def,
         auto simp add: ex_def mult_deriv[OF _ \<open>pderiv fm \<noteq> 0\<close>])
    qed (auto simp add: fac_set_def)  
  qed (auto simp add: \<open>fm\<noteq>0\<close> that)
  
  ultimately have u: "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    by blast
  then have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))"
    unfolding u Let_def by (smt (verit) P1_def P2_def \<open>P1 \<inter> P2 = {}\<close> \<open>fac_set = P1 \<union> P2\<close> 
      \<open>finite P1\<close> \<open>finite P2\<close> mem_Collect_eq prod.cong prod.union_disjoint)

  have v_def: "v = fm div u" unfolding fm_def u_def using assms unfolding aux_def 
    by (auto split: if_splits simp add: Let_def)
  have v: "v = \<Prod>P1" 
  proof -
    have "v = ((\<Prod>fj\<in>P1. fj^(ex fj)) * (\<Prod>fj\<in>P2. fj^(ex fj))) div u" 
      unfolding v_def fm_P1_P2 by auto
    also have "\<dots> = (\<Prod>fj\<in>P1. fj^(ex fj)) div (\<Prod>fj\<in>P1. fj^(ex fj-1))" unfolding u Let_def
    by (metis (no_types, lifting) \<open>fm \<noteq> 0\<close> div_div_div_same dvd_triv_right fm_P1_P2 mult_not_zero 
      nonzero_mult_div_cancel_right semiring_gcd_class.gcd_dvd1 u u' u_def)
    also have "\<dots> = \<Prod>P1"
    proof -
      have *: "(\<Prod>fj\<in>P1. fj^(ex fj)) = (\<Prod>P1) * (\<Prod>fj\<in>P1. fj^(ex fj-1))"
      by (smt (z3) P1_def dvd_0_right mem_Collect_eq power_eq_if prod.cong prod.distrib)
      show ?thesis unfolding * by auto
    qed
    finally show ?thesis by auto
  qed



  have prime_factors_v: "prime_factors v = P1" unfolding v 
  proof (subst prime_factors_prod[OF \<open>finite P1\<close>], goal_cases)
    case 1
    then show ?case using \<open>fac_set = P1 \<union> P2\<close> nonzero by blast
  next
    case 2
    have prime: "prime x" if "x\<in>P1" for x using P1_def fac_set_def that by blast
    have "\<Union> (prime_factors ` P1) = P1" using prime[THEN prime_prime_factors] by auto
    then show ?case by simp
  qed

  show "squarefree v" proof (subst squarefree_factorial_semiring', safe, goal_cases)
    case (2 p)
    have "0 \<notin> (\<lambda>x. x) ` P1" using prime_factors_v by force
    moreover have "prime_elem p" using "2" in_prime_factors_imp_prime by blast 
    moreover have "sum (multiplicity p) P1 = 1"
      by (metis "2" \<open>finite P1\<close> calculation(2) in_prime_factors_imp_prime multiplicity_prime 
      prime_factors_v prime_multiplicity_other sum_eq_1_iff)
    ultimately show ?case using 2 unfolding prime_factors_v unfolding v 
      by (subst prime_elem_multiplicity_prod_distrib) auto
  qed (simp add: v P1_def)

  have gcd_u_v: "gcd u (v^n) = (\<Prod>fj\<in>P1. fj ^(ex fj -1))" sorry
  
  have "w = (\<Prod>fj\<in>P2. fj^(ex fj))" sorry

  have z_def: "z = root_poly' p w" 
    unfolding p_def w_def u_def fm_def n_def using assms unfolding aux_def
    by (auto simp add: Let_def split: if_splits)

  have z: "z = (\<Prod>x\<in>P2. x ^(ex x div p))" sorry

  show "z ^ CARD('e) dvd f" unfolding p_def[symmetric] sorry

  show "radical f = v * radical z"  sorry

qed

lemma degree_aux_less [termination_simp]:
  assumes "aux f = Some (v, z)"
  shows   "degree z < degree f"
using square_free_part_of_correct_aux[OF assms] 
sorry

lemma is_measure_degree [measure_function]: "is_measure Polynomial.degree"
  by (rule is_measure_trivial)

text \<open>This algorithm output only the square-free part of a polynomial. 
  It is also called Elimination of Repeated Factors (ERF).
  According to Alg 1 in https://carleton.ca/math/wp-content/uploads/Factoring-Polynomials-over-Finite-Fields_Melissa-Scott.pdf

Problem: This is only for finite fields of the form \<bbbF>_p where p is a prime (no prime power allowed).
For prime powers we run into the dependent type problem: Our algorithm depends on the field 
characteristic which is only embedded in the type 'e. 
Fortunately for the usecase of the KZG, thie field we use is of the form \<bbbF>_p with p prime.
\<close>
fun square_free_part_of ::"'e mod_ring poly \<Rightarrow> 'e mod_ring poly list" where
  "square_free_part_of f = (
     case aux f of
       None \<Rightarrow> if degree f = 0 then [] else [f]
     | Some (v, z) \<Rightarrow> v # square_free_part_of z)"

lemma square_free_part_of_correct:
  assumes "f \<noteq> 0"
  shows   "prod_list (square_free_part_of f) = radical f"
          "p \<in> set (square_free_part_of f) \<Longrightarrow> squarefree p"
using square_free_part_of_correct_aux
sorry


thm multiplicity_gcd
thm gcd_eq_factorial'
thm prime_power_dvd_pderiv


notepad
begin
  fix f :: "'e mod_ring poly"
  fix p :: nat
  write multiplicity ("\<natural>[_]")
  define Pf1 where "Pf1 = {x\<in>prime_factors f. p dvd multiplicity x f}"
  define Pf2 where "Pf2 = {x\<in>prime_factors f. \<not>p dvd multiplicity x f}"
end
  

proof (relation "Wellfounded.measure (\<lambda> f. degree f)", goal_cases)
qed auto

  case (2 f a f_mono p u n v w z)
(*
  have "degree f > 1" 
  proof (rule ccontr)
    assume "\<not> 1 < degree f"
    then consider (zero)"degree f = 0" | (one) "degree f = 1" by arith
    then show False proof (cases)
      case zero
      then show ?thesis using 2(1) by auto
    next
      case one
      then obtain a0 a1 where "f = [:a0,a1:]" "a1\<noteq>0" using degree1_coeffs by blast
      then have f_mono: "f_mono = [:a0 * (inverse a1), 1:]" unfolding 2(2,3) by auto
      have pderiv: "pderiv f_mono = [:1:]" unfolding f_mono by (auto simp add: pderiv_pCons)
      have "u = 1" unfolding 2(5) pderiv unfolding f_mono by auto
      then show ?thesis using 2(7) by auto
    qed
  qed
*)
  have "degree f = degree f_mono" unfolding 2 by auto
  have "f \<noteq> 0" using 2(1) by auto
  obtain c fs where factor_f: "f = smult c (prod_mset fs)" 
    and irred_monic: "(set_mset fs \<subseteq> Irr_Mon)" 
    using exactly_one_factorization[OF \<open>f\<noteq>0\<close>] unfolding factorization_def by auto
  (* f_i = set_mset   e_i = count fs fi*)
  have "monic f_mono" unfolding 2(3) 2(2) using 2(1) by auto
  have "f = smult a f_mono" unfolding 2(3) by (simp add: "2"(2) \<open>f \<noteq> 0\<close>)
  then have "smult c (prod_mset fs) = smult a f_mono" unfolding factor_f[symmetric] by auto
  have non_zero: "a\<noteq>0" "c\<noteq>0" using \<open>f \<noteq> 0\<close> factor_f \<open>f = smult a f_mono\<close> by auto
  have "monic (\<Prod>\<^sub># fs)" using irred_monic unfolding Irr_Mon_def
    by (simp add: monic_prod_mset subset_iff)
  have "c = a" by (rule decompose_monic_part_and_coefficient(1)[OF \<open>monic (\<Prod>\<^sub># fs)\<close> \<open>monic f_mono\<close> 
    \<open>smult c (prod_mset fs) = smult a f_mono\<close> non_zero(2) non_zero(1)])
  have f_mono_factor: "prod_mset fs = f_mono" by (rule decompose_monic_part_and_coefficient(2)[OF \<open>monic (\<Prod>\<^sub># fs)\<close> 
    \<open>monic f_mono\<close> \<open>smult c (prod_mset fs) = smult a f_mono\<close> non_zero(2) non_zero(1)])
  
  
  have pderiv_fmono: "pderiv f_mono = (\<Sum> f\<in>(set_mset fs). 
    Polynomial.smult (of_nat (count fs f)) (pderiv f) * f ^ (count fs f - 1) *
     (\<Prod>fj\<in>set_mset fs - {f}. fj ^ count fs fj))"
  using pderiv_exp_prod_monic[OF f_mono_factor[symmetric]] unfolding Let_def by auto

  have "(\<Prod>fj\<in>set_mset fs. let ej = count fs fj in 
    (if p dvd ej then  fj ^ ej else fj ^(ej-1))) = u"
    unfolding 2(5) pderiv_fmono unfolding f_mono_factor[symmetric] 
  proof (subst gcd_unique[symmetric], safe, goal_cases)
    case 1
    then show ?case unfolding Let_def prod_mset_multiplicity 
      by (rule prod_dvd_prod, auto simp add: le_imp_power_dvd)
  next
    case 2
    then show ?case unfolding Let_def prod_mset_multiplicity 
    proof (rule dvd_sum, goal_cases)
      case (1 a)
      define f where 
        " f = (\<lambda>fj. if p dvd count fs fj then fj ^ count fs fj else fj ^ (count fs fj - 1))"
      let ?left = "(\<Prod>fj\<in>set_mset fs. f fj)"
      let ?right = "(Polynomial.smult (of_nat (count fs a)) (pderiv a) * a ^ (count fs a - 1) *
         (\<Prod>fj\<in>set_mset fs - {a}. fj ^ count fs fj)) "
      let ?A = "f ` (set_mset fs)"
      let ?multifs = "set_mset fs - {fi. fi \<in># fs \<and> f fi = 1}"
      have "?left = (\<Prod>fj\<in>?multifs. f fj)" 
        by (smt (verit, del_insts) DiffD1 DiffD2 DiffI Diff_subset finite_set_mset mem_Collect_eq 
        prod.mono_neutral_cong_left)
      also have "\<dots> = \<Prod> (f ` ?multifs)"
      proof (rule prod.image_eq[of f, symmetric])
        have "x = y" if "x\<in>?multifs" "y\<in>?multifs" "f x = f y" for x y
        proof -
          have irred_norm: "irreducible x" "irreducible y" "normalize x = x" "normalize y = y"
            using irred_monic 1 normalize_monic that unfolding Irr_Mon_def by auto
          have prime: "prime x" "prime y" using 1 unfolding normalization_semidom_class.prime_def 
            by (auto simp add: irred_norm)
          show ?thesis 
          proof (cases "p dvd count fs x")
            case True
            have zero: "0 < count fs x" using that by simp
            show ?thesis  by (cases "p dvd count fs y") 
              (use True that prime_power_eq_imp_eq[OF prime(1) prime(2) zero] f_def in \<open>auto\<close>)
          next
            case False 
            have zero: "0 < count fs x - Suc 0" using that  by (metis (mono_tags, lifting) 
              DiffD1 DiffD2 False One_nat_def f_def gr0I mem_Collect_eq power_0)
            then show ?thesis by (cases "p dvd count fs y") 
              (use False that prime_power_eq_imp_eq[OF prime(1) prime(2) zero] f_def in \<open>auto\<close>)
          qed
        qed
        then show  "inj_on f ?multifs" unfolding inj_on_def by auto
      qed
      also have "\<dots> = \<Prod> ?A"
      proof -
        have *: "set_mset fs = ?multifs \<union> {fi. fi \<in># fs \<and> f fi = 1}" by auto
        have eval_1: "\<Prod>((\<lambda>x. 1) ` {fi. fi \<in># fs \<and> f fi = 1}) = 1" by (meson imageE prod.neutral)
        then show ?thesis by (subst (3) *, subst image_Un, subst prod.union_disjoint) auto
      qed
      finally have rew_left: "?left = \<Prod> ?A" by auto
      have finite: "finite ?A" using finite_set_mset[of fs] by auto
      have coprime_factors:
        " \<forall>c1 c2. c1 \<in> ?A \<and> c2 \<in> ?A \<and> c1 \<noteq> c2 \<longrightarrow> comm_monoid_mult_class.coprime c1 c2"
      proof (safe, goal_cases)
        case (1 c1 c2 fi fj)
        define ei where "ei = count fs fi"
        define ej where "ej = count fs fj"
        have "fi \<noteq> fj" using 1(2) by auto
        have "coprime fi fj" by (rule coprime_polynomial_factorization[of "set_mset fs"])
          (use 1  irred_monic in \<open>unfold Irr_Mon_def, auto\<close>) 
        then show ?case unfolding ei_def[symmetric] ej_def[symmetric] f_def by auto
      qed
      have dvd: "\<forall>c\<in>?A. c dvd ?right" proof (safe, goal_cases)
        case (1 c fj)
        let ?ej = "count fs fj"
        let ?ea = "count fs a"
        show ?case proof (cases "p dvd ?ea")
          case True
          then have "(of_nat ?ea :: 'e mod_ring) = 0" using \<open>p = CARD('e)\<close> by auto
          then have zero: "?right = 0" by auto
          show ?thesis unfolding zero by auto
        next
          case False
          then show ?thesis proof (cases "p dvd ?ej")
            case True
            then have "fj \<noteq> a" using \<open>\<not> p dvd ?ea\<close> by auto
            then have "fj\<in>set_mset fs - {a}" using \<open>fj\<in># fs\<close> by auto
            then show ?thesis using True f_def by (intro dvd_mult, auto)
          next
            case False
            then show ?thesis proof (cases "a = fj")
              case True
              then show ?thesis using \<open>\<not> p dvd count fs fj\<close> f_def
              by (subst dvd_mult2[where c="(\<Prod>fj\<in>set_mset fs - {a}. fj ^ count fs fj)"]) 
                 (subst dvd_mult, auto)
            next
              case False
              then have "fj\<in>set_mset fs - {a}" using \<open>fj\<in># fs\<close> by auto
              then have "fj ^ (?ej - Suc 0) dvd (\<Prod>fj\<in>set_mset fs - {a}. fj ^ count fs fj)"
                by (meson diff_le_self dvd_prod finite_Diff finite_set_mset le_imp_power_dvd) 
              then show ?thesis using \<open>\<not> p dvd count fs fj\<close> f_def by (subst dvd_mult, auto)
            qed
          qed
        qed
      qed
      show ?case unfolding f_def[symmetric] unfolding rew_left 
        using divides_prod2[OF finite dvd coprime_factors] by auto
    qed
  next
    case 3
    then show ?case by (rule normalize_monic, rule monic_prod) 
      (use Irr_Mon_def irred_monic monic_power in \<open>auto simp add: Let_def\<close>)
  next
    case (4 e)
    obtain es where "es \<subseteq># fs" "e = \<Prod>\<^sub># es" using 4(1) prod_mset_primes_dvd_imp_subset
    let ?u = "(\<Prod>fj\<in>set_mset fs. let ej = count fs fj in if p dvd ej then fj ^ ej 
      else fj ^ (ej - 1))"
    let ?deriv = "(\<Sum>f\<in>set_mset fs. smult (of_nat (count fs f)) (pderiv f) *
           f ^ (count fs f - 1) * (\<Prod>fj\<in>set_mset fs - {f}. fj ^ count fs fj))"
    
    show ?case proof (rule contrapos_pp[OF conjI[OF 4(1) 4(2)]], goal_cases)
      case 1

      have u_dvd_all: "?u dvd \<Prod>\<^sub># fs" unfolding Let_def prod_mset_multiplicity 
        by (rule prod_dvd_prod)(auto simp add: le_imp_power_dvd)
      have "\<not> e dvd ?deriv" if "e dvd \<Prod>\<^sub># fs"
      proof -
        have *: "False" if "fi ^ count fs fi dvd e \<Longrightarrow> fi\<in># fs \<Longrightarrow> p dvd count fs fi" for fi
        proof -
          have "fi ^ count fs fi dvd ?u" using that  using 1 \<open>e dvd \<Prod>\<^sub># fs\<close> u_dvd_all
           sorry
          show ?thesis sorry
        qed
        then obtain fi where fi_def: "fi\<in># fs" "fi ^(count fs fi) dvd e" "\<not> p dvd (count fs fi)"
          by blast
        have "\<not> fi ^(count fs fi) dvd ?u" sorry

        then show ?thesis using swap sorry
      qed
      then show ?case by auto
    qed
  qed

  have "p dvd (degree w)" sorry
  moreover have "p>1" unfolding 2(4) using nontriv by blast
  ultimately have "degree w > 1" unfolding 2(9) using 2 sorry
  have "degree w \<le> degree f" sorry
  have "degree z < degree f" unfolding 2(10) using degree_take_root_decr[OF \<open>degree w > 1\<close>]
    by auto
  then show ?case by auto
qed auto






end

context bind_game_def
begin
text \<open>This functions purpose is to extract \<alpha> based on the inputs g^\<alpha> and \<phi>, where \<phi> has a root at \<alpha>. 
The function factorizes \<phi> and filters for all roots. Since \<alpha>'s mod_ring is of the same cardinality 
as g's group's order, we can conclude that if g^r = g^\<alpha> then r=\<alpha>\<close>
fun find_\<alpha>_square_free :: "'a \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring" where
  "find_\<alpha>_square_free g_pow_\<alpha> \<phi> = (let (c, polys) = finite_field_factorization \<phi>;
    deg1_polys = filter (\<lambda>f. degree f = 1) polys;
    root_list = map (\<lambda>p. poly.coeff p 0) deg1_polys;
    \<alpha>_roots = filter (\<lambda>r. g_pow_\<alpha> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> r) root_list
in -\<alpha>_roots!0)"

(*TODO finite_field_factorization works only for square-free polys \<rightarrow> add step for non-sf to sf*)
fun find_\<alpha> :: "'a \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring" where
  "find_\<alpha> g_pow_\<alpha> \<phi> = find_\<alpha>_square_free g_pow_\<alpha> (square_free_part_of \<phi>)"

lemma poly_eq0_is_find_\<alpha>_eq_\<alpha>: "\<phi> \<noteq> 0 \<Longrightarrow> poly \<phi> \<alpha> = 0 \<longleftrightarrow> find_\<alpha> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>) \<phi> = \<alpha>"
unfolding find_\<alpha>.simps find_\<alpha>_square_free.simps Let_def
proof (safe, goal_cases)
  case 1
  obtain c polys where polys: "(c,polys) = finite_field_factorization \<phi>" by (metis prod.exhaust)
  then have "- filter (\<lambda>r. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> = \<^bold>g [^] r) 
    (map (\<lambda>p. poly.coeff p 0) (filter (\<lambda>f. degree f = 1) polys)) ! 0 = \<alpha>"
     sorry
  then show ?case sorry by (metis polys prod.simps(2))
next
  case 2
  then show ?case sorry
qed


end
end
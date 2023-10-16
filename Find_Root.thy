theory Find_Root

imports "Berlekamp_Zassenhaus.Finite_Field_Factorization" KZG_Def
"Mason_Stothers.Mason_Stothers" 
Root_Power_Poly_Finite_Field
Factorization_Over_Finite_Field_Poly


begin


context
assumes "SORT_CONSTRAINT('e::prime_card)"
begin

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
  have P1_monic[simp]: "monic x" if "x\<in>P1" for x unfolding P1_def
    using P1_def fac_set_monic that by blast

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
        also have "(\<Sum>y\<in>P1. ?deriv_P1 y) = ?deriv_P1 x + (\<Sum>y\<in>P1-{x}. ?deriv_P1 y)" 
          by (intro sum.remove, auto simp add: that)
        also have "\<dots> = ?deriv_P1 x + (x^ex x) * (\<Sum>y\<in>P1 - {x}. smult (of_nat (ex y))
        (pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>(P1 - {x})- {y}. fj ^ ex fj)))"
        proof -
          have *: "(pderiv xa * xa ^ (ex xa - Suc 0) * (\<Prod>fj\<in>P1 - {xa}. fj ^ ex fj)) =
            (x ^ ex x * (pderiv xa * xa ^ (ex xa - Suc 0) * (\<Prod>fj\<in>P1 - {x} - {xa}. fj ^ ex fj)))" 
          if "xa\<in>P1-{x}" for xa
          proof -
            have "x\<in>P1-{xa}" using that \<open>x\<in>P1\<close> by auto
            have fin: "finite (P1 - {xa})" by auto
            show ?thesis by (subst prod.remove[OF fin \<open>x\<in>P1-{xa}\<close>]) 
               (smt (verit, del_insts) Diff_insert2 Groups.mult_ac(3) insert_commute)
          qed
          show ?thesis by (auto simp add: sum_distrib_left *)
        qed
        finally have "x ^ ex x dvd ?deriv_P1 x + (x^ex x) * (\<Sum>y\<in>P1 - {x}. smult (of_nat (ex y))
        (pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>(P1 - {x})- {y}. fj ^ ex fj)))" by auto
        then have "x ^ ex x dvd ?deriv_P1 x" using dvd_add_times_triv_right_iff
        by (simp add: dvd_add_left_iff)
        then show False using P1_ex_power_not_dvd'[OF that(1)] by auto
      qed
      then have less: "a \<le> ex x - 1" if "a\<in>{n. x ^ n dvd pderiv fm}" for a 
      by (metis IntI Int_Collect Suc_pred' algebraic_semidom_class.unit_imp_dvd 
        bot_nat_0.not_eq_extremum is_unit_power_iff not_less_eq_eq power_le_dvd that)
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
      then show ?case by (intro Max_ge, auto simp add: fin)
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
        using P1_def \<open>pderiv fm \<noteq> 0\<close> ex_def mult_deriv1 that(1) that(2) by auto
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

  have gcd_u_v: "gcd u (v^n) = (\<Prod>fj\<in>P1. fj ^(ex fj -1))" unfolding u' v 
  proof (subst gcd_mult_left_right_cancel, goal_cases)
    case 1
    then show ?case by (simp add: P1_P2_coprime prod_coprime_left)
  next
    case 2
    have nonzero1: "(\<Prod>fj\<in>P1. fj ^ (ex fj - 1)) \<noteq> 0"
      by (metis (no_types, lifting) \<open>fm \<noteq> 0\<close> dvd_mult_div_cancel mult_eq_0_iff 
       semiring_gcd_class.gcd_dvd1 u' u_def) 
    have nonzero2: "\<Prod>P1 ^ n \<noteq> 0" using prime_factors_v by fastforce
    have null: "0 \<notin> (\<lambda>fj. fj ^ (ex fj - Suc 0)) ` P1" using prime_factors_v by fastforce
    have null': "0 \<notin> (\<lambda>x. x) ` P1" using prime_factors_v by force
    have P1: "prime_factors (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) \<inter> prime_factors (\<Prod>P1 ^ n) = 
      {x\<in>P1. ex x > 1}"
    proof (unfold n_def,
           subst prime_factors_prod[OF \<open>finite P1\<close> null],
           subst prime_factors_power[OF \<open>0<degree f\<close>],
           subst prime_factors_prod[OF \<open>finite P1\<close> null'],
           unfold comp_def, safe, goal_cases)
      case (1 x xa xb) then show ?case by (metis dvd_trans in_prime_factors_iff prime_factors_v) 
    next
      case (2 x xa xb)
      then have "x = xa"
        by (metis in_prime_factors_iff prime_dvd_power prime_factors_v primes_dvd_imp_eq)
      then have "x \<in># prime_factorization (x ^ (ex x - 1))" using 2 by auto
      then show ?case
      by (metis gr0I in_prime_factors_iff not_prime_unit power_0 zero_less_diff)
    next
      case (3 x) then show ?case 
      by (smt (verit) One_nat_def Totient.prime_factors_power dvd_refl image_ident 
        in_prime_factors_iff mem_simps(8) null' prime_factors_v zero_less_diff) 
    next
      case (4 x) then show ?case
      by (metis dvd_refl in_prime_factors_iff mem_simps(8) not_prime_0 prime_factors_v) 
    qed
    have n: "ex fj \<le> n" if "fj\<in>P1" for fj
    proof -
      have "fj \<noteq> 0" using that unfolding P1_def by auto
      have "degree fj * ex fj \<le> degree f" by (subst degree_power_eq[OF \<open>fj\<noteq>0\<close>, symmetric],
        unfold ex_def) (use divides_degree[OF multiplicity_dvd] \<open>fm \<noteq> 0\<close> fm_def in \<open>auto\<close>)
      then show ?thesis unfolding n_def
      by (metis Missing_Polynomial.is_unit_field_poly \<open>fj \<noteq> 0\<close> bot_nat_0.not_eq_extremum 
        dual_order.trans dvd_imp_le dvd_triv_right empty_iff in_prime_factors_iff 
        linordered_semiring_strict_class.mult_pos_pos prime_factorization_1 prime_factors_v 
        semiring_norm(160) set_mset_empty that)
    qed
    then have min: "min (ex x - Suc 0) n = ex x -1" if "x\<in>P1" for x using n[OF that] by auto
    have mult1: "multiplicity g (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) = ex g -1" if "g\<in>P1" for g
    proof -
      have "prime_elem g" using in_prime_factors_imp_prime prime_factors_v that by blast
      have "multiplicity g (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) = 
            multiplicity g (g^(ex g -1) * (\<Prod>fj\<in>P1-{g}. fj ^ (ex fj - Suc 0)))"
        by (subst prod.remove[OF \<open>finite P1\<close> \<open>g\<in>P1\<close>], auto)
      also have "\<dots> = multiplicity g ((\<Prod>fj\<in>P1-{g}. fj ^ (ex fj - Suc 0)) * g^(ex g -1))"
        by (auto simp add: algebra_simps)
      also have "\<dots> = multiplicity g (g^(ex g -1))" 
      proof (intro multiplicity_prime_elem_times_other[OF \<open>prime_elem g\<close>], rule ccontr, safe) 
        assume ass: "g dvd (\<Prod>fj\<in>P1 - {g}. fj ^ (ex fj - Suc 0))"
        have "irreducible g" using \<open>prime_elem g\<close> by blast
        obtain a where "a\<in>P1-{g}" "g dvd a ^ (ex a -1)" 
          using irreducible_dvd_prod[OF \<open>irreducible g\<close> ass]
          by (metis dvd_1_left nat_dvd_1_iff_1)
        then have "g dvd a" by (meson \<open>prime_elem g\<close> prime_elem_dvd_power)
        then show False
        by (metis DiffD1 DiffD2 \<open>a \<in> P1 - {g}\<close> in_prime_factors_imp_prime insertI1 
          prime_factors_v primes_dvd_imp_eq that)
      qed
      also have "\<dots> = ex g -1" by (metis image_ident in_prime_factors_imp_prime 
        multiplicity_same_power not_prime_unit null' prime_factors_v that)
      finally show ?thesis by blast
    qed
    have mult2: "multiplicity g (\<Prod>P1 ^ n) = n" if "g\<in>P1" for g  
    proof -
      have "\<Prod>P1\<noteq>0" unfolding P1_def 
      using P1_def in_prime_factors_iff prime_factors_v that v by blast
      have "prime_elem g" using in_prime_factors_imp_prime prime_factors_v that by blast
      have "multiplicity g (\<Prod>P1 ^ n) = n * (multiplicity g (\<Prod>P1))" 
        by (subst prime_elem_multiplicity_power_distrib[OF \<open>prime_elem g\<close> \<open>\<Prod>P1\<noteq>0\<close>], auto)
      also have "\<dots> = n * multiplicity g (g * \<Prod>(P1-{g}))" by (metis \<open>finite P1\<close> prod.remove that)
      also have "\<dots> = n * multiplicity g (\<Prod>(P1-{g}) * g)" by (auto simp add: algebra_simps)
      also have "\<dots> = n" 
      proof (subst multiplicity_prime_elem_times_other[OF \<open>prime_elem g\<close>]) 
        show "\<not> g dvd \<Prod>(P1 - {g})" by (metis DiffD1 DiffD2 \<open>prime_elem g\<close> 
          as_ufd.prime_elem_iff_irreducible in_prime_factors_imp_prime irreducible_dvd_prod 
          prime_factors_v primes_dvd_imp_eq singletonI that) 
        show "n * multiplicity g g = n" by (auto simp add: multiplicity_prime[OF \<open>prime_elem g\<close>])
      qed
      finally show ?thesis by blast
    qed
    have split: "(\<Prod>x\<in>{x \<in> P1. Suc 0 < ex x}. x ^ (ex x - Suc 0)) =
      (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0))" 
    proof -
      have *: "ex x \<noteq> 0" if "x\<in>P1" for x by (metis P1_ex_nonzero of_nat_0 that)
      have "Suc 0 < ex x" if "x\<in>P1" "ex x \<noteq> Suc 0" for x using *[OF that(1)] that(2) by auto
      then have union: "P1 = {x\<in>P1. 1 < ex x} \<union> {x\<in>P1. ex x = 1}" by auto
      show ?thesis by (subst (2) union, subst prod.union_disjoint) auto 
    qed
    show ?case by (subst gcd_eq_factorial'[OF nonzero1 nonzero2],subst normalize_prod_monics) 
      (auto simp add: P1 mult1 mult2 min normalize_prod_monics split)
  qed
  
  have w: "w = (\<Prod>fj\<in>P2. fj^(ex fj))" unfolding w_def gcd_u_v unfolding u'
  by (metis (no_types, lifting) \<open>fm \<noteq> 0\<close> gcd_eq_0_iff gcd_u_v nonzero_mult_div_cancel_left u_def)

  have w_power: "w = (\<Prod>fj\<in>P2. fj^(ex fj div p))^p" 
  proof -
    have w: "w = (\<Prod>fj\<in>P2. fj^((ex fj div p)*p))" unfolding w P2_def by auto
    show ?thesis unfolding w by (auto simp add: power_mult prod_power_distrib[symmetric])
  qed

  have z_def: "z = root_poly' p w" 
    unfolding p_def w_def u_def fm_def n_def using assms unfolding aux_def
    by (auto simp add: Let_def split: if_splits)

  have z: "z = (\<Prod>x\<in>P2. x ^(ex x div p))" unfolding z_def p_def w_power
    using root_poly'_power' by auto
  have zw: "z^CARD('e) = w" unfolding w_power z p_def[symmetric] by auto

  show "z ^ CARD('e) dvd f" unfolding zw w 
  by (metis (full_types) dvd_mult_right dvd_normalize_iff dvd_refl fm_P1_P2 fm_def)

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
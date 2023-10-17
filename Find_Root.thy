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

lemma  u_characterization :
fixes f::"'e mod_ring poly"
assumes "degree f \<noteq> 0" 
and u_def: "u = gcd (normalize f) (pderiv (normalize f))"
shows "u = (let fm' = normalize f in
  (\<Prod>fj\<in>prime_factors fm'. let ej = multiplicity fj fm' in 
    (if CARD('e) dvd ej then  fj ^ ej else fj ^(ej-1))))" (is ?u)
and "u = (let fm' = normalize f; P1 = {f\<in>prime_factors fm'. \<not> CARD('e) dvd multiplicity f fm'};
              P2 = {f\<in>prime_factors fm'. CARD('e) dvd multiplicity f fm'} in 
  (\<Prod>fj\<in>P1. fj^(multiplicity fj fm' -1)) * (\<Prod>fj\<in>P2. fj^(multiplicity fj fm')))"
(is ?u')
proof -
  define p where "p = CARD('e)"

  interpret finite_field_poly_factorization "TYPE('e)" f p
  proof (unfold_locales)
    show "p = CARD('e)" by (rule p_def)
    show "degree f \<noteq> 0" using assms by auto
  qed
  
  
  have "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    if "pderiv fm = 0"
  proof -
    have "u = fm" unfolding u_def \<open>pderiv fm = 0\<close> using fm_def that by auto
    moreover have "fm = (\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else 
      fj ^(ej-1)))"
      using pderiv0_p_dvd_count[OF _ that] unfolding Let_def f_fac prod_mset_multiplicity
      by (intro prod.cong) (simp add:fac_set_def fac_def, auto)
    ultimately show ?thesis by auto
  qed

  moreover have "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    if "pderiv fm \<noteq> 0"
  unfolding u_def fm_def[symmetric] proof (subst gcd_eq_factorial', goal_cases)
    case 3
    let ?prod_pow = "(\<Prod>p\<in>prime_factors fm \<inter> prime_factors (pderiv fm).
        p ^ min (multiplicity p fm) (multiplicity p (pderiv fm)))"
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
      ultimately show ?case by (intro prod.cong, simp, unfold Let_def,
         auto simp add: ex_def mult_deriv[OF _ \<open>pderiv fm \<noteq> 0\<close>])
    qed (auto simp add: fac_set_def)  
  qed (auto simp add: fm_nonzero that)
  
  ultimately have u: "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    by blast
  then have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))"
    unfolding Let_def by (smt (verit) P1_def P2_def P1_P2_intersect fac_set_P1_P2 
      finites(2) finites(3) mem_Collect_eq prod.cong prod.union_disjoint)
  
  show ?u using u unfolding ex_def fm_def fac_set_def unfolding Let_def p_def by auto
  show ?u' using u' unfolding local.P1_def local.P2_def 
    unfolding p_def ex_def fm_def Let_def fac_set_def by auto
qed

lemma v_characterization:
assumes "aux f = Some (v,z)"
shows "v = (let fm = normalize f in fm div (gcd fm (pderiv fm)))" (is ?a)
and "v = \<Prod>{x\<in>prime_factors (normalize f). \<not> CARD('e) dvd multiplicity x (normalize f)}" (is ?b)
and "prime_factors v = {x\<in>prime_factors (normalize f). \<not> CARD('e) dvd multiplicity x (normalize f)}"(is ?c)
and "squarefree v"(is ?d)
proof -
  define p where "p = CARD('e)"
  have [simp]: "degree f \<noteq> 0" using assms unfolding aux_def by (metis not_None_eq)

  interpret finite_field_poly_factorization "TYPE('e)" f p
  proof (unfold_locales)
    show "p = CARD('e)" by (rule p_def)
    show "degree f \<noteq> 0" by auto
  qed

  define u where "u = gcd fm (pderiv fm)"
  have u_def': "u = gcd (normalize f) (pderiv (normalize f))" unfolding u_def fm_def by auto
  have u: "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    using u_characterization[OF \<open>degree f \<noteq> 0\<close>] u_def 
    unfolding fm_def Let_def fac_set_def ex_def p_def
    by blast 
  have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))" 
    using u_characterization(2)[OF \<open>degree f \<noteq> 0\<close> u_def'] unfolding fm_def[symmetric] Let_def 
      fac_set_def[symmetric] ex_def[symmetric] p_def[symmetric]
    using P1_def P2_def ex_def by presburger
    

  have v_def: "v = fm div u" unfolding fm_def u_def using assms unfolding aux_def 
    by (auto split: if_splits simp add: Let_def)
  then show ?a unfolding u_def fm_def Let_def by auto

  have v: "v = \<Prod>P1" 
  proof -
    have "v = ((\<Prod>fj\<in>P1. fj^(ex fj)) * (\<Prod>fj\<in>P2. fj^(ex fj))) div u" 
      unfolding v_def fm_P1_P2 by auto
    also have "\<dots> = (\<Prod>fj\<in>P1. fj^(ex fj)) div (\<Prod>fj\<in>P1. fj^(ex fj-1))" unfolding u Let_def
    by (metis (no_types, lifting) fm_nonzero div_div_div_same dvd_triv_right fm_P1_P2 mult_not_zero 
      nonzero_mult_div_cancel_right semiring_gcd_class.gcd_dvd1 u u' u_def)
    also have "\<dots> = \<Prod>P1"
    proof -
      have *: "(\<Prod>fj\<in>P1. fj^(ex fj)) = (\<Prod>P1) * (\<Prod>fj\<in>P1. fj^(ex fj-1))"
      by (smt (z3) P1_def dvd_0_right mem_Collect_eq power_eq_if prod.cong prod.distrib)
      show ?thesis unfolding * by auto
    qed
    finally show ?thesis by auto
  qed
  then show ?b unfolding P1_def fac_set_def fm_def ex_def unfolding p_def by auto


  have prime_factors_v: "prime_factors v = P1" unfolding v 
  proof (subst prime_factors_prod[OF finites(2)], goal_cases)
    case 1
    then show ?case using fac_set_P1_P2 nonzero by blast
  next
    case 2
    have prime: "prime x" if "x\<in>P1" for x using P1_def fac_set_def that by blast
    have "\<Union> (prime_factors ` P1) = P1" using prime[THEN prime_prime_factors] by auto
    then show ?case by simp
  qed
  then show ?c unfolding P1_def fac_set_def ex_def fm_def unfolding p_def by auto

  show "squarefree v" proof (subst squarefree_factorial_semiring', safe, goal_cases)
    case (2 p)
    have "0 \<notin> (\<lambda>x. x) ` P1" using prime_factors_v P1_prime_elem by fastforce
    moreover have "prime_elem p" using "2" in_prime_factors_imp_prime by blast 
    moreover have "sum (multiplicity p) P1 = 1"
      by (metis "2" finites(2) calculation(2) in_prime_factors_imp_prime multiplicity_prime 
      prime_factors_v prime_multiplicity_other sum_eq_1_iff)
    ultimately show ?case using 2 unfolding prime_factors_v unfolding v 
      by (subst prime_elem_multiplicity_prod_distrib) auto
  qed (simp add: v P1_def)
qed

lemma gcd_u_v: 
assumes "aux f = Some (v,z)"
shows "let fm = normalize f; u = gcd fm (pderiv fm); 
  P1 = {x\<in>prime_factors fm. \<not> CARD('e) dvd multiplicity x fm} in
gcd u (v^(degree f)) = (\<Prod>fj\<in>P1. fj ^(multiplicity fj fm -1))"
proof -
  define p where "p = CARD('e)"
  have [simp]: "degree f \<noteq> 0" using assms unfolding aux_def by (metis not_None_eq)

  interpret finite_field_poly_factorization "TYPE('e)" f p
  proof (unfold_locales)
    show "p = CARD('e)" by (rule p_def)
    show "degree f \<noteq> 0" by auto
  qed

  define u where "u = gcd (normalize f) (pderiv (normalize f))"
  have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))" 
    using u_characterization(2)[OF \<open>degree f \<noteq> 0\<close> u_def] unfolding fm_def[symmetric] Let_def 
      fac_set_def[symmetric] ex_def[symmetric] p_def[symmetric]
    using P1_def P2_def ex_def by presburger
  have v: "v = \<Prod>P1" using v_characterization(2)[OF assms] unfolding P1_def fac_set_def fm_def ex_def
    using p_def by auto
  have prime_factors_v: "prime_factors v = P1" using v_characterization(3)[OF assms]
    unfolding P1_def fac_set_def ex_def fm_def using p_def by auto
  have v_def: "v = fm div u" unfolding fm_def u_def using assms unfolding aux_def 
    by (auto split: if_splits simp add: Let_def)

  have "gcd u (v^(degree f)) = (\<Prod>fj\<in>P1. fj ^(multiplicity fj fm -1))" unfolding u' v 
  proof (subst gcd_mult_left_right_cancel, goal_cases)
    case 1
    then show ?case by (simp add: P1_P2_coprime prod_coprime_left)
  next
    case 2
    have nonzero1: "(\<Prod>fj\<in>P1. fj ^ (ex fj - 1)) \<noteq> 0" using ex_def by auto
    have nonzero2: "\<Prod>P1 ^ (degree f) \<noteq> 0" using prime_factors_v v v_def by fastforce
    have null: "0 \<notin> (\<lambda>fj. fj ^ (ex fj - Suc 0)) ` P1" using prime_factors_v nonzero1 by force
    have null': "0 \<notin> (\<lambda>x. x) ` P1" using prime_factors_v P1_irreducible by blast
    have P1: "prime_factors (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) \<inter> prime_factors (\<Prod>P1 ^ (degree f)) = 
      {x\<in>P1. ex x > 1}"
    proof (subst prime_factors_prod[OF finites(2) null],
           subst prime_factors_power[OF deg_f_gr_0],
           subst prime_factors_prod[OF finites(2) null'],
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
    have n: "ex fj \<le> degree f" if "fj\<in>P1" for fj
    proof -
      have "fj \<noteq> 0" using that unfolding P1_def by auto
      have "degree (fj ^ multiplicity fj fm) \<le> degree f" 
        using divides_degree[OF multiplicity_dvd] fm_nonzero 
        by (subst degree_normalize[of f, symmetric], unfold fm_def[symmetric]) auto
      then have "degree fj * ex fj \<le> degree f" by (subst degree_power_eq[OF \<open>fj\<noteq>0\<close>, symmetric],
        unfold ex_def) 
      then show ?thesis 
      by (metis Missing_Polynomial.is_unit_field_poly \<open>fj \<noteq> 0\<close> bot_nat_0.not_eq_extremum 
        dual_order.trans dvd_imp_le dvd_triv_right empty_iff in_prime_factors_iff 
        linordered_semiring_strict_class.mult_pos_pos prime_factorization_1 prime_factors_v 
        semiring_norm(160) set_mset_empty that)
    qed
    then have min: "min (ex x - Suc 0) (degree f) = ex x -1" if "x\<in>P1" for x using n[OF that] by auto
    have mult1: "multiplicity g (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) = ex g -1" if "g\<in>P1" for g
    proof -
      have "prime_elem g" using in_prime_factors_imp_prime prime_factors_v that by blast
      have "multiplicity g (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) = 
            multiplicity g (g^(ex g -1) * (\<Prod>fj\<in>P1-{g}. fj ^ (ex fj - Suc 0)))"
        by (subst prod.remove[OF finites(2) \<open>g\<in>P1\<close>], auto)
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
    have mult2: "multiplicity g (\<Prod>P1 ^ (degree f)) = (degree f)" if "g\<in>P1" for g  
    proof -
      have "\<Prod>P1\<noteq>0" unfolding P1_def 
      using P1_def in_prime_factors_iff prime_factors_v that v by simp
      have "prime_elem g" using in_prime_factors_imp_prime prime_factors_v that by blast
      have "multiplicity g (\<Prod>P1 ^ (degree f)) = (degree f) * (multiplicity g (\<Prod>P1))" 
        by (subst prime_elem_multiplicity_power_distrib[OF \<open>prime_elem g\<close> \<open>\<Prod>P1\<noteq>0\<close>], auto)
      also have "\<dots> = (degree f) * multiplicity g (g * \<Prod>(P1-{g}))" by (metis finites(2) prod.remove that)
      also have "\<dots> = (degree f) * multiplicity g (\<Prod>(P1-{g}) * g)" by (auto simp add: algebra_simps)
      also have "\<dots> = (degree f)" 
      proof (subst multiplicity_prime_elem_times_other[OF \<open>prime_elem g\<close>]) 
        show "\<not> g dvd \<Prod>(P1 - {g})" by (metis DiffD1 DiffD2 \<open>prime_elem g\<close> 
          as_ufd.prime_elem_iff_irreducible in_prime_factors_imp_prime irreducible_dvd_prod 
          prime_factors_v primes_dvd_imp_eq singletonI that) 
        show "(degree f) * multiplicity g g = (degree f)" 
          by (auto simp add: multiplicity_prime[OF \<open>prime_elem g\<close>])
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
      (auto simp add: P1 mult1 mult2 min normalize_prod_monics split, auto simp add: ex_def)
  qed
  then show ?thesis unfolding Let_def u_def P1_def fm_def ex_def fac_set_def using p_def by auto
qed

lemma square_free_part_of_correct_aux:
  assumes "aux f = Some (v, z)"                                
  shows   "radical f = v * radical z"
          "squarefree v"
          "z ^ CARD('e) dvd f"
          (* "prime_factors f = prime_factors v \<union> prime_factors z" (* alt. form of "radical f = v * radical z"; probably unnecessary *)*)
proof -
  define p where "p = CARD('e)"

  have [simp]: "degree f \<noteq> 0" using assms unfolding aux_def by (metis not_None_eq)

  interpret finite_field_poly_factorization "TYPE('e)" f p
  proof (unfold_locales)
    show "p = CARD('e)" by (rule p_def)
    show "degree f \<noteq> 0" by auto
  qed

  define u where "u = gcd fm (pderiv fm)"
  define n where "n = degree f"
  define w where "w = u div (gcd u (v^n))"
  have u_def': "u = gcd (normalize f) (pderiv (normalize f))" unfolding u_def fm_def by auto

  have u: "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    using u_characterization[OF \<open>degree f \<noteq> 0\<close>] u_def 
    unfolding fm_def Let_def fac_set_def ex_def p_def
    by blast 
  have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))" 
    using u_characterization(2)[OF \<open>degree f \<noteq> 0\<close> u_def'] unfolding fm_def[symmetric] Let_def 
      fac_set_def[symmetric] ex_def[symmetric] p_def[symmetric]
    using P1_def P2_def ex_def by presburger
    

  have v_def: "v = fm div u" unfolding fm_def u_def using assms unfolding aux_def 
    by (auto split: if_splits simp add: Let_def)
  have v: "v = \<Prod>P1" using v_characterization(2)[OF assms] unfolding P1_def fac_set_def fm_def ex_def
    using p_def by auto

  have prime_factors_v: "prime_factors v = P1" 
    using v_characterization(3)[OF assms] unfolding P1_def fac_set_def fm_def ex_def
    using p_def by auto

  show "squarefree v" by (rule v_characterization(4)[OF assms])


  have gcd_u_v: "gcd u (v^n) = (\<Prod>fj\<in>P1. fj ^(ex fj -1))" using gcd_u_v[OF assms]
    unfolding Let_def u_def fm_def P1_def fac_set_def ex_def using p_def n_def by force
  
  have w: "w = (\<Prod>fj\<in>P2. fj^(ex fj))" unfolding w_def gcd_u_v unfolding u'
  by (metis (no_types, lifting) fm_nonzero gcd_eq_0_iff gcd_u_v nonzero_mult_div_cancel_left u_def)

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

  have "z\<noteq>0" by (simp add: fac_set_P1_P2 z)
  
  have prime_factors_z: "\<Prod>(prime_factors z) = \<Prod>P2" unfolding z 
  proof (subst prime_factors_prod)
    show "finite P2" by auto
    show "0 \<notin> (\<lambda>x. x ^ (ex x div p)) ` P2" using fac_set_P1_P2 by force
    have pos: "0 < ex x div p" if "x\<in>P2" for x 
    by (metis (no_types, lifting) P2_def count_prime_factorization_prime dvd_div_eq_0_iff 
        ex_def fac_set_def gr0I in_prime_factors_imp_prime mem_Collect_eq not_in_iff that)
    have "prime_factors (x ^ (ex x div p)) = {x}" if "x\<in>P2" for x 
      unfolding prime_factors_power[OF pos[OF that]] using that by (simp add: prime_prime_factors)
    then have *: "(\<Union>x\<in>P2. prime_factors (x ^ (ex x div p))) = P2" by auto
    show "\<Prod>(\<Union> ((prime_factors \<circ> (\<lambda>x. x ^ (ex x div p))) ` P2)) = \<Prod>P2" 
      unfolding comp_def * by auto
  qed

  show "radical f = v * radical z"
  proof -
    have factors: "prime_factors f = fac_set" unfolding fac_set_def fm_def by auto
    have "\<Prod>(prime_factors f) = \<Prod>P1 * \<Prod>P2" unfolding factors fac_set_P1_P2 
      by (subst prod.union_disjoint, auto)
    also have "\<dots> = v * \<Prod>(prime_factors z)" unfolding v using \<open>z\<noteq>0\<close> prime_factors_z by auto
    finally have "\<Prod>(prime_factors f) = v * \<Prod>(prime_factors z)" by auto
    then show ?thesis  unfolding radical_def using \<open>z\<noteq>0\<close> f_nonzero by auto
  qed

qed

lemma square_free_part_of_correct_aux_None:
assumes "aux f = None"
shows "degree f = 0 \<or> radical f = normalize f" "squarefree f"
proof -
  define u where "u = gcd (normalize f) (pderiv (normalize f))"
  have or: "degree f = 0 \<or> u = 1" using assms unfolding aux_def 
    by (smt (verit, best) option.simps(3) u_def)
  have rad: "radical f = normalize f" if "u =1"   sorry
  
  show "degree f = 0 \<or> radical f = normalize f" using or rad by auto
  show "squarefree f" using radical_squarefree sorry
qed

lemma degree_aux_less [termination_simp]:
  assumes "aux f = Some (v, z)"
  shows   "degree z < degree f"
proof -
  have "z\<noteq>0" by (metis Find_Root.square_free_part_of_correct_aux(1) assms aux_def degree_0 
    mult_poly_0(2) option.simps(3) radical_eq_0_iff)
  have "f\<noteq>0" using assms unfolding aux_def by auto
  then have "degree z * CARD('e) \<le> degree f" 
    using divides_degree[OF square_free_part_of_correct_aux(3)[OF assms]] 
    unfolding degree_power_eq[OF \<open>z\<noteq>0\<close>] by auto
  then show ?thesis by (metis assms aux_def dual_order.strict_trans1 less_nat_zero_code 
    linorder_cases mult.comm_neutral mult_less_cancel1 nontriv option.simps(2))
qed

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
proof -
  show "prod_list (square_free_part_of f) = radical f"
  proof (cases "aux f")
    case None
    then show ?thesis apply (subst square_free_part_of.simps) apply auto sorry
  next
    case (Some a)
    then show ?thesis sorry
  qed
  show "p \<in> set (square_free_part_of f) \<Longrightarrow> squarefree p"
  proof (cases "aux f")
    case None
    then show ?thesis sorry
  next
    case (Some a)
    then show ?thesis sorry
  qed
qed
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
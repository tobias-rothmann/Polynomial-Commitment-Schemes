theory Find_Root

imports "Berlekamp_Zassenhaus.Finite_Field_Factorization" KZG_Def
"Mason_Stothers.Mason_Stothers"

begin


definition root_poly :: "( 'a :: zero \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "root_poly rt n p = Abs_poly (\<lambda>i. rt (poly.coeff p (i * n)))"

lemma coeff_root_poly [simp]: "poly.coeff (root_poly rt n p) i = rt (poly.coeff p (i * n))"
  sorry

definition root_poly' :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> _ poly" where
  "root_poly' n p = Abs_poly (\<lambda>i. poly.coeff p (i * n))"

definition root_poly'_impl :: "nat \<Rightarrow> 'a :: zero list \<Rightarrow> 'a list" where
  "root_poly'_impl n cs = undefined"

lemma root_poly'_code [code]:
  "coeffs (root_poly' n p) = root_poly'_impl n (coeffs p)"
sorry

context
assumes "SORT_CONSTRAINT('e::prime_card)"
begin

lemma root_poly'_power:
  assumes "is_nth_power CARD('e) p"
  shows   "root_poly' CARD('e) p ^ CARD('e) = p"
  sorry

(*
definition root_poly' :: "'e mod_ring poly \<Rightarrow> 'e mod_ring poly" where
  "root_poly' = root_poly (\<lambda>_ x. x) CARD('e)"
*)

lemma CHAR_mod_ring [simp]: "CHAR('e mod_ring) = CARD('e)"
apply (rule CHAR_eqI)
apply auto
using of_nat_0_mod_ring_dvd by blast

(*
definition is_rootable :: "nat \<Rightarrow> 'e mod_ring poly \<Rightarrow> bool" where
"is_rootable p f = (\<exists>x. x^p = f)"

definition take_root :: "nat \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring poly" where
"take_root p f = (if (is_rootable p f) then (SOME x. x^p = f) else 0)"

lemma degree_take_root:
assumes "degree f \<noteq> 0" 
shows "degree (take_root p f) < degree f"
unfolding take_root_def proof (split if_splits, safe, goal_cases)
  case 1
  then obtain x where x: "x = (SOME x. x^p = f)" by blast
  have "x^p = f" 
    apply (subst x, unfold some_eq_ex[of "(\<lambda>y. y^p=f)"]) using 1 by (auto simp add: is_rootable_def)
  then show ?case unfolding x[symmetric] sledgehammer sorry
next
  case 2
  then show ?case using assms by auto
qed
*)
(*
definition is_square :: "nat \<Rightarrow> bool" where
"is_square n = ((Discrete.sqrt n)^2 = n)"

lemma is_square_0 [simp]:
"is_square 0"
unfolding is_square_def by auto

lemma is_square_1 [simp]:
"is_square (Suc 0)"
unfolding is_square_def using sqrt_one by fastforce

lemma not_is_square_2[simp]:
"\<not> (is_square (Suc (Suc 0)))"
unfolding is_square_def 
by (metis One_nat_def bot_nat_0.extremum less_exp not_less_eq_eq numerals(2) power_one sqrt_unique)
*)
(*

fun take_root_coeffs :: "nat \<Rightarrow> 'e mod_ring list \<Rightarrow> 'e mod_ring list" where
"take_root_coeffs n [] = []" |
"take_root_coeffs n (c # cs) = 
  (if (length cs) then c # (take_root_coeffs n cs) else take_root_coeffs n cs)"

definition take_root ::"nat \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring poly" where
"take_root n f = Poly (take_root_coeffs n (coeffs f))"

lemma take_root_0:
"take_root n 0 = 0"
unfolding take_root_def by auto


lemma is_square_length_degree:
assumes "\<not> (coeffs as = [] \<and> a = 0)"
shows "is_square (degree (pCons a as)) = is_square (length (coeffs as))"
unfolding degree_eq_length_coeffs using assms by auto

lemma take_root_pCons:
"take_root n (pCons a as) = 
  (if is_square (degree (pCons a as)) then pCons a (take_root n as)  else take_root n as)"
proof (cases "is_square (degree (pCons a as))")
  case True
  have "Poly (take_root_coeffs n (cCons a (coeffs as))) =
        pCons a (Poly (take_root_coeffs n (coeffs as)))"
  proof (cases "coeffs as = [] \<and> a = 0")
    case False
    then show ?thesis using True is_square_length_degree[OF False] by auto
  qed auto
  then show ?thesis using True unfolding take_root_def by auto
next
  case False
  have "take_root_coeffs n (cCons a (coeffs as)) = take_root_coeffs n (coeffs as)"
  proof (cases "coeffs as = [] \<and> a = 0")
    case False
    then show ?thesis using \<open>\<not> is_square (degree (pCons a as))\<close> 
      is_square_length_degree[OF False] by auto
  qed auto
  then show ?thesis using False unfolding take_root_def by auto
qed



lemma length_take_root_coeffs:
assumes "length cs > 2"
shows "length (take_root_coeffs n cs) < length cs"
proof -
  obtain b c d as where cs: "cs = b # c # d # as" using assms 
    by (metis Cons_nth_drop_Suc One_nat_def nat_1_add_1 not_less_eq not_less_iff_gr_or_eq 
    nth_drop_0 plus_1_eq_Suc)
  show ?thesis unfolding cs by (induct as, auto)
qed


lemma degree_take_root_decr:
assumes "degree f > 1"
shows "degree (take_root n f) < degree f"
unfolding take_root_def using degree_Poly 
by (smt (verit, best) One_nat_def Poly.simps(1) add_less_mono1 assms degree_0 degree_Poly' 
le_simps(2) length_coeffs length_coeffs_degree length_take_root_coeffs nat_1_add_1 not_less_eq 
order_less_imp_not_less order_trans_rules(21))
*)

(*
lemma poly_power_sum:
"p^n = (\<Sum>i\<le>degree p. Polynomial.monom (poly.coeff p i) (i^n))"
apply (subst poly_as_sum_of_monoms[of p, symmetric]) using poly_power_card_as_sum_of_monoms
oops

lemma coeff_poly_power_characterization:
"poly.coeff (p^n) i = (if is_square i then (poly.coeff p (THE x. x^2 = i))^n else 0)"
apply (subst poly_as_sum_of_monoms[of p, symmetric]) apply auto
oops

lemma is_root_take_root:
"take_root n (p^n) = p"
proof -
  define cs where cs_def: "cs = coeffs (p^n)"
  have assms: "p^n = Poly (cs)" unfolding cs_def by auto
  show ?thesis unfolding take_root_def Let_def cs_def[symmetric] using assms cs_def
  proof (induction cs arbitrary: n p)
    case (Nil)
    then have "p = 0" by auto 
    then show ?case unfolding take_root_coeffs.simps by auto
  next
    case (Cons a as)
    then show ?case 
    proof (cases "is_square (length (a # as))")
      case True
      have "Poly (a # local.take_root_coeffs n as) = p" sorry
      then show ?thesis unfolding take_root_coeffs.simps using True by auto
    next
      case False
      then have "a = 0"
      have "Poly (local.take_root_coeffs n as) = p" sorry
      then show ?thesis unfolding take_root_coeffs.simps using False by auto
    qed
  qed
qed
*)

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
  define f' where "f' = normalize f"
  define p where "p = CARD('e)"
  define u where "u = gcd f' (pderiv f')"
  define n where "n = degree f"

  consider "degree f = 0" | "degree f > 0" "u = 1" | "degree f > 0" "u \<noteq> 1"
    by blast
  then have "radical f = v * radical z \<and> squarefree v \<and> z ^ CARD('e) dvd f" (is "?th1 \<and> ?th2 \<and> ?th3")
  proof cases
  case 1
    then show ?thesis sorry
  next
  case 2
    then show ?thesis sorry
  next
  case 3
    then show ?thesis sorry
  qed
  thus ?th1 ?th2 ?th3
    by blast+
qed

lemma degree_aux_less [termination_simp]:
  assumes "aux f = Some (v, z)"
  shows   "degree z < degree f"
using square_free_part_of_correct_aux
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
theory KZG_hiding

imports KZG_correct DL_assumption Cyclic_Group_SPMF_ext Polynomial_Interpolation.Lagrange_Interpolation 
HOL.Finite_Set

begin

locale hiding_game_def = KZG_correct
begin

text \<open>Although the hiding game will look similar to the Sigma_Commit_Crypto hiding_game, 
The evaluation commitment and verification phase does not exactly mirror the classical 
commitment scheme as defined in Sigma_Commit_Crypto, which is why we will define our own game 
to show this property. 
Explanation:
In a classical commitment-scheme one tries to break the commitment by coming up with two 
plain texts that verify for the same commitment. 
However in the evaluation commitment phase, one tries to come up with a commitment to a 
polynomial that allows to verify the commitment of the evaluation of two different polynomials and the witness 
to these evaluations. This could be modelled in the classical approach, however the semantics would 
not really fit as we are not trying to come up with two different plain texts but with commitments.
\<close>
text \<open>The evaluation commitment scheme functions.\<close>

text \<open>Expose just the public key from the Setup\<close>
definition key_gen:: "'a pk spmf" where
  "key_gen = do {
    (_::'e sk, PK::'a pk) \<leftarrow> Setup;
    return_spmf PK
  }"

definition valid_msg :: "'e eval_value \<Rightarrow> 'a eval_witness \<Rightarrow> bool" where 
  "valid_msg \<phi>_i w_i = (w_i \<in> carrier G\<^sub>p)"

subsection \<open>Game definition\<close>

type_synonym ('a', 'e')  adversary = 
  "'a' commit \<Rightarrow> ('e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness) list \<Rightarrow> 
 'e' polynomial spmf"

definition hiding_game :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf"
  where "hiding_game I \<A> = TRY do {
  \<phi> \<leftarrow> sample_uniform_poly max_deg;
  PK \<leftarrow> key_gen;
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) I;
  \<phi>' \<leftarrow> \<A> C witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"

definition hiding_advantage :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> real"
  where "hiding_advantage I \<A> \<equiv> spmf (hiding_game I \<A>) True"

subsection \<open>DL game\<close>

sublocale DL_G\<^sub>p: DL G\<^sub>p "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding DL_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

subsection \<open>Reduction\<close>

definition compute_g_pow_\<phi>_of_\<alpha> :: "('e mod_ring \<times> 'a) list \<Rightarrow> 'e mod_ring \<Rightarrow> 'a" where
  "compute_g_pow_\<phi>_of_\<alpha> xs_ys \<alpha>= do {
  let xs = map fst xs_ys;
  let lagrange_exp = map (\<lambda>(xj,yj). yj ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_basis_poly xs xj) \<alpha>)) xs_ys;
  fold (\<lambda>x prod. prod \<otimes>\<^bsub>G\<^sub>p\<^esub> x) lagrange_exp \<one>}"

(*TODO implement fun*)
fun sample_not_in :: "'e eval_position list \<Rightarrow> 'e eval_position"
  where "sample_not_in I = (SOME x. x \<notin> set I)"

lemma sample_not_in:
  assumes "length I < CARD('e)"
  and "distinct I"
shows "distinct (sample_not_in I#I)"
  sorry

fun reduction
  :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> ('a,'e) DL.adversary"                     
where
  "reduction I \<A> g_pow_a = do {
  let I_ext = sample_not_in I;
  evals \<leftarrow> sample_uniform_list max_deg (order G\<^sub>p);
  let exp_evals = g_pow_a # map (\<lambda>i. \<^bold>g [^] i) evals ;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip (I_ext#I) exp_evals) \<alpha>;
  let wtn_ts = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (map (of_int_mod_ring \<circ> int) evals));
  \<phi>' \<leftarrow> \<A> C wtn_ts;
  return_spmf (poly \<phi>' I_ext)
  }"

end 

locale hiding_game_proof = hiding_game_def 
begin

subsection \<open>Reduction proof\<close>

subsubsection \<open>helping lemmas\<close>

lemma eval_on_lagrange_basis: "poly (lagrange_interpolation_poly xs_ys) x \<equiv> (let 
    xs = map fst xs_ys
    in sum_list (map (\<lambda> (xj,yj).  yj * (poly (lagrange_basis_poly xs xj) x)) xs_ys))"
  (is "?lhs\<equiv>?rhs")
proof -
  have "?lhs\<equiv>let 
    xs = map fst xs_ys
    in sum_list (map (\<lambda> p. poly p x) (map (\<lambda> (xj,yj). Polynomial.smult yj (lagrange_basis_poly xs xj)) xs_ys))"
    unfolding lagrange_interpolation_poly_def Let_def
    by (simp add: poly_sum_list poly_hom.hom_sum_list)
  also have "\<dots>\<equiv>let 
    xs = map fst xs_ys
    in sum_list (map ((\<lambda> (xj,yj). poly (Polynomial.smult yj (lagrange_basis_poly xs xj)) x)) xs_ys)"
    unfolding split_def Let_def
    by (smt (verit, ccfv_SIG) length_map nth_equalityI nth_map)
  also have "\<dots>\<equiv>let 
    xs = map fst xs_ys
    in sum_list (map ((\<lambda> (xj,yj). yj * (poly (lagrange_basis_poly xs xj) x))) xs_ys)"
    by fastforce
  finally show "?lhs \<equiv> ?rhs" .
qed

lemma fold_on_G\<^sub>p_is_sum_list: "fold (\<lambda>x prod. prod \<otimes>\<^bsub>G\<^sub>p\<^esub> x) (map (\<lambda>x. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> f x) xs) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> z) 
  = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> z \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (sum_list (map f xs))"
proof (induction xs arbitrary: z)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "fold (\<lambda>x prod. prod \<otimes> x) (map (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> f x) (a # xs)) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> z)
    =  fold (\<lambda>x prod. prod \<otimes> x) (map (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> f x) xs) (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (z + f a))"
     by (simp add: mod_ring_pow_mult_G\<^sub>p)
   also have "\<dots> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (z + f a) \<otimes> \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> sum_list (map f xs)" 
     using Cons.IH by blast 
   also have "\<dots> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> z  \<otimes> \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>(f a) \<otimes> \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> sum_list (map f xs)"
     by (simp add: mod_ring_pow_mult_G\<^sub>p)
   also have "\<dots> =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> z  \<otimes> \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> sum_list (map f (a # xs))"
     using G\<^sub>p.cyclic_group_assoc mod_ring_pow_mult_G\<^sub>p by force
   finally show ?case .
 qed

lemma compute_g_pow_\<phi>_of_\<alpha>_is_Commit:
  assumes dist: "distinct (map fst xs_ys)"
  and length_xs_ys: "length xs_ys \<le> max_deg+1"
shows "compute_g_pow_\<phi>_of_\<alpha> (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha> = Commit 
    (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys)"
proof -
  have "compute_g_pow_\<phi>_of_\<alpha> (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha> = 
    (let xs = map fst (map (\<lambda>(x, y). (x, \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys);
         lagrange_exp =
           map (\<lambda>(xj, y). (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> poly (lagrange_basis_poly xs xj) \<alpha>) xs_ys 
     in fold (\<lambda>x prod. prod \<otimes> x) lagrange_exp \<one>)"
    by (smt (verit) case_prod_unfold compute_g_pow_\<phi>_of_\<alpha>_def length_map nth_equalityI nth_map prod.simps(2))
  also have "\<dots> = (let xs = map fst (map (\<lambda>(x, y). (x, \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys);
         lagrange_exp =
           map (\<lambda>(xj, y). \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (y * poly (lagrange_basis_poly xs xj) \<alpha>)) xs_ys 
     in fold (\<lambda>x prod. prod \<otimes> x) lagrange_exp \<one>)"
    using mod_ring_pow_pow_G\<^sub>p by presburger
  also have "\<dots> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>
  (\<Sum>(xj,
      y)\<leftarrow>xs_ys. y * poly (lagrange_basis_poly
                            (map fst (map (\<lambda>(x, y). (x, \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys)) xj)
                      \<alpha>)"
    using fold_on_G\<^sub>p_is_sum_list[of "(\<lambda>(xj, y). (y *
               poly
                (lagrange_basis_poly (map fst (map (\<lambda>(x, y). (x, \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys))
                  xj)
                \<alpha>))" xs_ys 0]
    unfolding Let_def split_def by force
  also have "\<dots> =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)"
    using eval_on_lagrange_basis
    by (smt (verit, ccfv_SIG) fst_conv length_map nth_equalityI nth_map split_def)
  also have "\<dots> = Commit 
    (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys)"
  proof -
    have "degree (lagrange_interpolation_poly xs_ys) \<le> max_deg"
      by (meson assms(2) degree_lagrange_interpolation_poly le_diff_conv le_trans nat_le_iff_add)
    then show "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (lagrange_interpolation_poly xs_ys) \<alpha> = Commit 
    (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys)"
    unfolding Commit_def 
    using g_pow_PK_Prod_correct by presburger
  qed
  finally show ?thesis by fast
qed

lemma split_pow_div_G\<^sub>p:
  shows " \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (y/x) = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/x)"
  by (metis mod_ring_pow_pow_G\<^sub>p mult_cancel_left2 times_divide_eq_right)

(*TODO alter map ... xs_ys to some xs that is subset of xs_ss \<rightarrow> should be fine *)
lemma witness_calc_correct: 
  assumes dist: "distinct (map fst xs_ys)"
  and length_xs_ys: "length xs_ys \<le> max_deg + 1"
  and \<alpha>_nin_xs: "\<alpha> \<notin> set (map fst xs_ys)"
  shows "map (\<lambda>i. (i, poly (lagrange_interpolation_poly xs_ys) i, createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) i)) (map fst xs_ys)
    =  map (\<lambda>(x,y). (x,y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) xs_ys"
proof -
  have "?thesis = (map (\<lambda>i. (fst i, poly (lagrange_interpolation_poly xs_ys) (fst i), createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) (fst i))) xs_ys
  =  map (\<lambda>(x,y). (x,y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) xs_ys)"
    by simp
  also have "\<dots>"
  proof(rule map_ext)
    fix x
    show "x \<in> set xs_ys \<longrightarrow>
         (fst x, poly (lagrange_interpolation_poly xs_ys) (fst x),
          createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) (fst x)) =
         (\<lambda>(x, y). (x, y, (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>) \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - x)))) x"
    proof 
      assume asm: "x \<in> set xs_ys"
      then obtain xj yj where xj_yj: "(xj,yj) = x"
        using prod.collapse by blast
      moreover have "(xj, poly (lagrange_interpolation_poly xs_ys) xj, createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) xj) 
                   = (xj, yj, (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>) \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> yj) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - xj)))"
      proof -
        have \<alpha>_neg_xj: "\<alpha> \<noteq> xj"
              by (metis asm assms(1) assms(3) entries_keysD entries_of_alist fst_eqD keys_of_alist xj_yj)

        have "createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) xj = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>) \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> yj) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - xj))"
          (is "?lhs = ?rhs")
        proof -
          have "?lhs = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (\<psi>_of (lagrange_interpolation_poly xs_ys) xj) \<alpha>)"
            unfolding createWitness.simps Let_def 
            using g_pow_PK_Prod_correct
            by (meson assms(2) degree_lagrange_interpolation_poly degree_q_le_\<phi> le_diff_conv le_trans)
          also have "\<dots> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> ((poly (lagrange_interpolation_poly xs_ys) \<alpha> - poly (lagrange_interpolation_poly xs_ys) xj)/(\<alpha>-xj))"
              using \<alpha>_neg_xj \<phi>x_m_\<phi>u_eq_xmu_\<psi>x by simp
          also have "\<dots> =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> ((poly (lagrange_interpolation_poly xs_ys) \<alpha> - yj)/(\<alpha>-xj))"
            using asm dist lagrange_interpolation_poly xj_yj by blast
          also have "\<dots> =  (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha> - yj)) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - xj))"
            using \<alpha>_neg_xj split_pow_div_G\<^sub>p by force
          also have "\<dots> = ?rhs"
            using mod_ring_pow_mult_inv_G\<^sub>p by presburger
          finally show ?thesis .
        qed
        then show ?thesis
          using asm assms calculation lagrange_interpolation_poly by blast
      qed
      ultimately show "(fst x, poly (lagrange_interpolation_poly xs_ys) (fst x),
          createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) (fst x)) =
         (\<lambda>(x, y). (x, y, (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>) \<otimes> inv (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y)) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - x)))) x"
        by force
    qed
  qed
  finally show ?thesis
    by fast
qed

lemma of_int_mod_inj_on_ff: "inj_on (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) {0..<CARD ('e)}"
proof 
  fix x 
  fix y
  assume x: "x \<in> {0..<CARD('e)}"
  assume y: "y \<in> {0..<CARD('e)}"
  assume app_x_eq_y: "(of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) x = (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) y"
  show "x = y"
    using x y app_x_eq_y 
    by (metis atLeastLessThan_iff nat_int o_apply of_nat_0_le_iff of_nat_less_iff to_int_mod_ring_of_int_mod_ring)
qed

lemma assert_anding[symmetric]: "TRY do {
          _ :: unit \<leftarrow> assert_spmf (a);
            _ :: unit \<leftarrow> assert_spmf (b);
            return_spmf True
        } ELSE return_spmf False 
    = TRY do {
          _ :: unit \<leftarrow> assert_spmf (a \<and> b);
          return_spmf True
      } ELSE return_spmf False"
  by (simp add: try_bind_assert_spmf) 

subsubsection \<open>reduction proof\<close>

definition game2 :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf" where 
  "game2 I \<A> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf (hd evals = poly \<phi>' (hd I))}
  ELSE return_spmf False"

definition game2_wo_assert :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf" where 
  "game2_wo_assert I \<A> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  return_spmf (hd evals = poly \<phi>' (hd I))}
  ELSE return_spmf False"

lemma literal_exchange_lemma: 
  assumes "\<And>x y. x \<in> set_spmf X \<Longrightarrow> U x y = V x y"
  shows"TRY do {x \<leftarrow> X::'x spmf;
           y \<leftarrow> Y :: 'y spmf;
           let r = (U::'x \<Rightarrow> 'y \<Rightarrow> 'r) x y;
           let s = (S::'x \<Rightarrow> 'y \<Rightarrow> 'r \<Rightarrow> 's) x y r;
           w \<leftarrow> (W::'r \<Rightarrow>'s \<Rightarrow> 'w spmf) r s;
           return_spmf ((Z::'x \<Rightarrow> 'y \<Rightarrow> 'w \<Rightarrow> 'z) x y w)} ELSE return_spmf (Z'::'z) = 
        TRY do {x \<leftarrow> X::'x spmf;
           y \<leftarrow> Y :: 'y spmf;
           let r = (V::'x \<Rightarrow> 'y \<Rightarrow> 'r) x y;
           let s = (S::'x \<Rightarrow> 'y \<Rightarrow> 'r \<Rightarrow> 's) x y r;
           w \<leftarrow> (W::'r \<Rightarrow>'s \<Rightarrow> 'w spmf) r s;
           return_spmf ((Z::'x \<Rightarrow> 'y \<Rightarrow> 'w \<Rightarrow> 'z) x y w)} ELSE return_spmf (Z'::'z)"
  using assms
  by (metis (mono_tags, lifting) bind_spmf_cong)


lemma hiding_game_to_game1:
  assumes "distinct I"
  and "length I = max_deg"
  shows "hiding_game I \<A> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) I;
  \<phi>' \<leftarrow> \<A> C witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do {
  evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  PK \<leftarrow> key_gen;
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) I;
  \<phi>' \<leftarrow> \<A> C witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
    sorry
  also have "\<dots> = TRY do {
  evals::'e mod_ring list \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) I;
  \<phi>' \<leftarrow> \<A> C witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
    unfolding key_gen_def split_def by fastforce
  also have "\<dots> = TRY do {
  evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  \<alpha>::'e mod_ring \<leftarrow>  map_spmf (\<lambda>x. of_int_mod_ring (int x)) (sample_uniform (order G\<^sub>p));
  let C = Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (lagrange_interpolation_poly (zip I evals));
  let witn_tupel = map (\<lambda>i. (i, poly (lagrange_interpolation_poly (zip I evals)) i, createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (lagrange_interpolation_poly (zip I evals)) i)) I;
  \<phi>' \<leftarrow> \<A> C witn_tupel;                             
  return_spmf (lagrange_interpolation_poly (zip I evals) = \<phi>')} ELSE return_spmf False"
    unfolding Setup_def split_def Let_def by(simp add: bind_map_spmf o_def)
  also have "\<dots> = TRY do {
  evals:: 'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  \<alpha>::'e mod_ring \<leftarrow>  map_spmf (\<lambda>x. of_int_mod_ring (int x)) (sample_uniform (order G\<^sub>p));
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>i. (i, poly (lagrange_interpolation_poly (zip I evals)) i, createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (lagrange_interpolation_poly (zip I evals)) i)) I;
  \<phi>' \<leftarrow> \<A> C witn_tupel;                             
  return_spmf (lagrange_interpolation_poly (zip I evals) = \<phi>')} ELSE return_spmf False"
   proof(rule literal_exchange_lemma)
     fix evals :: "'e mod_ring list"
     fix \<alpha>
     have 1: "distinct (map fst ((zip I evals)))"
       by (simp add: assms(1) map_fst_zip_take)
     have [symmetric]: "evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p))) 
      \<Longrightarrow> compute_g_pow_\<phi>_of_\<alpha> (map2 (\<lambda>x y. (x, \<^bold>g ^ y)) I evals) \<alpha> = Commit (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly (zip I evals))"
       using compute_g_pow_\<phi>_of_\<alpha>_is_Commit[OF 1] by auto
     then show "evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p))) 
      \<Longrightarrow> Commit (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly (zip I evals)) = compute_g_pow_\<phi>_of_\<alpha> (zip I (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>"
      by (simp add: zip_map2)
  qed
  also have "\<dots> = ?rhs"
    unfolding Setup_def Let_def split_def by(simp add: bind_map_spmf o_def)
  finally show ?thesis .
qed

  

lemma game2_to_game2_assert: 
  assumes "distinct I"
  and "length I = max_deg"
  shows 
"TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False
= game2 I \<A>"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip I evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
      \<phi>' \<leftarrow> \<A> C witn_tupel;
      TRY do {
      return_spmf (\<phi> = \<phi>')}
      ELSE return_spmf False}
    ELSE return_spmf False}
  ELSE return_spmf False}
  ELSE return_spmf False"
  unfolding split_def Let_def
  by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip I evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
      \<phi>' \<leftarrow> \<A> C witn_tupel;
      TRY do {
      _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
      return_spmf True}
      ELSE return_spmf False}
    ELSE return_spmf False}
  ELSE return_spmf False}
  ELSE return_spmf False"
    unfolding Let_def
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf True}
  ELSE return_spmf False"
   unfolding split_def Let_def
   by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>' \<and> hd evals = poly \<phi>' (hd I));
  return_spmf True}
  ELSE return_spmf False"
  proof -
    have "\<And>evals \<phi>'. evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p)))  
      \<Longrightarrow> ((lagrange_interpolation_poly (zip I evals) = \<phi>' 
      \<longleftrightarrow> (lagrange_interpolation_poly (zip I evals)) = \<phi>' \<and> hd evals = poly \<phi>' (hd I)))"
    proof -
      fix evals :: "'e mod_ring list"
      fix \<phi>'
      assume "evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p)))"
      then have evals_length: "length evals = max_deg"
        by (force simp add: bind_map_spmf o_def)
      show "(lagrange_interpolation_poly (zip I evals) = \<phi>' 
      \<longleftrightarrow> lagrange_interpolation_poly (zip I evals) = \<phi>' \<and> hd evals = poly \<phi>' (hd I))"
      proof
        show "lagrange_interpolation_poly (zip I evals) = \<phi>' \<Longrightarrow> lagrange_interpolation_poly (zip I evals) = \<phi>' \<and> hd evals = poly \<phi>' (hd I)"
        proof 
          assume asm: "lagrange_interpolation_poly (zip I evals) = \<phi>'"
          show "hd evals = poly \<phi>' (hd I)"
          proof(rule lagrange_interpolation_poly[symmetric, of "zip I evals"])
            show "distinct (map fst (zip I evals))"
              using assms(1)
              by (simp add: map_fst_zip_take)
            show "\<phi>' = lagrange_interpolation_poly (zip I evals)"
              using asm[symmetric] .
            show "(hd I, hd evals) \<in> set (zip I evals)" 
              using assms(2) evals_length
              by (metis Nil_eq_zip_iff d_pos hd_in_set hd_zip length_greater_0_conv)
          qed
        qed 
      qed simp
    qed
    then show ?thesis 
      unfolding split_def 
      using bind_spmf_cong
      by (smt (verit))
  qed
 also have "\<dots> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip I evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
      \<phi>' \<leftarrow> \<A> C witn_tupel;
      TRY do {
      _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>' \<and> hd evals = poly \<phi>' (hd I));
      return_spmf True}
      ELSE return_spmf False}
    ELSE return_spmf False}
  ELSE return_spmf False}
  ELSE return_spmf False"
  unfolding split_def Let_def
  by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
 also have "\<dots> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip I evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
      \<phi>' \<leftarrow> \<A> C witn_tupel;
      TRY do {
      _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
      _::unit \<leftarrow> assert_spmf (hd evals = poly \<phi>' (hd I));
      return_spmf True}
      ELSE return_spmf False}
    ELSE return_spmf False}
  ELSE return_spmf False}
  ELSE return_spmf False"
   using assert_anding by presburger
  also have "\<dots> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip I evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
      \<phi>' \<leftarrow> \<A> C witn_tupel;
      TRY do {
      _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
        TRY do {
        _::unit \<leftarrow> assert_spmf (hd evals = poly \<phi>' (hd I));
        return_spmf True}
        ELSE return_spmf False}
      ELSE return_spmf False}
    ELSE return_spmf False}
  ELSE return_spmf False}
  ELSE return_spmf False"
    unfolding split_def Let_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
 also have "\<dots> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip I evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
      \<phi>' \<leftarrow> \<A> C witn_tupel;
      TRY do {
      _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
        TRY do {
        return_spmf (hd evals = poly \<phi>' (hd I))}
        ELSE return_spmf False}
      ELSE return_spmf False}
    ELSE return_spmf False}
  ELSE return_spmf False}
  ELSE return_spmf False"
    unfolding Let_def split_def
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip I evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf (hd evals = poly \<phi>' (hd I))}
  ELSE return_spmf False"
    unfolding split_def Let_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  finally show ?thesis unfolding game2_def .
qed

lemma game2_wo_assert_to_DL_reduction_game:"game2_wo_assert I \<A> =  DL_G\<^sub>p.game (reduction I \<A>)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do {
  nat_evals \<leftarrow> sample_uniform_list max_deg (order G\<^sub>p);
  let evals = map (of_int_mod_ring \<circ> int) nat_evals;
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  return_spmf (hd evals = poly \<phi>' (hd I))}
  ELSE return_spmf False"
    unfolding game2_wo_assert_def Let_def by(simp add: bind_map_spmf o_def)
  also have "\<dots> = TRY do {
  a \<leftarrow> sample_uniform (order G\<^sub>p);
  nat_evals \<leftarrow> sample_uniform_list (max_deg-1) (order G\<^sub>p);
  let evals = map (of_int_mod_ring \<circ> int) (a#nat_evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = compute_g_pow_\<phi>_of_\<alpha> (zip I exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip (tl I) evals);
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  return_spmf (hd evals = poly \<phi>' (hd I))}
  ELSE return_spmf False"
    sorry
  
  show ?thesis 
    sorry
qed
  

text \<open>TODO update proofs for changed reduction def\<close>
end



end
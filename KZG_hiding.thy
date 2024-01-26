theory KZG_hiding

imports KZG_correct DL_assumption Cyclic_Group_SPMF_ext Polynomial_Interpolation.Lagrange_Interpolation 

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

definition hiding_Adversary_game :: "'e mod_ring \<Rightarrow> 'e eval_position list \<Rightarrow> 'e polynomial \<Rightarrow> ('a, 'e) adversary \<Rightarrow> 'e polynomial spmf"
  where "hiding_Adversary_game \<alpha> eval_pos \<phi> \<A> = do {
  let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) eval_pos;
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  return_spmf \<phi>'}"

text \<open>put C and eval_poses in parameter and assert\<close>

definition hiding_advantage :: "'e mod_ring \<Rightarrow> 'e eval_position list \<Rightarrow>  'e polynomial \<Rightarrow> ('a, 'e) adversary \<Rightarrow> real"
  where "hiding_advantage \<alpha> eval_pos \<phi> \<A> \<equiv> spmf (hiding_Adversary_game \<alpha> eval_pos \<phi> \<A>) \<phi>"

subsection \<open>DL game\<close>

sublocale DL_G\<^sub>p: DL G\<^sub>p "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding DL_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

subsection \<open>Reduction\<close>

lemma split_sample_distinct_coordinates_uniform_into_points:
"bind_spmf (sample_distinct_coordinates_uniform k n) (\<lambda>coords. return_spmf coords) =
  do {
   points \<leftarrow> sample_distinct_uniform_list k n;
   coords \<leftarrow> map_spmf pair_lists (pair_spmf (return_spmf points) (sample_uniform_list k n));
   return_spmf coords
  }"
  unfolding sample_distinct_coordinates_uniform_def 
  by (smt (verit) bind_return_spmf bind_spmf_cong map_spmf_bind_spmf pair_spmf_alt_def return_bind_spmf)

(* TODO delete +  lemma after this*)
definition sample_n_coords :: "nat \<Rightarrow> ('e mod_ring \<times> 'e mod_ring) list spmf"
where 
  "sample_n_coords n =
    map_spmf (map (\<lambda>(x,y). (of_int_mod_ring (int x),of_int_mod_ring (int y))))
    (sample_distinct_coordinates_uniform n (order G\<^sub>p))"

lemma length_pair_lists: "length xs = n \<Longrightarrow> length ys = n \<Longrightarrow> length (pair_lists (xs,ys)) = n"
  by (induction "(xs,ys)" arbitrary: n xs ys rule: pair_lists.induct)simp+


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

definition compute_g_pow_\<phi>_of_\<alpha> :: "('e mod_ring \<times> 'a) list \<Rightarrow> 'e mod_ring \<Rightarrow> 'a" where
  "compute_g_pow_\<phi>_of_\<alpha> xs_ys \<alpha>= do {
  let xs = map fst xs_ys;
  let lagrange_exp = map (\<lambda>(xj,yj). yj ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_basis_poly xs xj) \<alpha>)) xs_ys;
  fold (\<lambda>x prod. prod \<otimes>\<^bsub>G\<^sub>p\<^esub> x) lagrange_exp \<one>}"

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


fun reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e) DL.adversary"                     
where
  "reduction \<A> g_pow_a = do {
    let coords = zip (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]) (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]); 
    let exp_coords = (fst (hd coords),g_pow_a)#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) (tl coords);
    (\<alpha>, PK) \<leftarrow> Setup;
    let g_pow_\<phi>_of_\<alpha> = compute_g_pow_\<phi>_of_\<alpha> exp_coords \<alpha>;
    let wtn_tuples = map (\<lambda>(x,y). (x,y,(g_pow_\<phi>_of_\<alpha>  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (tl coords);
    \<phi>' \<leftarrow> \<A> g_pow_\<phi>_of_\<alpha> wtn_tuples;
    return_spmf (poly \<phi>' 0)}"

(*sample n coords max_deg + 1 (for point (x,a) ) *)

subsection \<open>Reduction proof\<close>

subsubsection \<open>helping lemmas\<close>

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
    

lemma literal_helping_1: 
  assumes "max_deg + 1 < CARD ('e)"
  shows "(let coords = zip (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) [0..<max_deg + 1]) (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) [0..<max_deg + 1]);
        exp_coords = (fst (hd coords),(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> a))#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) (tl coords) in 
  compute_g_pow_\<phi>_of_\<alpha> exp_coords \<alpha> 
  = Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (lagrange_interpolation_poly ((fst (hd coords),a)#tl coords)))"
proof -
  let ?coords = "zip (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) [0..<max_deg + 1]) (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) [0..<max_deg + 1])::('e mod_ring*'e mod_ring) list"
  let ?exp_coords = "(fst (hd ?coords),(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> a))#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) (tl ?coords)"
  let ?PK = "(map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])"

  have "compute_g_pow_\<phi>_of_\<alpha> ?exp_coords \<alpha> = Commit ?PK (lagrange_interpolation_poly ((fst (hd ?coords), a)#tl ?coords))"
  proof -
    obtain xs_ys where xs_ys: "xs_ys = (fst (hd ?coords),a)#tl ?coords" by fast
    then have exp_coords_is_map_xs_ys: "?exp_coords = (map (\<lambda>(x, y). (x, \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys)" by force
    from xs_ys have dist_xs_ys: "distinct (map fst xs_ys)"
    proof -
      have "(map fst xs_ys) = (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1])"
      proof -
        have "map fst ((fst (hd ?coords),a)#tl ?coords) = fst (fst (hd ?coords),a) # map fst (tl ?coords)"
          by force
        also have "\<dots> = fst (hd ?coords) # map fst (tl ?coords)"
          by fastforce
        also have "\<dots> = map fst (?coords)"
          by (simp add: d_pos hd_zip map_tl)
        also have "\<dots> = map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) [0..<max_deg + 1]"
          by force
        finally show ?thesis unfolding xs_ys .
      qed
      moreover have "distinct (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) [0..<max_deg + 1])"
      proof -
        have "distinct [0..<max_deg + 1]"
          by auto
        moreover have "inj_on (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) (set [0..<max_deg + 1])"
        proof - 
          have "(set [0..<max_deg + 1]) \<subseteq> {0..<CARD ('e)}"
            using assms by auto
          then show ?thesis 
            using of_int_mod_inj_on_ff inj_on_subset by blast 
        qed
        ultimately show ?thesis
          using distinct_map[of "(of_int_mod_ring \<circ> int)" "[0..<max_deg + 1]"] by blast
      qed
      ultimately show ?thesis by argo
    qed
    moreover have length_xs_ys: "length xs_ys \<le> max_deg +1"
    proof -
      have "length xs_ys = length ?coords"
        unfolding xs_ys 
        by force
      also have "\<dots> = max_deg +1"
        by fastforce
      finally show ?thesis by simp
    qed
    show ?thesis using compute_g_pow_\<phi>_of_\<alpha>_is_Commit[OF dist_xs_ys length_xs_ys]
      unfolding xs_ys
      by fastforce
  qed
  then show ?thesis unfolding Let_def .
qed


fun coords_for_witn_tupl :: "('e eval_position * 'e mod_ring) list \<Rightarrow> 'e eval_position \<Rightarrow> ('e eval_position * 'e mod_ring) list" where 
  "coords_for_witn_tupl coords \<alpha> = (if \<alpha> \<in> set (map fst coords) then filter (\<lambda>x. fst x = \<alpha>) coords else tl coords)"

fun cut_coords :: "'e mod_ring list \<Rightarrow> 'e mod_ring \<Rightarrow> 'e mod_ring list" where
  "cut_coords coords \<alpha> = (if \<alpha> \<in> set coords then remove1 \<alpha> coords else tl coords)"

lemma "x < order G\<^sub>p \<Longrightarrow> spmf (sample_uniform (order G\<^sub>p)) x = (1::real)/(order G\<^sub>p)"
  using spmf_sample_uniform by simp


subsubsection \<open>reduction proof\<close>

thm ennreal_spmf_bind

thm spmf_bind
thm nn_integral_measure_spmf

theorem
  assumes "\<And>\<phi> \<alpha> eval_pos. length eval_pos \<le> max_deg \<and> distinct eval_pos \<and> \<alpha> \<notin> set eval_pos \<longrightarrow> spmf (hiding_Adversary_game \<alpha> eval_pos \<phi> \<A>) \<phi> = 1"
  and "max_deg + 1 < CARD ('e)"
  shows "spmf (DL_G\<^sub>p.game (reduction \<A>)) True = 1"
proof -
   note [simp] = Let_def split_def

  text \<open>abbreviations for the mod_ring version of sample uniform nat 
  and the public key\<close>
  let ?mr = "\<lambda>\<alpha>. (of_int_mod_ring (int \<alpha>)::'e mod_ring)"
  let ?PK = "\<lambda>\<alpha>. (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((?mr \<alpha>)^t)) [0..<max_deg+1])"
      
  have "DL_G\<^sub>p.game (reduction \<A>) = TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G\<^sub>p);
    a' \<leftarrow> reduction \<A> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (?mr a));
    return_spmf (?mr a = a') 
  } ELSE return_spmf False"
    unfolding DL_G\<^sub>p.game_def by force
  also have "\<dots> = TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G\<^sub>p);
    a' \<leftarrow>  do {
    let coords = zip (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]) (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]);
    let exp_coords = (fst (hd coords),(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (?mr a)))#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) (tl coords);
    (\<alpha>, PK) \<leftarrow> Setup;
    let g_pow_\<phi>_of_\<alpha> = compute_g_pow_\<phi>_of_\<alpha> exp_coords \<alpha>;
    let wtn_tuples = map (\<lambda>(x,y). (x,y,(g_pow_\<phi>_of_\<alpha>  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (tl coords);
    \<phi>' \<leftarrow> \<A> g_pow_\<phi>_of_\<alpha> wtn_tuples;
    return_spmf (poly \<phi>' 0)};
    return_spmf (of_int_mod_ring (int a) = a') 
  } ELSE return_spmf False"
    unfolding reduction.simps by fast
  also have "\<dots> = TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G\<^sub>p);
    let coords = zip (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]) (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]);
    \<phi>' \<leftarrow> do {
    let exp_coords = (fst (hd coords),(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (?mr a)))#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) (tl coords);
    (\<alpha>, PK) \<leftarrow> Setup;
    let g_pow_\<phi>_of_\<alpha> = compute_g_pow_\<phi>_of_\<alpha> exp_coords \<alpha>;
    let wtn_tuples = map (\<lambda>(x,y). (x,y,(g_pow_\<phi>_of_\<alpha>  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (tl coords);
    \<phi>' \<leftarrow> \<A> g_pow_\<phi>_of_\<alpha> wtn_tuples;
    return_spmf \<phi>'};
    let a' = (poly \<phi>' 0);
    return_spmf (of_int_mod_ring (int a) = a') 
  } ELSE return_spmf False"
    by force
  also have "\<dots> = TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G\<^sub>p);
    \<phi>' \<leftarrow> do {
    let coords = zip (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]) (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]);
    let exp_coords = (fst (hd coords),(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (?mr a)))#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) (tl coords);
    \<alpha> :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let g_pow_\<phi>_of_\<alpha> = compute_g_pow_\<phi>_of_\<alpha> exp_coords (?mr \<alpha>);
    let wtn_tuples = map (\<lambda>(x,y). (x,y,(g_pow_\<phi>_of_\<alpha>  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/((?mr \<alpha>)-x)))) (tl coords);
    \<phi>' \<leftarrow> \<A> g_pow_\<phi>_of_\<alpha> wtn_tuples;
    return_spmf \<phi>'};
    let a' = (poly \<phi>' 0);
    return_spmf (of_int_mod_ring (int a) = a') 
  } ELSE return_spmf False"
    unfolding Setup_def by force
  also have "\<dots> = TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G\<^sub>p);
    \<phi>' \<leftarrow> do {
    let coords = zip (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]) (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]);
    let exp_coords = (fst (hd coords),(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (?mr a)))#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) (tl coords);
    \<alpha> :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let C = Commit (?PK \<alpha>) (lagrange_interpolation_poly ((fst (hd coords),?mr a)#tl coords));
    let wtn_tuples = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/((?mr \<alpha>)-x)))) (tl coords);
    \<phi>' \<leftarrow> \<A> C wtn_tuples;
    return_spmf \<phi>'};
    let a' = (poly \<phi>' 0);
    return_spmf (of_int_mod_ring (int a) = a') 
  } ELSE return_spmf False"
    using literal_helping_1[OF assms(2)] unfolding Let_def
    by algebra
  also have "\<dots> = TRY do { 
    a \<leftarrow> sample_uniform (Coset.order G\<^sub>p);
    \<phi>' \<leftarrow> do {
    let coords = zip (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]) (map (of_int_mod_ring \<circ> int) [0..<max_deg + 1]);
    let exp_coords = (fst (hd coords),(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (?mr a)))#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) (tl coords);
    \<alpha> :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let C = Commit (?PK \<alpha>) (lagrange_interpolation_poly ((fst (hd coords),?mr a)#tl coords));
    let wtn_tuples = map (\<lambda>i. (i, poly (lagrange_interpolation_poly ((fst (hd coords),?mr a)#tl coords)) i, 
        createWitness (?PK \<alpha>) (lagrange_interpolation_poly ((fst (hd coords),?mr a)#tl coords)) i)) (map fst (coords_for_witn_tupl coords (?mr \<alpha>)));
    \<phi>' \<leftarrow> \<A> C wtn_tuples;
    return_spmf \<phi>'};
    let a' = (poly \<phi>' 0);
    return_spmf (of_int_mod_ring (int a) = a') 
  } ELSE return_spmf False"
    using assms unfolding 
    key_gen_def Setup_def Let_def
    sorry           
  

  show ?thesis
  using assms unfolding DL_G\<^sub>p.game_def reduction.simps
  key_gen_def Let_def Setup_def
  sorry
qed

end



end
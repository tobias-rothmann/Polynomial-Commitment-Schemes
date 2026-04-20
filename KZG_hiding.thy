theory KZG_hiding

imports KZG_correct DL_assumption tDL_assumption CryptHOL_ext
begin

locale KZG_PCS_weak_hiding = KZG_PCS_correct
begin

section \<open>Definitions for the weak hiding game\<close>

text \<open>The difference between the weak hiding game and the hiding game is that in the weak hiding 
game the polynomial is uniform random, not arbitrary. Since arbitrary values can be 
modelled as uninitialized parameters in Isabelle, like the polynomial in the hiding game, we can make
the hiding weaker by instantiating a part of it.\<close>

text \<open>The polynomial is chosen uniform random. We also enforce two additional properties on the 
adversary outputs. With this construction we can use the predefined eval hiding game from 
Polynomial Commitment Scheme.\<close>
definition weak_eval_hiding_adversary1 :: "('a vk, 'e argument,'state) 
  eval_hiding_adversary1 \<Rightarrow> ('a vk, 'e argument,'state) eval_hiding_adversary1"
  where 
  "weak_eval_hiding_adversary1 \<A> vk = do {
    (I,\<sigma>) \<leftarrow> \<A> vk;
    _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
    return_spmf (I,\<sigma>)
    }"

text \<open>eval_hiding_game except the polynomial is chosen at uniform random and not by the adversary.\<close>
definition weak_eval_hiding_game ::  "('a vk, 'e argument, 'state) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> bool spmf"
  where "weak_eval_hiding_game \<A>1 \<A>2 = 
  TRY do {
    p::'e mod_ring poly \<leftarrow> sample_uniform_poly max_deg;
    eval_hiding_game p (weak_eval_hiding_adversary1 \<A>1) \<A>2 
  } ELSE return_spmf False"

text \<open>The advantage of the adversary over the weak hiding game is the advantage of eval hiding with
the weak adversary.\<close>
definition weak_eval_hiding_advantage :: "('a vk, 'e argument, 'state) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> real"
  where "weak_eval_hiding_advantage \<A>1 \<A>2 
    \<equiv> spmf (weak_eval_hiding_game \<A>1 \<A>2) True"

subsection \<open>DL game\<close>

text \<open>We instantiate the DL game for the group Gp\<close>
sublocale DL_G\<^sub>p: DL G\<^sub>p "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding DL_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

text \<open>We instantiate the t-DL game for the group Gp\<close>

sublocale t_DL_G\<^sub>p: t_DL G\<^sub>p max_deg "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding t_DL_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

subsection \<open>Reduction\<close>

text \<open>interpolate a polynomial over group points i.e. points of the form (i,g^i). 
Furthermore, return the polynomial evaluated at a value \<alpha>\<close>
definition interpolate_on :: "('e mod_ring \<times> 'a) list \<Rightarrow> 'e mod_ring \<Rightarrow> 'a" where
  "interpolate_on xs_ys \<alpha>= do {
  let xs = map fst xs_ys;
  let lagrange_exp = map (\<lambda>(xj,yj). yj ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_basis_poly xs xj) \<alpha>)) xs_ys;
  fold (\<lambda>x prod. prod \<otimes>\<^bsub>G\<^sub>p\<^esub> x) lagrange_exp \<one>}"

text \<open>filter for the elements that are in xs but not in ys\<close>
fun filter_distinct :: "'e mod_ring list \<Rightarrow> 'e argument list \<Rightarrow> 'e argument list"
  where "filter_distinct xs ys = filter (\<lambda>x. find ((=) x) ys = None) xs"

lemma set_filter_distinct: "set (filter_distinct xs ys) = {x. x \<in> set xs \<and> x \<notin> set ys}"
  by (simp add: find_None_iff)

lemma length_filter_distinct:
  assumes "card (set xs) > card (set ys)"
  shows "length (filter_distinct xs ys) > 0"
proof -
  have "{x. x \<in> set xs \<and> x \<notin> set ys} = set xs - set ys"
    by blast
  moreover have "card (set xs - set ys) \<ge> card (set xs) - card (set ys)"
    using diff_card_le_card_Diff by blast
  moreover have "\<dots> > 0"
    using assms calculation(2) by linarith
  ultimately show ?thesis
    using set_filter_distinct 
    by (metis bot_nat_0.extremum_uniqueI card_length not_gr_zero)
qed

text \<open>function to pick a field element that is not in I. Intuitively, this function 
returns the lowest value not contained in I (note, finite fields do not have a ordering by 
default).\<close>
fun PickDistinct :: "'e argument list \<Rightarrow> 'e argument"
  where "PickDistinct I = hd (filter_distinct (map (of_int_mod_ring::int \<Rightarrow> 'e mod_ring) [0..<CARD('e)]) I)"

lemma card_map_card: "card (set (map (of_int_mod_ring::int \<Rightarrow> 'e mod_ring) [0..<CARD('e)])) = CARD('e)"
proof -
  have "card ((of_int_mod_ring \<circ> int::nat \<Rightarrow> 'e mod_ring) ` {0..<CARD('e)}) = card {0..<CARD('e)}"
    apply (rule card_image)
    apply (rule comp_inj_on)
    apply simp
    apply (metis of_int_mod_inj_on_ff atLeast0LessThan inj_on_imageI)
    done
  then show ?thesis by force
qed

text \<open>helping lemma to show that PickDistinct I prepended to I is distinct if I is distinct and 
smaller than the finite field of its elements.\<close>
lemma PickDistinct: 
  assumes "length I < CARD('e)"
  and "distinct I"
shows "distinct ((PickDistinct I)#I)"
proof -
  have "length (filter_distinct (map of_int_mod_ring [0..<CARD('e)]) I) > 0"
    apply (rule length_filter_distinct)
    apply (insert card_map_card)
    apply (simp add: distinct_card assms) 
    done
  then have "filter_distinct (map of_int_mod_ring [0..<CARD('e)]) I \<noteq> []"
    by blast
  then  have "PickDistinct I \<notin> set I"
    using set_filter_distinct[of _ I]
    by (metis (no_types, lifting) PickDistinct.elims list.set_sel(1) mem_Collect_eq)
  then show ?thesis 
    by (meson assms(2) distinct.simps(2))
qed

text \<open>The reduction function takes an adversary for the hiding game and returns an 
adversary for the DL game. Specifically, the reduction uses the hiding adversary to 
construct a winning strategy for the DL game (i.e. to win it every time).
Essentially, it encodes the DL-instance in a polynomial evaluation on group elements and asks the 
hiding adversary to return the plain polynomial, which contains the solution to the DL-instance.\<close>
fun reduction
  :: "('a vk, 'e argument, 'state) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> ('a,'e) DL.adversary"                     
where
  "reduction \<A>1 \<A>2 g_pow_a = do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  let i = PickDistinct I;
  plain_evals \<leftarrow> map_spmf (map ((of_int_mod_ring::int \<Rightarrow> 'e mod_ring) \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let evals = g_pow_a # map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) plain_evals ;
  let C = interpolate_on (zip (i#I) evals) \<alpha>;
  let W = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> ((1::'e mod_ring)/(\<alpha>-x)))) (zip I plain_evals);
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I W;
  return_spmf (poly \<phi>' i)
  }"

fun reduction_tDL :: "('a vk, 'e argument, 'state) eval_hiding_adversary1 
\<Rightarrow> ('a,'e) t_DL.adversary"
  where "reduction_tDL \<A>1 PK = do {
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  let (\<alpha>'::'e mod_ring) = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = PK!1) (PickDistinct I #I)) of Some x => x | None => 1);
  return_spmf \<alpha>'
  }"

section \<open>Hiding proof\<close>

subsubsection \<open>helping lemmas\<close>

lemma PK1[simp]: "map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1 =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>"
  by (metis (no_types) Suc_eq_plus1 add.commute d_pos diff_zero landau_product_preprocess(53) 
      less_Suc_eq_0_disj nth_map_upt power_one_right)

text \<open>The "find" in the tDL reduction is successful.\<close>
lemma in_set_impl_find: "x \<in> set xs \<Longrightarrow> Some(x) = find (\<lambda>y. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x) xs"
proof - 
  assume asm: "x \<in> set xs"
  then have "\<exists>y. y \<in> set xs \<and> y=x"
    by blast
  then have "find (\<lambda>y. y = x) xs = Some (x)"
    by (smt (verit, ccfv_threshold) find_None_iff find_Some_iff2 not_None_eq)
  then show "Some(x) = find (\<lambda>y. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x) xs"
    by (simp add: pow_on_eq_card)
qed

lemma exchange_lem: "length I = max_deg \<and> distinct I \<and> \<alpha> \<in> set (PickDistinct I#I) 
   \<longleftrightarrow> length I = max_deg \<and> distinct I \<and> \<alpha> \<in> set (PickDistinct I#I) 
   \<and> \<alpha> = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1) (PickDistinct I#I)) of Some x => x | None => 1)"
proof 
  assume asm: "length I = max_deg \<and> distinct I \<and> \<alpha> \<in> set (PickDistinct I # I)"
  then have some: "Some \<alpha> =
    find (\<lambda>x. \<^bold>g ^ x = map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1] ! 1) (PickDistinct I # I)"
    apply (simp only: PK1)
    apply (rule in_set_impl_find)
    apply simp
    done
  show " length I = max_deg \<and>
    distinct I \<and>
    \<alpha> \<in> set (PickDistinct I # I) \<and>
   \<alpha> = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1) (PickDistinct I#I)) of Some x => x | None => 1)"
    apply (subst some[symmetric])
    apply (insert asm)
    apply fastforce
    done
qed simp

text \<open>Note, the following 3 lemmas are build up for the 4th, which states that interpolate_on 
is equivalent to computing Commit.\<close>

text \<open>restate the interpolation of a polynomial as the sum of Lagrange basis polynomials.\<close>
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

text \<open>This lemma is used to restate the folding operation used in the Commit function as a summing 
operation. Together with the prior lemma (i.e. interpolation is summation of Lagrange basis 
polynomials), this allows to restate Commit as the Lagrange interpolation over some points, 
evaluated at \<alpha>.\<close>
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

text \<open>The two prior lemmas are pulled together to show that interpolation_on is 
the evaluation of a polynomial on \<alpha> as a group value i.e (g^{\<phi>(\<alpha>)}). Note (g^{\<phi>(\<alpha>)}) is also the 
result of a correctly computed Commit.\<close>
lemma interpolate_on_\<alpha>_is_\<phi>_of_\<alpha>:
assumes dist: "distinct (map fst xs_ys)"
  and length_xs_ys: "length xs_ys \<le> max_deg+1"
shows "interpolate_on (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha> 
  = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly  (lagrange_interpolation_poly xs_ys) \<alpha>)"
proof -
  have "interpolate_on (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha> = 
    (let xs = map fst (map (\<lambda>(x, y). (x, \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys);
         lagrange_exp =
           map (\<lambda>(xj, y). (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> poly (lagrange_basis_poly xs xj) \<alpha>) xs_ys 
     in fold (\<lambda>x prod. prod \<otimes> x) lagrange_exp \<one>)"
    by (smt (verit) case_prod_unfold interpolate_on_def length_map nth_equalityI nth_map prod.simps(2))
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
  finally show ?thesis by fast
qed

corollary interpolate_on_\<alpha>_is_\<phi>_of_\<alpha>_helper: 
  assumes "length I = max_deg \<and> distinct I"
  and "\<alpha> \<notin> set I"
shows "interpolate_on (zip (PickDistinct I # I) (map ((^\<^bsub>G\<^sub>p\<^esub>) \<^bold>g) evals)) \<alpha>
  = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly  (lagrange_interpolation_poly (zip (PickDistinct I # I) evals)) \<alpha>)"
proof - 
  obtain xs_ys where xs_ys: "xs_ys = zip (PickDistinct I # I) evals" by fast 
  then have "length xs_ys \<le> max_deg + 1" using assms(1) by simp
  moreover have "distinct (map fst xs_ys)" unfolding xs_ys using assms (1)
    by (metis CARD_q PickDistinct d_l_p distinct_take map_fst_zip_take of_nat_less_imp_less)
  ultimately have "interpolate_on (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha> 
  = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly  (lagrange_interpolation_poly xs_ys) \<alpha>)" using interpolate_on_\<alpha>_is_\<phi>_of_\<alpha>
    by blast
  then show ?thesis unfolding xs_ys 
    by (simp add: zip_map2)
qed

text \<open>Finnaly, conclude the statement that interpolate_on is equivalent to computing Commit.
This is what the prior 3 lemmas where building up to.\<close>
lemma interpolate_on_is_Commit:
  assumes dist: "distinct (map fst xs_ys)"
  and length_xs_ys: "length xs_ys \<le> max_deg+1"
shows "interpolate_on (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha> = g_pow_PK_Prod 
    (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys)"
proof -
  have "interpolate_on (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha>  
  =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)"
    by(rule interpolate_on_\<alpha>_is_\<phi>_of_\<alpha>[OF assms])
  also have "\<dots> = g_pow_PK_Prod 
    (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys)"
  proof -
    have "degree (lagrange_interpolation_poly xs_ys) \<le> max_deg"
      by (meson assms(2) degree_lagrange_interpolation_poly le_diff_conv le_trans nat_le_iff_add)
    then show "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (lagrange_interpolation_poly xs_ys) \<alpha> = g_pow_PK_Prod 
    (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys)"
    using g_pow_PK_Prod_correct by presburger
  qed
  finally show ?thesis by fast
qed

lemma split_pow_div_G\<^sub>p:
  shows "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (y/x) = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/x)"
  by (metis mod_ring_pow_pow_G\<^sub>p mult_cancel_left2 times_divide_eq_right)


text \<open>Show that the witness emulation from the reduction adversary, is equivalent to computing 
Eval if \<alpha> \<notin> I.\<close>
lemma witness_calc_correct: 
  assumes dist: "distinct (map fst xs_ys)"
  and length_xs_ys: "length xs_ys \<le> max_deg + 1"
  and \<alpha>_nin_xs: "\<alpha> \<notin> set (map fst (tl xs_ys))"
  shows "map (\<lambda>i. (Eval (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (\<alpha> ^ t)) [0..<max_deg + 1]) () (lagrange_interpolation_poly xs_ys) i)) (map fst (tl xs_ys))
    =  map (\<lambda>(x,y). (y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (tl xs_ys)"
proof -
  have "?thesis = (map (\<lambda>(x,y). (Eval (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (\<alpha> ^ t)) [0..<max_deg + 1]) () (lagrange_interpolation_poly xs_ys) x)) (tl xs_ys)
  = map (\<lambda>(x,y). (y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (tl xs_ys))"
    by auto
  also have "\<dots>"
  proof- 
    have "\<And>x y. (x,y) \<in> set (tl xs_ys) \<Longrightarrow> 
      Eval (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) () (lagrange_interpolation_poly xs_ys) x
     =  (y, (\<^bold>g ^ poly (lagrange_interpolation_poly xs_ys) \<alpha> \<otimes> inv (\<^bold>g ^ y)) ^
                (1 / (\<alpha> - x)))"
    proof -
      fix x y
      assume asm: "(x, y) \<in> set (tl xs_ys)"
      let ?\<phi> = "lagrange_interpolation_poly xs_ys"

      have y: "poly (lagrange_interpolation_poly xs_ys) x = y"
          by (rule lagrange_interpolation_poly[OF assms(1)])(simp add: asm calculation in_set_tlD)+

      have deg_\<psi>_le: "degree (\<psi>_of (?\<phi>) x) \<le> max_deg"
        by (meson degree_lagrange_interpolation_poly degree_q_le_\<phi> le_diff_conv le_trans
            length_xs_ys)

      have \<alpha>_neg_x: "\<alpha> \<noteq> x"
        by (metis (mono_tags, lifting) asm assms(1,3) distinct_tl entries_keysD entries_of_alist
            keys_of_alist map_tl prod.sel(1))

      then have \<psi>_unfold: "poly (\<psi>_of ?\<phi> x) \<alpha> = (poly ?\<phi> \<alpha> - poly ?\<phi> x) / (\<alpha> - x)"
        by (simp add: \<phi>x_m_\<phi>u_eq_xmu_\<psi>x)

      show "Eval (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) () (lagrange_interpolation_poly xs_ys) x
     =  (y, (\<^bold>g ^ poly (lagrange_interpolation_poly xs_ys) \<alpha> \<otimes> inv (\<^bold>g ^ y)) ^
                (1 / (\<alpha> - x)))"
      unfolding Eval_def Let_def
      apply (rule prod_eqI)
      apply (metis asm dist in_set_tlD lagrange_interpolation_poly prod.sel(1))
      apply (simp only: prod.sel(2) g_pow_PK_Prod_correct[OF deg_\<psi>_le])
      apply (simp only: \<psi>_unfold)
      apply (simp only: y)
      apply (simp only:  split_pow_div_G\<^sub>p)
      apply (simp only: mod_ring_pow_mult_inv_G\<^sub>p)
      done
    qed
    then show ?thesis by auto
  qed
  finally show ?thesis by fast
qed

corollary witness_calc_helper:
  assumes "length I = max_deg \<and> distinct I"
  and "\<alpha> \<notin> set I"
  and "evals
       \<in> set_spmf
           (map_spmf (map (\<lambda>x. of_int_mod_ring (int x)))
             (sample_uniform_list (max_deg + 1) (order G\<^sub>p)))"
shows "map (\<lambda>i. (Eval (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (\<alpha> ^ t)) [0..<max_deg + 1]) () (lagrange_interpolation_poly  (zip (PickDistinct I # I) evals)) i)) I
    =  map2 (\<lambda>x y. (y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly  (zip (PickDistinct I # I) evals)) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) I (tl evals)"
proof - 
  obtain xs_ys where xs_ys: "xs_ys = (zip (PickDistinct I # I) evals)" by fast
  have hlength: "length evals = length (PickDistinct I#I)"
      using assms(3,1) by force
  then have h1: "map fst (tl (zip (PickDistinct I # I) evals)) = I"
      by (metis list.sel(3) map_fst_zip map_tl)
  have h2: "(tl (zip (PickDistinct I # I) evals)) = zip I (tl evals)" 
    by (metis hlength h1 map_snd_zip map_tl xs_ys zip_map_fst_snd)
  have asm1: "distinct (map fst xs_ys)" unfolding xs_ys using assms(1)
    by (metis CARD_q PickDistinct d_l_p distinct_take map_fst_zip_take of_nat_less_imp_less)
  moreover have asm2: "length xs_ys \<le> max_deg + 1" unfolding xs_ys using assms(1) by force 
  moreover have asm3: "\<alpha> \<notin> set (map fst (tl xs_ys))"
  proof (rule ccontr)
    have tl_move: "tl xs_ys = zip I (tl evals)" unfolding xs_ys
      by (metis list.sel(2,3) neq_Nil_conv zip.simps(1) zip_Cons_Cons)
    assume "\<not> \<alpha> \<notin> set (map fst (tl xs_ys))"
    then have "\<alpha> \<in> set (map fst (tl xs_ys))" by linarith
    then obtain y where y: "(\<alpha>,y) \<in> set (tl xs_ys)" by fastforce
    then have "\<alpha> \<in> set I" by (simp only: tl_move set_zip_leftD)
    then show "False" using assms(2) by blast
  qed
  
  ultimately have "map (\<lambda>i. (Eval (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (\<alpha> ^ t)) [0..<max_deg + 1]) () (lagrange_interpolation_poly xs_ys) i)) (map fst (tl xs_ys))
    =  map (\<lambda>(x,y). (y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (tl xs_ys)"
    using witness_calc_correct by blast
  then show ?thesis unfolding xs_ys 
    using h1 h2 by argo
qed
 

text \<open>show that converting a nat to a finite field element is injective on the natural numbers that 
are less than the cardinality of the finite field.\<close>
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

text \<open>The proof goal is to show that the probabillity of winning the hiding game is less than or 
equal to winning the DL game. We start with the hiding game transform it via game-based methods into 
the DL game (with some reduction adversary).

We define 4 new games as subgoals in our proof:
- game1
- game2 
- game2_w_asert
- game2_wo_assert

The proof is structered into 5 steps, each step targets one subgoal, except the fifth one, where the 
trarget is DL game: 

1. Transform the hiding game into game 1. We exchange Commit with interpolate_on and prepare the 
game to easily replace CreateWitness with the witness emulation of the reduction adversary. We use 
only game hops based on bridging steps in this step.
  
2. We use a game-hop based on a failure event to transform game1 into game2. We extract the 
negligible probabillity that \<alpha> is contained in I, as in that case, CreateWitness is not the same as 
the emulation in the reduction adversary. 

3. We use game-hops based on bridging steps to explicitly restate game2 as game2_w_assert. 
We extract the assert that the adversary guessed polynomial \<phi>' equals \<phi>, which is part of the hiding 
game but not of the DL reduction.

4. We use over-estimation to drop the \<phi>'= \<phi>-assert. We obtain game2_wo_assert from game2_w_assert.

5. We transform game2_wo_assert into the DL game using game hops based on bridging steps.

For a more intuitive understanding of the steps go to the final theorem at the end of the file.
\<close>

text \<open>The hiding game with interpolate_on instead of Commit and the random sampling of \<phi> split up 
into sampling random points for interpolate_on.\<close>
definition game1 :: "('a vk, 'e argument, 'state) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> bool spmf" where 
  "game1 \<A>1 \<A>2 = TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int::nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let W = map (\<lambda>j. Eval PK () \<phi> j) I;
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I W;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"

text \<open>game1 with the reduction adversaries emulation instead of CreateWitness\<close>
definition game2 :: "('a vk, 'e argument, 'state) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> bool spmf" where 
  "game2 \<A>1 \<A>2 = TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"

text \<open>game 2 with extracted \<phi> = \<phi>'-assert\<close>
definition game2_w_assert :: "('a vk, 'e argument, 'state) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> bool spmf" where 
  "game2_w_assert \<A>1 \<A>2 = TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf (hd evals = poly \<phi>' i)} ELSE return_spmf False"

text \<open>game2_w_asssert without the assert.\<close>
definition game2_wo_assert :: "('a vk, 'e argument, 'state) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> bool spmf" where 
  "game2_wo_assert \<A>1 \<A>2 = TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK; 
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  return_spmf (hd evals = poly \<phi>' i)} ELSE return_spmf False"

lemma PickDistinct_Prop: "length a = max_deg \<and> distinct a
  \<Longrightarrow> distinct (PickDistinct a#a) \<and> length (PickDistinct a#a) = max_deg + 1"
  by (metis CARD_q PickDistinct Suc_eq_plus1 d_l_p length_Cons
      of_nat_less_iff)

corollary PickDistinct_Prop' : "length a = max_deg \<and> distinct a \<and> valid_poly \<phi>
  \<Longrightarrow> distinct (PickDistinct a#a) \<and> length (PickDistinct a#a) = max_deg + 1"
  using PickDistinct_Prop by presburger

lemma distinct_map_fst_zip: "distinct a \<Longrightarrow> distinct (map fst (zip a b))"
  by (simp add: map_fst_zip_take)

lemma card_eq_ord: "CARD('e) = order G\<^sub>p"
  using CARD_q CARD_G\<^sub>p by force

text \<open>Step 1 of the proof.\<close>
lemma hiding_game_to_game1:
shows "spmf (weak_eval_hiding_game \<A>1 \<A>2) True = spmf (game1 \<A>1 \<A>2) True"
 (is "?lhs = ?rhs")
proof -
  text \<open>We unfold the weak eval hiding game\<close>
  have "?lhs = spmf (TRY do {
  p::'e mod_ring poly \<leftarrow> sample_uniform_poly max_deg;
  (ck, vk) \<leftarrow> key_gen;
  (I,\<sigma>) \<leftarrow> do {
    (I,\<sigma>) \<leftarrow> \<A>1 vk;
    _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
    return_spmf (I,\<sigma>)
    };
  (c,d) \<leftarrow> commit ck p; 
  let W = map (\<lambda>i. Eval ck d p i) I; 
  p' \<leftarrow> \<A>2 vk \<sigma> c I W;
  return_spmf (p = p')} ELSE return_spmf False) True"
    unfolding weak_eval_hiding_game_def eval_hiding_game_def weak_eval_hiding_adversary1_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])(simp)
  also have "\<dots> = spmf (TRY do {
  p::'e mod_ring poly \<leftarrow> sample_uniform_poly max_deg;
  (ck, vk) \<leftarrow> key_gen;
  (I,\<sigma>) \<leftarrow> \<A>1 vk;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  (c,d) \<leftarrow> commit ck p; 
  let W = map (\<lambda>i. Eval ck d p i) I; 
  p' \<leftarrow> \<A>2 vk \<sigma> c I W;
  return_spmf (p = p')} ELSE return_spmf False) True"
    by (simp add: bind_spmf_assoc key_gen_def bind_map_spmf o_def Setup_def split_def Let_def 
       del: PickDistinct.simps)
  text \<open>sample phi uniform random is sampling evaluation points for the adversaries I uniform random\<close>
  also have "\<dots> = spmf (TRY do {
  (ck, vk) \<leftarrow> key_gen;
  (I,\<sigma>) \<leftarrow> \<A>1 vk;
  p::'e mod_ring poly \<leftarrow> do {
    _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
    evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (max_deg+1) (CARD ('e)));
    let i = PickDistinct I;
    return_spmf (lagrange_interpolation_poly (zip (i#I) evals))
    };
  (c,d) \<leftarrow> commit ck p; 
  let W = map (\<lambda>i. Eval ck d p i) I; 
  p' \<leftarrow> \<A>2 vk \<sigma> c I W;
  return_spmf (p = p')} ELSE return_spmf False) True"
    apply (rule spmf_eqI')
    apply (rule unpack_try_spmf)
    apply (subst bind_commute_spmf; rule unpack_bind_spmf';rule ext; 
        simp 
        split: prod.splits 
        add: split_paired_all 
        del: return_bind_spmf bind_spmf_assoc PickDistinct.simps)+
    apply (subst bind_commute_spmf)
    apply (subst bind_spmf_assoc)
    apply (rule assert_based_eq)
    apply (drule PickDistinct_Prop) 
    apply (subst sample_uniform_evals_is_sample_poly[of "(PickDistinct aa # aa)" max_deg])
    apply simp+
    done
  text \<open>Now we bring the game in a nicer form and expose the Setup from key_gen\<close>
  also have "\<dots> = spmf(TRY do {
  \<alpha>::'e mod_ring \<leftarrow>  map_spmf (\<lambda>x. of_int_mod_ring (int x)) (sample_uniform (order G\<^sub>p));
  let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (max_deg+1) (CARD ('e)));
  let i = PickDistinct I;
  let p = (lagrange_interpolation_poly (zip (i#I) evals));
  (c,d) \<leftarrow> commit PK p; 
  let W = map (\<lambda>i. Eval PK d p i) I; 
  p' \<leftarrow> \<A>2 PK \<sigma> c I W;
  return_spmf (p = p')} ELSE return_spmf False) True"
   by (simp add: bind_spmf_assoc key_gen_def bind_map_spmf o_def Setup_def split_def Let_def 
       del: PickDistinct.simps)
  text \<open>Now we replace the Commit computed with a valid public key PK by interpolate_on\<close>
  also have "\<dots> = spmf(TRY do {
  \<alpha>::'e mod_ring \<leftarrow>  map_spmf (\<lambda>x. of_int_mod_ring (int x)) (sample_uniform (order G\<^sub>p));
  let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (max_deg+1) (CARD ('e)));
  let i = PickDistinct I;
  let p = (lagrange_interpolation_poly (zip (i#I) evals));
  let exp_evals = map (\<lambda>i. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let W = map (\<lambda>i. Eval PK () p i) I; 
  p' \<leftarrow> \<A>2 PK \<sigma> C I W;
  return_spmf (p = p')} ELSE return_spmf False) True"
    apply (rule spmf_eqI')
    apply (simp only: Let_def split_def)
    apply (rule unpack_try_spmf; rule unpack_bind_spmf')+
    apply (rule ext; simp split: prod.splits add: split_paired_all 
        del: return_bind_spmf bind_spmf_assoc PickDistinct.simps One_nat_def; 
        rule unpack_bind_spmf'; rule ext)
    apply (rule assert_based_eq)
    apply (simp split: prod.splits add: split_paired_all 
        del: return_bind_spmf bind_spmf_assoc PickDistinct.simps One_nat_def)
    apply (drule PickDistinct_Prop)
    apply (simp only: commit_def return_bind_spmf bind_return_spmf)
    apply (subst interpolate_on_is_Commit[symmetric, of ])
      apply (simp add: map_fst_zip_take)
       apply simp
      apply (simp add: zip_map2)
      done
  also have "\<dots> = ?rhs" 
    by (simp add: game1_def Setup_def Let_def split_def card_eq_ord bind_map_spmf o_def 
        return_bind_spmf bind_return_spmf bind_spmf_assoc 
        del: PickDistinct.simps)
  finally show ?thesis .
qed

lemma lossless_mod_ring_list: "lossless_spmf (map_spmf (map (\<lambda>x. of_int_mod_ring (int x)::'e mod_ring))
            (sample_uniform_list (max_deg + 1) (order G\<^sub>p)))"
  by (simp add: G\<^sub>p.order_gt_0)

text \<open>Step 2 of the proof:\<close>
lemma fundamental_lemma_game1_game2: 
  assumes lossless_\<A>1: "\<And>PK . lossless_spmf (\<A>1 PK)"
  and lossless_\<A>2: "\<And>PK \<sigma> C I W . lossless_spmf (\<A>2 PK \<sigma> C I W)"
  shows "spmf (game1 \<A>1 \<A>2) True \<le> spmf (game2 \<A>1 \<A>2) True + t_DL_G\<^sub>p.advantage (reduction_tDL \<A>1)"
proof -
  note [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD map_spmf_bind_spmf bind_spmf_const Let_def o_def
  note %invisible [cong del] = if_weak_cong 
   and [split del] = if_split
   and [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD map_spmf_bind_spmf bind_spmf_const
   and [if_distribs] = if_distrib[where f="\<lambda>x. try_spmf x _"] if_distrib[where f="weight_spmf"] if_distrib[where f="\<lambda>r. scale_spmf r _"]

  define game1b :: "('a vk, 'e argument, 'f) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'f)
  eval_hiding_adversary2 \<Rightarrow> (bool\<times>bool) spmf"
    where "game1b \<A>1 \<A>2 = TRY do {
  \<alpha>::'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int::nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let W = map (\<lambda>j. Eval PK () \<phi> j) I;
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I W;
  return_spmf (\<phi> = \<phi>', \<alpha> \<in> set (PickDistinct I#I))} ELSE return_spmf (False,False)"
    for \<A>1 \<A>2

  text \<open>show game1 is game1b with random sampling, filtered for the first result i.e. neglecting 
  whether the failure event occured\<close>
  have game1b: "game1 \<A>1 \<A>2 = map_spmf fst (game1b \<A>1 \<A>2)"
  proof -
    have "game1 \<A>1 \<A>2 = TRY do {
      \<alpha> :: 'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
      let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      (I,\<sigma>) \<leftarrow> \<A>1 PK;
      _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
      let i = PickDistinct I;
      evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int::nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
      let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
      let exp_evals = map (\<lambda>i. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i) evals;
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let W = map (\<lambda>j. Eval PK () \<phi> j) I;
      \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I W;
    return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
      by (simp add: bind_map_spmf o_def game1_def Setup_def Let_def)
    also have "\<dots> = map_spmf fst (game1b \<A>1 \<A>2)"
      unfolding game1b_def
      apply (simp add: map_try_spmf try_spmf_bind_spmf_lossless lossless_\<A>1 
          del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
      apply (rule unpack_try_spmf)
      apply (rule unpack_bind_spmf';rule ext)+
      apply (simp split: prod.splits add: split_paired_all 
          del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
      done
    finally show ?thesis .
  qed

   define game2b :: "('a vk, 'e argument, 'f) eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'f)
  eval_hiding_adversary2 \<Rightarrow> (bool\<times>bool) spmf"
    where "game2b \<A>1 \<A>2 = TRY do {
  \<alpha>::'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  return_spmf (\<phi> = \<phi>', \<alpha> \<in> set (PickDistinct I#I))} ELSE return_spmf (False, False)" 
    for \<A>1 \<A>2

  text \<open>accordingly we show game2 is game2b with random sampling, filtered for the first result 
  i.e. neglecting whether the failure event occured\<close>
  have game2b: "game2 \<A>1 \<A>2 = map_spmf fst (game2b \<A>1 \<A>2)"
  proof -
    have "game2 \<A>1 \<A>2 = TRY do {
    \<alpha> :: 'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
    let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
    (I,\<sigma>) \<leftarrow> \<A>1 PK;
      _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
    let i = PickDistinct I;
    evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
    let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
    let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
    \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
    return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
      by (simp add: bind_map_spmf o_def game2_def Setup_def Let_def)
    also have "\<dots> = map_spmf fst (game2b \<A>1 \<A>2)"
      unfolding game2b_def
      apply (simp add: map_try_spmf try_spmf_bind_spmf_lossless lossless_\<A>1 
          del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
      apply (rule unpack_try_spmf)
      apply (rule unpack_bind_spmf';rule ext)+
      apply (simp split: prod.splits add: split_paired_all 
          del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
      done
    finally show ?thesis .
  qed

  text \<open>We capture the failure event (i.e. \<alpha> \<in> I) in the collision game.\<close>
  define collision_game :: "('a vk, 'e argument, 'f) eval_hiding_adversary1 \<Rightarrow> bool spmf" where 
  "collision_game \<A>1 = TRY do {
     \<alpha>::'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
     _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I); 
     return_spmf (\<alpha> \<in> set (PickDistinct I#I))} ELSE return_spmf False" for \<A>1

  text \<open>We show that the second result of game1b captures the failure event, i.e. is the collision 
  game.\<close>
  have map_snd_game1_is_collision_game: "map_spmf snd (game1b \<A>1 \<A>2) = collision_game \<A>1"
    apply (simp only: game1b_def collision_game_def)
    apply (simp add: map_try_spmf try_spmf_bind_spmf_lossless lossless_\<A>1
          del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
    apply (rule unpack_try_spmf)
    apply (rule unpack_bind_spmf';rule ext)+
    apply (simp split: prod.splits add: split_paired_all 
          del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def) (* return_bind_spmf*)
    apply (rule unpack_bind_spmf';rule ext) 
    apply (simp add: map_try_spmf del: PickDistinct.simps One_nat_def bind_spmf_assoc bind_spmf_const)
    apply (simp only: try_spmf_bind_spmf_lossless try_spmf_lossless 
        lossless_mod_ring_list lossless_\<A>2 lossless_return_spmf 
        bind_spmf_independent_return_spmf)
    done

   text \<open>We show that the second result of game1b captures the failure event, i.e. is the collision 
  game.\<close>
  have map_snd_game1_is_collision_game': "map_spmf snd (game1b \<A>1 \<A>2) = collision_game \<A>1"
    apply (simp only: game1b_def collision_game_def)
    apply (simp add: map_try_spmf try_spmf_bind_spmf_lossless lossless_\<A>1
          del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
    apply (rule unpack_try_spmf)
    apply (rule unpack_bind_spmf';rule ext)+
    apply (simp split: prod.splits add: split_paired_all 
          del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
    apply (rule unpack_bind_spmf';rule ext) 
    apply (simp add: map_try_spmf del: PickDistinct.simps One_nat_def bind_spmf_assoc bind_spmf_const)
    apply (simp only: try_spmf_bind_spmf_lossless try_spmf_lossless 
        lossless_mod_ring_list lossless_\<A>2 lossless_return_spmf 
        bind_spmf_independent_return_spmf)
    done

   text \<open>Before we start performing the game-hop with the fundamental lemma, we state the 
  probability of winning the failure event. That is less than or equal to breaking the 
  t-DL assumption\<close>
  have spmf_collision_game: "spmf (collision_game \<A>1) True
  \<le> t_DL_G\<^sub>p.advantage (reduction_tDL \<A>1)"
  proof -
    have "spmf (collision_game \<A>1) True = spmf (TRY do {
     x \<leftarrow> sample_uniform (order G\<^sub>p);
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) x;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
     _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I); 
     return_spmf (\<alpha> \<in> set (PickDistinct I#I))} ELSE return_spmf False) True"
      by (simp add: collision_game_def bind_map_spmf o_def del: PickDistinct.simps)
     also have "\<dots> = spmf (TRY do {
     x \<leftarrow> sample_uniform (order G\<^sub>p);
     TRY do {
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) x;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
      TRY do {
     _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I); 
      TRY do {
     _ :: unit \<leftarrow> assert_spmf (\<alpha> \<in> set (PickDistinct I#I));
     return_spmf True} ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False
    } ELSE return_spmf False) True"
       unfolding Let_def split_def
       apply (simp only: return_spmf_assert[symmetric])
       apply (fold try_bind_spmf_lossless2[OF lossless_return_spmf]) 
       apply (simp)
       done
     also have "\<dots> = spmf (TRY do {
     x \<leftarrow> sample_uniform (order G\<^sub>p);
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) x;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
     _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I); 
     _ :: unit \<leftarrow> assert_spmf (\<alpha> \<in> set (PickDistinct I#I));
     return_spmf True} ELSE return_spmf False) True"
       unfolding Let_def split_def
        by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
     also have "\<dots> = spmf (TRY do {
     x \<leftarrow> sample_uniform (order G\<^sub>p);
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) x;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
     _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I \<and> \<alpha> \<in> set (PickDistinct I#I)); 
     return_spmf True} ELSE return_spmf False) True"
       by (simp add: assert_collapse 
           del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
      also have "\<dots> = spmf (TRY do {
     x \<leftarrow> sample_uniform (order G\<^sub>p);
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) x;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
     let (\<alpha>'::'e mod_ring) = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = PK!1) (PickDistinct I#I)) of Some x => x | None => 1);
     _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I \<and> \<alpha> \<in> set (PickDistinct I#I)); 
     _ :: unit \<leftarrow> assert_spmf (\<alpha> = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1) (PickDistinct I#I)) of Some x => x | None => 1)); 
     return_spmf True} ELSE return_spmf False) True"
        apply (simp only: Let_def)
        apply (subst exchange_lem)
        apply (simp add: assert_collapse 
            del: bind_spmf_const PickDistinct.simps One_nat_def)
        done
       also have "\<dots> \<le> spmf (TRY do {
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) \<alpha>;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
     let \<alpha>' = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = PK!1) (PickDistinct I#I)) of Some x => x | None => 1);
      _ :: unit \<leftarrow> assert_spmf (\<alpha> = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1) (PickDistinct I#I)) of Some x => x | None => 1));
     return_spmf True
      } ELSE return_spmf False) True"
         apply(simp only: Let_def split_def)
         apply (rule try_spmf_le)
         apply (rule bind_spmf_le)+
         apply (simp add: del_assert del: bind_spmf_const PickDistinct.simps One_nat_def)
         done
       also have "\<dots> = spmf (TRY do {
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
     TRY do {
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) \<alpha>;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
     TRY do {
     let \<alpha>' = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = PK!1) (PickDistinct I#I)) of Some x => x | None => 1);
     return_spmf (\<alpha> = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1) (PickDistinct I#I)) of Some x => x | None => 1))
      } ELSE return_spmf False
      } ELSE return_spmf False
      } ELSE return_spmf False) True"
       unfolding Let_def split_def
       apply (simp only: return_spmf_assert)
       apply (fold try_bind_spmf_lossless2[OF lossless_return_spmf]) 
       apply (simp del: PickDistinct.simps One_nat_def)
       done
      also have "\<dots> = spmf (TRY do {
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) \<alpha>;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (I,\<sigma>) \<leftarrow> \<A>1 PK;
     let \<alpha>' = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = PK!1) (PickDistinct I#I)) of Some x => x | None => 1);
     return_spmf (\<alpha> = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1) (PickDistinct I#I)) of Some x => x | None => 1))
      } ELSE return_spmf False) True"
        by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
      also have "\<dots> = spmf (TRY do {
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) \<alpha>;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     \<alpha>' \<leftarrow> do {
        (I,\<sigma>) \<leftarrow> \<A>1 PK;
        let (\<alpha>'::'e mod_ring) = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = PK!1) (PickDistinct I#I)) of Some x => x | None => 1);
        return_spmf \<alpha>'};
     return_spmf (\<alpha> = \<alpha>')
      } ELSE return_spmf False) True"
        unfolding Let_def split_def by force
      also have "\<dots> = t_DL_G\<^sub>p.advantage (reduction_tDL \<A>1)"
        unfolding t_DL_G\<^sub>p.advantage_def t_DL_G\<^sub>p.game_def reduction_tDL.simps Let_def split_def
        by (simp add: return_bind_spmf bind_spmf_assoc del: PickDistinct.simps One_nat_def Let_def)
      finally show ?thesis .
    qed
  
  text \<open>We now use relation reasoning to state that game1 and game2 are equal except for the 
  failure event.\<close>
  have "rel_spmf (\<lambda>(win, bad) (win', bad'). (bad \<longleftrightarrow> bad') \<and> (\<not> bad' \<longrightarrow> win \<longleftrightarrow> win')) (game1b \<A>1 \<A>2) (game2b \<A>1 \<A>2)"
    apply (simp only: game1b_def game2b_def)
    apply (intro rel_spmf_try_spmf)
     apply (simp del: bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
     apply (rule rel_spmf_bind_reflI)
     apply (rule rel_spmf_bind_reflI)
     apply (simp split: prod.splits add: split_paired_all 
        del: return_bind_spmf bind_spmf_const bind_spmf_assoc PickDistinct.simps One_nat_def)
     apply (rule rel_spmf_bind_assert_reflI)
     apply (rule rel_spmf_bind_reflI)
     apply (rename_tac \<alpha> I \<sigma> evals)
     apply (case_tac "\<alpha> \<in> set I")
      apply (simp add: rel_spmf_bindI1 rel_spmf_bindI2 lossless_\<A>2 
              del: PickDistinct.simps One_nat_def bind_spmf_assoc bind_spmf_const)
     apply (rule rel_spmf_bindI[of "(=)"])
      apply (simp only: spmf_rel_eq)
      apply (simp add: witness_calc_helper interpolate_on_\<alpha>_is_\<phi>_of_\<alpha>_helper
              del: PickDistinct.simps One_nat_def bind_spmf_assoc bind_spmf_const)
     apply (simp del: PickDistinct.simps One_nat_def bind_spmf_assoc bind_spmf_const)+
    done
  text \<open>We use the fundamental lemma to conclude that the difference in winnig one or the other game 
  differs at most in the probability of the failure event.\<close>
  hence "\<bar>measure (measure_spmf (game1b \<A>1 \<A>2)) {(win, _). win} - measure (measure_spmf (game2b \<A>1 \<A>2)) {(win, _). win}\<bar>
      \<le> measure (measure_spmf (game1b \<A>1 \<A>2)) {(_, bad). bad}"
  unfolding split_def by(rule fundamental_lemma)
  moreover have "measure (measure_spmf (game1b \<A>1 \<A>2)) {(win, _). win} = spmf (map_spmf fst (game1b \<A>1 \<A>2)) True"
    and "measure (measure_spmf (game2b \<A>1 \<A>2)) {(win, _). win} = spmf (map_spmf fst (game2b \<A>1 \<A>2)) True"
    and "measure (measure_spmf (game1b \<A>1 \<A>2)) {(_, bad). bad} = spmf (map_spmf snd (game1b \<A>1 \<A>2)) True"
      unfolding spmf_conv_measure_spmf measure_map_spmf by(auto simp add: vimage_def split_def)
 text \<open>We use this to overestimate the probability of game1 by the probability of winning game2 
 plus the probability of the failure event happening\<close>
 ultimately have
    "\<bar>spmf (map_spmf fst (game1b \<A>1 \<A>2)) True - spmf (map_spmf fst (game2b \<A>1 \<A>2)) True\<bar>
    \<le> spmf (map_spmf snd (game1b \<A>1 \<A>2)) True"
    by simp
  then have "spmf (map_spmf fst (game1b \<A>1 \<A>2)) True \<le> spmf (map_spmf fst (game2b \<A>1 \<A>2)) True 
    + spmf (map_spmf snd (game1b \<A>1 \<A>2)) True"
    by linarith
  then show ?thesis
    unfolding game1b game2b map_snd_game1_is_collision_game 
    using spmf_collision_game
    by force
qed


text \<open>Step 3 of the proof:\<close>
lemma game2_le_DL: "spmf (game2 \<A>1 \<A>2) True \<le> DL_G\<^sub>p.advantage (reduction \<A>1 \<A>2)"
  (is "?lhs \<le> ?rhs")
proof -
  have "?lhs = spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  TRY do{
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  TRY do{
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  TRY do{
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  TRY do{
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  TRY do{
  _ :: unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf True
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False) True"
    unfolding game2_def split_def Let_def split_def
    apply (simp only: return_spmf_assert[symmetric])
    apply (fold try_bind_spmf_lossless2[OF lossless_return_spmf])
    apply (simp del: PickDistinct.simps) 
    done
  also have "\<dots> = spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  _ :: unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf True
  } ELSE return_spmf False) True"
    unfolding Let_def split_def 
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])
       (simp del: PickDistinct.simps One_nat_def) 
   text \<open>next we show that the assert \<phi> = \<phi>' implies `hd evals = poly \<phi>' (PickDistinct I)`, which is 
 asserted by the Dl reduction game. Hence we add `hd evals = poly \<phi>' (PickDistinct I)` to the 
 assert without changing the game.\<close>
   also have "\<dots> = spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  _ :: unit \<leftarrow> assert_spmf (\<phi> = \<phi>' \<and> hd evals = poly \<phi>' i);
  return_spmf True
  } ELSE return_spmf False) True"
  proof -
    have equi: "\<And>I evals \<phi>'. length I = max_deg \<and> distinct I 
      \<Longrightarrow> evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) 
          (sample_uniform_list (max_deg+1) (order G\<^sub>p)))  
      \<Longrightarrow> ((lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>' 
      \<longleftrightarrow> (lagrange_interpolation_poly (zip (PickDistinct I#I) evals)) = \<phi>' 
           \<and> hd evals = poly \<phi>' (PickDistinct I)))"
    proof -
      fix I evals :: "'e mod_ring list"
      fix \<phi>'
      assume asm1: "length I = max_deg \<and> distinct I"
      assume asm2: "evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p)))"
      then have evals_length: "length evals = max_deg+1"
        by (force simp add: bind_map_spmf o_def)
      show "(lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>' 
      \<longleftrightarrow> lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>' \<and> hd evals = poly \<phi>' (PickDistinct I))"
      proof
        show "lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>' \<Longrightarrow> lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>' \<and> hd evals = poly \<phi>' (PickDistinct I)"
        proof 
          assume asm: "lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>'"
          show "hd evals = poly \<phi>' (PickDistinct I)"
          proof(rule lagrange_interpolation_poly[symmetric, of "zip (PickDistinct I#I) evals"])
            show "distinct (map fst (zip (PickDistinct I#I) evals))"
              using PickDistinct_Prop asm1 distinct_map_fst_zip by blast
            show "\<phi>' = lagrange_interpolation_poly (zip (PickDistinct I#I) evals)"
              using asm[symmetric] .
            show "(PickDistinct I, hd evals) \<in> set (zip (PickDistinct I#I) evals)" 
              using asm1 evals_length
              by (metis Nil_eq_zip_iff add_is_0 hd_in_set hd_zip length_0_conv list.discI list.sel(1) rel_simps(92))
          qed
        qed 
      qed simp
    qed
    show ?thesis 
      unfolding split_def Let_def
      apply (rule spmf_eqI')
      apply (rule unpack_try_spmf)
      apply (rule unpack_bind_spmf'; rule ext)
      apply (rule unpack_bind_spmf'; rule ext)
      apply (rule assert_based_eq)
      apply (rule bind_spmf_cong)
       apply simp
      apply (rule unpack_bind_spmf'; rule ext)
      apply (rule unpack_bind_spmf)
      apply (subst equi)
        apply (simp_all)
      done
  qed
    text \<open>In the next part we split the conjuncture `\<phi> = \<phi>' \<and> hd evals = poly \<phi>' (PickDistinct I)` 
  into two separate assert statements, so we can use overestimation at a later step to get closer 
  to the DL game.\<close>
  also have "\<dots> = spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  _ :: unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  _ :: unit \<leftarrow> assert_spmf (hd evals = poly \<phi>' i);
  return_spmf True
  } ELSE return_spmf False) True"
    by (simp only: assert_collapse)
 also have "\<dots> = spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  TRY do {
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  TRY do {
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  TRY do {
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  TRY do {
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  TRY do {
  _ :: unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  TRY do {
  return_spmf (hd evals = poly \<phi>' i)
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False) True"
   apply (simp only: split_def Let_def)
   apply (subst return_spmf_assert)
   apply (fold try_bind_spmf_lossless2[OF lossless_return_spmf])
   apply (simp del: PickDistinct.simps)
   done
  also have "\<dots> = spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  _ :: unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf (hd evals = poly \<phi>' i)
  } ELSE return_spmf False) True"
    unfolding Let_def split_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])(simp del: PickDistinct.simps)
  also have "\<dots> \<le> spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  _ :: unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf (hd evals = poly \<phi>' i)
  } ELSE return_spmf False) True"
    apply (simp only:Let_def split_def)
    apply (rule try_spmf_le)
    apply (rule bind_spmf_le)+
    apply (simp only: del_assert)
    done
  also have "\<dots> \<le> spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  return_spmf (hd evals = poly \<phi>' i)
  } ELSE return_spmf False) True"
    apply (simp only:Let_def split_def)
    apply (rule try_spmf_le)
    apply (rule bind_spmf_le)+
    apply (simp only: del_assert)
    done
    text \<open>Next, we split the random sampled list up into a random point concatenated with a 
  one element shorter random list. The random point represents the DL value which creates later 
  the DL instance.\<close>
  also have "\<dots> = spmf (TRY do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  let i = PickDistinct I;
  a \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  plain_evals \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let evals = \<^bold>g ^ a # map (\<lambda>i. \<^bold>g ^ i) plain_evals;
  let C = interpolate_on (zip (i#I) evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I plain_evals);
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  return_spmf (a = poly \<phi>' i)
  } ELSE return_spmf False) True"
    using pretty_Cons_random_list_split p_gr_two CARD_G\<^sub>p 
    by(simp add: bind_map_spmf o_def Let_def del: PickDistinct.simps)
  text \<open>Lastly, we extract the functions from the reduction adversary into an do-block to mirror 
  the DL game.\<close>
  also have "\<dots> = spmf (TRY do {
  a \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  let i = PickDistinct I;
  plain_evals \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let evals = \<^bold>g ^ a # map (\<lambda>i. \<^bold>g ^ i) plain_evals;
  let C = interpolate_on (zip (i#I) evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I plain_evals);
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  return_spmf (a = poly \<phi>' i)
  } ELSE return_spmf False) True"
    apply (simp only: Let_def split_def)
    apply (subst bind_commute_spmf)
    apply (subst bind_commute_spmf)
    apply (blast)
    done
  also have "\<dots> = spmf (TRY do {
  a \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  a' \<leftarrow> do {
  (\<alpha>, PK) \<leftarrow> Setup;
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  let i = PickDistinct I;
  plain_evals \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let evals = \<^bold>g ^ a # map (\<lambda>i. \<^bold>g ^ i) plain_evals;
  let C = interpolate_on (zip (i#I) evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I plain_evals);
  \<phi>' \<leftarrow> \<A>2 PK \<sigma> C I witn_tupel;
  return_spmf (poly \<phi>' i)};
  return_spmf (a =a')
  } ELSE return_spmf False) True"
    by (simp add: Let_def split_def o_def del: PickDistinct.simps)
   also have "\<dots> = DL_G\<^sub>p.advantage (reduction \<A>1 \<A>2)"
    unfolding DL_G\<^sub>p.advantage_def DL_G\<^sub>p.game_alt_def2 reduction.simps ..
  finally show ?thesis .
qed

text \<open>Finally we assemble all proof steps for the weak hiding theorem\<close>
theorem weak_hiding: 
  assumes lossless_\<A>1: "\<And>PK . lossless_spmf (\<A>1 PK)"
  and lossless_\<A>2: "\<And>PK \<sigma> C I W . lossless_spmf (\<A>2 PK \<sigma> C I W)"
  shows "weak_eval_hiding_advantage \<A>1 \<A>2  
  \<le> DL_G\<^sub>p.advantage (reduction \<A>1 \<A>2) + t_DL_G\<^sub>p.advantage (reduction_tDL \<A>1)"
proof -
  have "weak_eval_hiding_advantage \<A>1 \<A>2 = spmf (game1 \<A>1 \<A>2) True"
    using hiding_game_to_game1
    unfolding weak_eval_hiding_advantage_def eval_hiding_advantage_def 
      weak_eval_hiding_adversary1_def weak_eval_hiding_game_def .
  also have "\<dots> \<le> spmf (game2 \<A>1 \<A>2) True + t_DL_G\<^sub>p.advantage (reduction_tDL \<A>1)"
    using assms fundamental_lemma_game1_game2 by blast
  also have "\<dots> \<le> DL_G\<^sub>p.advantage (reduction \<A>1 \<A>2) + t_DL_G\<^sub>p.advantage (reduction_tDL \<A>1)"
    by (simp add: game2_le_DL)
  finally show ?thesis .
qed

end

end
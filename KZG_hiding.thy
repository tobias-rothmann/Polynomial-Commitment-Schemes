theory KZG_hiding

imports KZG_correct DL_assumption tSDH_assumption Cyclic_Group_SPMF_ext Polynomial_Interpolation.Lagrange_Interpolation 
HOL.Finite_Set CryptHOL_ext
begin

hide_const order

locale hiding_game_def = KZG_correct
begin

section \<open>Definitions for the hiding game\<close>

text \<open>We define the hiding game, the reduction to the t-SDH assumption as well as any 
functions needed to construct them in this locale. This file contains another locale below which 
contains the proof.\<close>

text \<open>The hiding scheme functions.\<close>

text \<open>valid_msg ensures that the supplied witness w_i is a group element of Gp. 
Sadly cyclic groups are not constructed by type, which is why this check is necessary. 
A element of type 'a is not necessarily a group element of Gp.\<close>
definition valid_msg :: "'e eval_value \<Rightarrow> 'a eval_witness \<Rightarrow> bool" where 
  "valid_msg \<phi>_i w_i = (w_i \<in> carrier G\<^sub>p)"

subsection \<open>Game definition\<close>

type_synonym ('a', 'e')  adversary = 
  "'a' pk \<Rightarrow> 'a' commit \<Rightarrow> 'e' eval_position list \<Rightarrow> ('e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness) list \<Rightarrow> 
 'e' polynomial spmf"

text \<open>This is the formalized hiding game\<close>
definition hiding_game :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf"
  where "hiding_game I \<A> = TRY do {
  \<phi> \<leftarrow> sample_uniform_poly max_deg;
  PK \<leftarrow> KeyGen;
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. CreateWitness PK \<phi> i) I;
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"

text \<open>The advantage of the adversary over the hiding game is the probabillity that it 
wins.\<close>
definition hiding_advantage :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> real"
  where "hiding_advantage I \<A> \<equiv> spmf (hiding_game I \<A>) True"
subsection \<open>DL game\<close>

text \<open>We instantiate the DL game for the group Gp\<close>
sublocale DL_G\<^sub>p: DL G\<^sub>p "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding DL_def 
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
fun filter_distinct :: "'e mod_ring list \<Rightarrow> 'e eval_position list \<Rightarrow> 'e eval_position list"
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
fun PickDistinct :: "'e eval_position list \<Rightarrow> 'e eval_position"
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
    unfolding card_map_card 
    using assms
    by (simp add: distinct_card) 
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
hiding adversary to return the plian polynomial, which contains the solution to the DL-instance.\<close>
fun reduction
  :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> ('a,'e) DL.adversary"                     
where
  "reduction I \<A> g_pow_a = do {
  let i = PickDistinct I;
  plain_evals \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let evals = g_pow_a # map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) plain_evals ;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) evals) \<alpha>;
  let wtn_ts = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I plain_evals);
  \<phi>' \<leftarrow> \<A> PK C I wtn_ts;
  return_spmf (poly \<phi>' i)
  }"

end 


section \<open>Hiding proof\<close>

text \<open>This locale captures the proof for the definitions provided earlier\<close>
locale hiding_game_proof = hiding_game_def 
begin

subsubsection \<open>helping lemmas\<close>

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

text \<open>Finnaly, conclude the statement that interpolate_on is equivalent to computing Commit.
This is what the prior 3 lemmas where building up to.\<close>
lemma interpolate_on_is_Commit:
  assumes dist: "distinct (map fst xs_ys)"
  and length_xs_ys: "length xs_ys \<le> max_deg+1"
shows "interpolate_on (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha> = Commit 
    (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys)"
proof -
  have "interpolate_on (map (\<lambda>(x,y).(x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) xs_ys) \<alpha>  
  =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)"
    by(rule interpolate_on_\<alpha>_is_\<phi>_of_\<alpha>[OF assms])
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
  shows "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (y/x) = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/x)"
  by (metis mod_ring_pow_pow_G\<^sub>p mult_cancel_left2 times_divide_eq_right)

text \<open>Show that the witness emulation from the reduction adversary, is equivelnt to computing 
CreateWitness if \<alpha> \<notin> I.\<close>
lemma witness_calc_correct: 
  assumes dist: "distinct (map fst xs_ys)"
  and length_xs_ys: "length xs_ys \<le> max_deg + 1"
  and \<alpha>_nin_xs: "\<alpha> \<notin> set (map fst (tl xs_ys))"
  shows "map (\<lambda>i. (i, poly (lagrange_interpolation_poly xs_ys) i, createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) i)) (map fst (tl xs_ys))
    =  map (\<lambda>(x,y). (x,y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (tl xs_ys)"
proof -
  have "?thesis = (map (\<lambda>i. (fst i, poly (lagrange_interpolation_poly xs_ys) (fst i), createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) (fst i))) (tl xs_ys)
  =  map (\<lambda>(x,y). (x,y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (tl xs_ys))"
    by simp
  also have "\<dots>"
  proof(rule map_ext)
    fix x
    show "x \<in> set (tl xs_ys) \<longrightarrow>
         (fst x, poly (lagrange_interpolation_poly xs_ys) (fst x),
          createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) (fst x)) =
         (\<lambda>(x, y). (x, y, (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>) \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - x)))) x"
    proof 
      assume asm: "x \<in> set (tl xs_ys)"
      then obtain xj yj where xj_yj: "(xj,yj) = x"
        using prod.collapse by blast
      moreover have "(xj, poly (lagrange_interpolation_poly xs_ys) xj, createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) xj) 
                   = (xj, yj, (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>) \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> yj) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - xj)))"
      proof -
        have \<alpha>_neg_xj: "\<alpha> \<noteq> xj"
          by (metis asm assms(3) calculation image_eqI list.set_map prod.sel(1))
        have yj: "poly (lagrange_interpolation_poly xs_ys) xj = yj"
          by (rule lagrange_interpolation_poly[OF assms(1)])(simp add: asm calculation in_set_tlD)+
        have "createWitness (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly xs_ys) xj 
            = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha>) \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> yj) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - xj))"
          (is "?lhs = ?rhs")
        proof -
          have "?lhs = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (\<psi>_of (lagrange_interpolation_poly xs_ys) xj) \<alpha>)"
            unfolding createWitness.simps Let_def 
            using g_pow_PK_Prod_correct
            by (meson assms(2) degree_lagrange_interpolation_poly degree_q_le_\<phi> le_diff_conv le_trans)
          also have "\<dots> = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> ((poly (lagrange_interpolation_poly xs_ys) \<alpha> - poly (lagrange_interpolation_poly xs_ys) xj)/(\<alpha>-xj))"
              using \<alpha>_neg_xj \<phi>x_m_\<phi>u_eq_xmu_\<psi>x by simp
            also have "\<dots> =  \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> ((poly (lagrange_interpolation_poly xs_ys) \<alpha> - yj)/(\<alpha>-xj))"
            proof -
              show ?thesis using yj by blast
            qed
          also have "\<dots> =  (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly xs_ys) \<alpha> - yj)) ^\<^bsub>G\<^sub>p\<^esub> (1 / (\<alpha> - xj))"
            using \<alpha>_neg_xj split_pow_div_G\<^sub>p by force
          also have "\<dots> = ?rhs"
            using mod_ring_pow_mult_inv_G\<^sub>p by presburger
          finally show ?thesis .
        qed
        then show ?thesis
          using yj by blast
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

subsection \<open>reduction proof\<close>


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
only game hops based on bridging steps in this step (see game-based proofs in the thesis paper for 
details on game-hops).
  
2. We use a game-hop based on a failure event to transform game1 into game2. We extract the 
negligible probabillity that \<alpha> is contained in I, as in that case, CreateWitness is not the same as 
the emulation in the reduction adversary. 

3. We use game-hops based on bridging steps to explicitly restate game2 as game2_w_assert. 
We extract the assert that the adversary guessed polynomial \<phi>' equals \<phi>, which is part of the hiding 
game but not of the DL reduction.

4. We use over-estimation to drop the \<phi>'= \<phi>-assert. We obtain game2_wo_assert from game2_w_assert.

5. We transform game2_wo_assert into the DL game using game hops based on bridging steps.
\<close>

text \<open>The hiding game with interpolate_on instead of Commit and the random sampling of \<phi> split up 
into sampling random points for interpolate_on.\<close>
definition game1 :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf" where 
  "game1 I \<A> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>j. (j, poly \<phi> j, createWitness PK \<phi> j)) I;
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"

text \<open>game1 with the reduction adversaries emulation instead of CreateWitness\<close>
definition game2 :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf" where 
  "game2 I \<A> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"

text \<open>game 2 with extracted \<phi> = \<phi>'-assert \<close>
definition game2_w_assert :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf" where 
  "game2_w_assert I \<A> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf (hd evals = poly \<phi>' i)} ELSE return_spmf False"

text \<open>game2_w_asssert without the assert.\<close>
definition game2_wo_assert :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf" where 
  "game2_wo_assert I \<A> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (hd evals = poly \<phi>' i)} ELSE return_spmf False"

lemma literal_exchange_lemma: 
  assumes "\<And>x y. x \<in> set_spmf X \<Longrightarrow> U x y = V x y"
  shows"TRY do {x \<leftarrow> X::'x spmf;
           y \<leftarrow> Y :: 'y spmf;
           let q = (Q::'y \<Rightarrow> 'q) y;
           let r = (U::'x \<Rightarrow> 'y \<Rightarrow> 'r) x y;
           let s = (S::'x \<Rightarrow> 'y \<Rightarrow> 'r \<Rightarrow> 's) x y r;
           w \<leftarrow> (W::'q \<Rightarrow> 'r \<Rightarrow>'s \<Rightarrow> 'w spmf) q r s;
           return_spmf ((Z::'x \<Rightarrow> 'y \<Rightarrow> 'w \<Rightarrow> 'z) x y w)} ELSE return_spmf (Z'::'z) = 
        TRY do {x \<leftarrow> X::'x spmf;
           y \<leftarrow> Y :: 'y spmf;
           let q = (Q::'y \<Rightarrow> 'q) y;
           let r = (V::'x \<Rightarrow> 'y \<Rightarrow> 'r) x y;
           let s = (S::'x \<Rightarrow> 'y \<Rightarrow> 'r \<Rightarrow> 's) x y r;
           w \<leftarrow> (W::'q \<Rightarrow> 'r \<Rightarrow>'s \<Rightarrow> 'w spmf) q r s;
           return_spmf ((Z::'x \<Rightarrow> 'y \<Rightarrow> 'w \<Rightarrow> 'z) x y w)} ELSE return_spmf (Z'::'z)"
  using assms
  by (metis (mono_tags, lifting) bind_spmf_cong)

text \<open>Step 1 of the proof.\<close>
lemma hiding_game_to_game1:
  assumes "distinct I"
  and "length I = max_deg"
  and "length I < CARD('e)"
shows "hiding_game I \<A> = game1 I \<A>"
  (is "?lhs = ?rhs")
proof -
  text \<open>sample phi uniform random is sampling evaluation points for some I uniform random\<close>
  have "?lhs = TRY do {
  let i = PickDistinct I;
  \<phi> \<leftarrow> do {
      evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (max_deg+1) (CARD ('e)));
      return_spmf (lagrange_interpolation_poly (zip (i#I) evals))};
  PK \<leftarrow> KeyGen;
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. CreateWitness PK \<phi> i) I;
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
  proof -
    have distnct: "distinct (PickDistinct I# I)"
      using assms(1) assms(3) PickDistinct by presburger
    have lengt: "length (PickDistinct I# I) = max_deg +1"
      using assms(2) by fastforce
    show ?thesis
      unfolding hiding_game_def
      unfolding sample_uniform_evals_is_sample_poly[OF distnct lengt]
      unfolding Let_def ..
  qed
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  PK \<leftarrow> KeyGen;
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. CreateWitness PK \<phi> i) I;
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
  proof -
    have exchange: "CARD ('e) = order G\<^sub>p"
      using CARD_G\<^sub>p CARD_q by fastforce
    show ?thesis 
      unfolding Let_def exchange
      by simp
  qed
  text \<open>We make the secret key \<alpha> accessible in the reduction by unwrapping KeyGen to Setup.\<close>
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals::'e mod_ring list \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) I;
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;                             
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
  text \<open>We unwrap Steup further to get access to the computation of PK i.e. that PK is computed correctly.\<close>
    unfolding KeyGen_def split_def CreateWitness_def Let_def by fastforce
  also have "\<dots> = TRY do {
  evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  \<alpha>::'e mod_ring \<leftarrow>  map_spmf (\<lambda>x. of_int_mod_ring (int x)) (sample_uniform (order G\<^sub>p));
  let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  let C = Commit (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (lagrange_interpolation_poly (zip (PickDistinct I#I) evals));
  let witn_tupel = map (\<lambda>j. (j, poly (lagrange_interpolation_poly (zip (PickDistinct I#I) evals)) j, createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (lagrange_interpolation_poly (zip (PickDistinct I#I) evals)) j)) I;
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;                     
  return_spmf (lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>')} ELSE return_spmf False"
    unfolding Setup_def split_def Let_def 
    by (simp add: bind_map_spmf o_def del: createWitness.simps PickDistinct.simps)
  text \<open>Now we replace the Commit computed with a valid public key PK by interpolate_on\<close>
  also have "\<dots> = TRY do {
  evals:: 'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  \<alpha>::'e mod_ring \<leftarrow>  map_spmf (\<lambda>x. of_int_mod_ring (int x)) (sample_uniform (order G\<^sub>p));
  let PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  let C = interpolate_on (zip (PickDistinct I#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>j. (j, poly (lagrange_interpolation_poly (zip (PickDistinct I#I) evals)) j, createWitness (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) (lagrange_interpolation_poly (zip (PickDistinct I#I) evals)) j)) I;
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;                             
  return_spmf (lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>')} ELSE return_spmf False"
   proof(rule literal_exchange_lemma)
     fix evals :: "'e mod_ring list"
     fix \<alpha>
     have 1: "distinct (map fst ((zip (PickDistinct I#I) evals)))"
       by (metis assms(1) assms(3) distinct_take map_fst_zip_take PickDistinct)
     have [symmetric]: "evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p))) 
      \<Longrightarrow> interpolate_on (map2 (\<lambda>x y. (x, \<^bold>g ^ y)) (PickDistinct I#I) evals) \<alpha> = Commit (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly (zip (PickDistinct I#I) evals))"
       using interpolate_on_is_Commit[OF 1] by auto
     then show "evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p))) 
      \<Longrightarrow> Commit (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly (zip (PickDistinct I#I) evals)) = interpolate_on (zip (PickDistinct I#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>"
      by (simp add: zip_map2)
  qed
  also have "\<dots> = ?rhs"
    unfolding game1_def Setup_def Let_def split_def 
    by (simp add: bind_map_spmf o_def del: createWitness.simps PickDistinct.simps)
  finally show ?thesis .
qed

subsubsection \<open>literal helping lemma for step 2:\<close>

lemma literal_swap_lemma: 
  "TRY do {x \<leftarrow> X::'x spmf;
           y \<leftarrow> Y :: 'y spmf;
           w \<leftarrow> (W::'x \<Rightarrow> 'y\<Rightarrow> 'w spmf) x y ;
           return_spmf ((Z::'x \<Rightarrow> 'y \<Rightarrow> 'w \<Rightarrow> 'z) x y w)} ELSE return_spmf (Z'::'z) = 
   TRY do {y \<leftarrow> Y :: 'y spmf;
           x \<leftarrow> X::'x spmf;
           w \<leftarrow> (W::'x \<Rightarrow> 'y\<Rightarrow> 'w spmf) x y ;
           return_spmf ((Z::'x \<Rightarrow> 'y \<Rightarrow> 'w \<Rightarrow> 'z) x y w)} ELSE return_spmf (Z'::'z)"
proof -
  have "\<forall>X Y Z. ((X::'x spmf) \<bind> (\<lambda>x. (Y::'y spmf) \<bind> Z (x::'x)::'z spmf)::'z spmf) = Y \<bind> (\<lambda>y. X \<bind> (\<lambda>x. Z x (y::'y)::'z spmf)::'z spmf)"
    using bind_commute_spmf by blast
  then show ?thesis
    by presburger
qed


text \<open>Step 2 of the proof:\<close>
lemma fundamental_lemma_game1_game2: 
  assumes lossless_\<A>: "\<And>Q C W . lossless_spmf (\<A> Q C I W)"
  and dist_I: "distinct I"
  and len_I: "length I = max_deg"
  shows "spmf (game2 I \<A>) True + (max_deg+1)/p \<ge> spmf (game1 I \<A>) True"
proof -
  note [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD map_spmf_bind_spmf bind_spmf_const Let_def o_def
  note %invisible [cong del] = if_weak_cong 
   and [split del] = if_split
   and [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD map_spmf_bind_spmf bind_spmf_const
   and [if_distribs] = if_distrib[where f="\<lambda>x. try_spmf x _"] if_distrib[where f="weight_spmf"] if_distrib[where f="\<lambda>r. scale_spmf r _"]

  text \<open>We split of the random sampling of \<alpha> to externalize reasoning about the case that \<alpha> 
  is in I. This is essential for the fundamental lemma used later on.\<close>

  text \<open>this is sampling \<alpha> as a uniform random finite field element\<close>
  let ?sample = "\<lambda>f :: 'e mod_ring  \<Rightarrow> _ spmf. do {
   x::'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
   f x }"

  text \<open>game1b is game1 with \<alpha> as parameter, that additionally returns whether the failure event 
  happend i.e. \<alpha> \<in> I\<close>
  define game1b :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> 'e mod_ring \<Rightarrow> (bool\<times>bool) spmf"
    where "game1b I \<A> \<alpha> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>j. (j, poly \<phi> j, createWitness PK \<phi> j)) I;
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;                             
  return_spmf (\<phi> = \<phi>', \<alpha> \<in> set (PickDistinct I#I))} ELSE return_spmf (False, \<alpha> \<in> set (PickDistinct I#I))" for I \<A> \<alpha>

  text \<open>show game1 is game1b with random sampling, filtered for the first result i.e. neglecting 
  whether the failure event occured\<close>
  have game1b: "game1 I \<A> = map_spmf fst (?sample (game1b I \<A>))"
  proof -
    have "game1 I \<A> = TRY do {
      let i = PickDistinct I;
      evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
      let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
      let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
      \<alpha> :: 'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
      let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>j. (j, poly \<phi> j, createWitness PK \<phi> j)) I;
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
    return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
      unfolding game1_def Setup_alt_def Let_def  by auto
    also have "\<dots> = TRY do {
      \<alpha> :: 'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
      let i = PickDistinct I;
      evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
      let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
      let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
      let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>j. (j, poly \<phi> j, createWitness PK \<phi> j)) I;
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
    return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
      unfolding Let_def split_def 
      by (rule literal_swap_lemma)
    also have "\<dots> = do {
      \<alpha> :: 'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
      TRY do {
      let i = PickDistinct I;
      evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
      let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
      let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
      let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>j. (j, poly \<phi> j, createWitness PK \<phi> j)) I;
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
    return_spmf (\<phi> = \<phi>')} ELSE return_spmf False}"
      unfolding game1b_def 
      by (rule try_spmf_bind_spmf_lossless)(simp add: local.G\<^sub>p.order_gt_0)
    also have "\<dots> = map_spmf fst (?sample (game1b I \<A>))"
      unfolding game1b_def
      by (simp add: map_try_spmf del: PickDistinct.simps createWitness.simps)
    finally show ?thesis .
  qed

  text \<open>simiarly to game1b, game2b is game2 with \<alpha> as a parameter, that additionally returns 
  whether the failure event happend i.e. \<alpha> \<in> I\<close>
  define game2b :: "'e eval_position list \<Rightarrow> ('a, 'e) adversary \<Rightarrow> 'e mod_ring \<Rightarrow> (bool\<times>bool) spmf"
    where "game2b I \<A> \<alpha> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
  let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (\<phi> = \<phi>', \<alpha> \<in> set (PickDistinct I#I))} ELSE return_spmf (False, \<alpha> \<in> set (PickDistinct I#I))" for I \<A> \<alpha>

  text \<open>accordingly we show game2 is game2b with random sampling, filtered for the first result 
  i.e. neglecting whether the failure event occured\<close>
  have game2b: "game2 I \<A> = map_spmf fst (?sample (game2b I \<A>))"
  proof -
    have "game2 I \<A> = TRY do {
      let i = PickDistinct I;
      evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
      let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
      let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
      \<alpha> :: 'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
      let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
    return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
      unfolding game2_def Setup_alt_def Let_def by auto
    also have "\<dots> = TRY do {
      \<alpha> :: 'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
      let i = PickDistinct I;
      evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
      let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
      let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
      let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
    return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"
      unfolding Let_def split_def 
      by (rule literal_swap_lemma)
    also have "\<dots> = do {
      \<alpha> :: 'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
      TRY do {
      let i = PickDistinct I;
      evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
      let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
      let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
      let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
    return_spmf (\<phi> = \<phi>')} ELSE return_spmf False}"
      unfolding game1b_def 
      by (rule try_spmf_bind_spmf_lossless)(simp add: local.G\<^sub>p.order_gt_0)
    also have "\<dots> = map_spmf fst (?sample (game2b I \<A>))"
      unfolding game2b_def
      by (simp add: map_try_spmf del: PickDistinct.simps createWitness.simps)
    finally show ?thesis .
  qed

  text \<open>We capture the failure event (i.e. \<alpha> \<in> I) in the collision game.\<close>
  define collision_game :: "'e eval_position list \<Rightarrow> bool spmf" where 
  "collision_game l = do {
    \<alpha>::'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
    return_spmf (\<alpha> \<in> set l)}" for l

  text \<open>We show that the second result of game1b captures the failure evvent, i.e. is the collision 
  game.\<close>
  have map_snd_game1_is_collision_game: "map_spmf snd (?sample (game1b I \<A>)) = collision_game (PickDistinct I#I)"
  proof - 
    define collision_game_for :: "'e eval_position list \<Rightarrow> 'e mod_ring \<Rightarrow> bool spmf" where 
    "collision_game_for l \<alpha> = TRY do {
      return_spmf (\<alpha> \<in> set l)} 
      ELSE return_spmf (\<alpha> \<in> set l)" for l \<alpha>

    have "\<And>I. collision_game I = ?sample (collision_game_for I)"
      unfolding collision_game_def collision_game_for_def by simp
    moreover have "map_spmf snd (?sample (game1b I \<A>)) = ?sample (collision_game_for (PickDistinct I#I))"
      by (simp add: map_try_spmf game1b_def collision_game_for_def lossless_\<A> del: PickDistinct.simps createWitness.simps)
    ultimately show ?thesis by presburger
  qed

  text \<open>Before we start performing the game-hop with the fundamental lemma, we state the 
  probabillity of the failure event. Note, that this probability is negligible.\<close>
  have spmf_collision_game: "spmf (collision_game (PickDistinct I#I)) True = (max_deg+1) / p"
  proof -
    obtain A where A: "A = set (PickDistinct I#I)" by blast
    then have "spmf (collision_game (PickDistinct I#I)) True = spmf (do {
    \<alpha>::'e mod_ring \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
    return_spmf (\<alpha> \<in> A)}) True"
      unfolding collision_game_def by blast
    also have "\<dots> = spmf (
     map_spmf (\<lambda>x. x \<in> A) (map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p)))) True"
      by (simp add: map_spmf_conv_bind_spmf)
    also have "\<dots> = spmf (map_spmf (\<lambda>x. x \<in> A) (map_spmf (of_int_mod_ring \<circ> int) (spmf_of_set ({..<CARD('e)})))) True"
      unfolding sample_uniform_def
      using CARD_G\<^sub>p CARD_q by fastforce
    also have "\<dots> = spmf (map_spmf (\<lambda>x. x \<in> A) (spmf_of_set (UNIV::'e mod_ring set))) True"
    proof -
      have inj_on_UNIV: "inj_on (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) {..<CARD('e)}"
        using lessThan_atLeast0 of_int_mod_inj_on_ff by presburger
      moreover have "(of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) ` {..<CARD('e)} = (UNIV::'e mod_ring set)"
      proof
        show "(of_int_mod_ring \<circ> int) ` {..<CARD('e)} \<subseteq> UNIV"
          by blast
        show "UNIV \<subseteq> (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) ` {..<CARD('e)}" proof 
          fix x :: "'e mod_ring" 
          assume "x \<in> UNIV"
          obtain y where y: "y = (nat \<circ> to_int_mod_ring) x" by blast
          then have "nat y \<in> {..<CARD('e)}"
            using y range_to_int_mod_ring 
            by (metis Rep_mod_ring atLeastLessThan_iff comp_apply int_eq_iff lessThan_iff to_int_mod_ring.rep_eq zless_nat_eq_int_zless)
          moreover have "(of_int_mod_ring \<circ> int::nat \<Rightarrow> 'e mod_ring) y = x" 
            by (simp add: to_int_mod_ring_ge_0 y)
          ultimately show "x \<in> (of_int_mod_ring \<circ> int::nat \<Rightarrow> 'e mod_ring) ` {..<CARD('e)}"
            by fastforce
        qed
      qed 
      ultimately show ?thesis by fastforce
    qed
    also have "\<dots> = measure (measure_spmf (spmf_of_set (UNIV::'e mod_ring set))) A"
    proof -
      have  "(\<lambda>x::'e mod_ring. x \<in> (A::'e mod_ring set)) -` {True} = A"
      proof qed blast+
      then show ?thesis
        unfolding spmf_map by presburger
    qed
    also have "\<dots> = card A / card (UNIV::'e mod_ring set)"
      unfolding measure_spmf_of_set by auto
    also have "\<dots> = (max_deg+1)/p"
    proof - 
      have "card A = max_deg +1"
        unfolding A
        by (metis CARD_q Suc_eq_plus1 add_0_left assms(2) assms(3) d_l_p distinct_card list.size(4) of_nat_less_imp_less PickDistinct)
      moreover have "card (UNIV::'e mod_ring set) = p"
        by (simp add: CARD_q)
      ultimately show ?thesis by force
    qed
   finally show ?thesis .
  qed

  text \<open>We now use relation reasoning to state that game1 and game2 are equal except for the 
  failure event. Specifically, we show this for game1b and game2b, which externalize the failure 
  event and thus allow us to reason about the failure event.\<close>
  have "rel_spmf (\<lambda>(win, bad) (win', bad'). bad = bad' \<and> (\<not> bad' \<longrightarrow> win = win')) (game1b I \<A> \<alpha>) (game2b I \<A> \<alpha>)" for \<alpha>
    unfolding game1b_def game2b_def Let_def
    apply (rule rel_spmf_try_spmf)
    subgoal TRY
      apply (rule rel_spmf_bind_reflI)
      apply (cases "\<alpha> \<in> set (PickDistinct I #I)")
      subgoal True for evals
        by (auto intro!: rel_spmf_bindI1 rel_spmf_bindI2 lossless_\<A>)
      subgoal False for evals
      proof -
        assume asm1: "\<alpha> \<notin> set (PickDistinct I # I)"
        assume asm2: "evals \<in> set_spmf (map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg + 1) (Coset.order G\<^sub>p)))"
        then have evals_length: "length evals = max_deg + 1" by auto

        have witness_equal:"(map (\<lambda>j. (j, poly (lagrange_interpolation_poly (zip (PickDistinct I # I) evals)) j,
                   createWitness (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) (lagrange_interpolation_poly (zip (PickDistinct I # I) evals)) j))
         I) = map (\<lambda>(x,y). (x,y,(interpolate_on (zip (PickDistinct I#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals))"
        proof -
           have dist_pick_I_I: "distinct (map fst (zip (PickDistinct I # I) evals))"
          proof -
            have "map fst (zip (PickDistinct I # I) evals) = PickDistinct I#I"
              by (simp add: assms(3) evals_length)
            also have "distinct \<dots>"
              using CARD_q d_l_p dist_I len_I of_nat_less_imp_less PickDistinct by blast
            finally show ?thesis by blast
          qed
          have len_zip: "length (zip (PickDistinct I # I) evals) \<le> max_deg + 1"
            by (simp add: evals_length)
          have tl_zip_switch:"tl (zip (PickDistinct I # I) evals) = zip I (tl evals)"
            by (metis list.exhaust_sel list.sel(2) list.sel(3) zip.simps(1) zip_Cons_Cons)
          have map_fst_zip_is_I: "map fst (zip I (tl evals)) = I"
            by (simp add: assms(3) evals_length)
          have \<alpha>_not_in_I: "\<alpha> \<notin> set I"
            using asm1 by force
          have compute_pow_is_g_pow_\<alpha>: 
           "interpolate_on (zip (PickDistinct I # I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>  
          = \<^bold>g ^ poly (lagrange_interpolation_poly (zip (PickDistinct I # I) evals)) \<alpha>"
            using interpolate_on_\<alpha>_is_\<phi>_of_\<alpha>[OF dist_pick_I_I len_zip]
            by (simp add: zip_map2)
          show ?thesis 
            using witness_calc_correct[of "zip (PickDistinct I # I) evals" \<alpha>]
            unfolding tl_zip_switch compute_pow_is_g_pow_\<alpha> map_fst_zip_is_I
            using dist_pick_I_I len_zip \<alpha>_not_in_I by blast
        qed
        show ?thesis
          unfolding witness_equal 
          by (rule rel_spmf_bind_reflI)simp
      qed 
    done
    subgoal ELSE 
      apply force
      done
    done
  text \<open>We extend this result to the sampling \<alpha> uniform random with ?sample\<close>
  hence "rel_spmf (\<lambda>(win, bad) (win', bad'). (bad \<longleftrightarrow> bad') \<and> (\<not> bad' \<longrightarrow> win \<longleftrightarrow> win')) (?sample (game1b I \<A>)) (?sample (game2b  I \<A>))"
    by(intro rel_spmf_bind_reflI)
  text \<open>We use the fundamental lemma to conclude that the difference in winnig one or the other game 
  differs at most in the probability of the failure event.\<close>
  hence "\<bar>measure (measure_spmf (?sample (game1b I \<A>))) {(win, _). win} - measure (measure_spmf (?sample (game2b I \<A>))) {(win, _). win}\<bar>
      \<le> measure (measure_spmf (?sample (game1b I \<A>))) {(_, bad). bad}"
  unfolding split_def by(rule fundamental_lemma)
  moreover have "measure (measure_spmf (?sample (game1b I \<A>))) {(win, _). win} = spmf (map_spmf fst (?sample (game1b I \<A>))) True"
    and "measure (measure_spmf (?sample (game2b I \<A>))) {(win, _). win} = spmf (map_spmf fst (?sample (game2b I \<A>))) True"
    and "measure (measure_spmf (?sample (game1b I \<A>))) {(_, bad). bad} = spmf (map_spmf snd (?sample (game1b I \<A>))) True"
      unfolding spmf_conv_measure_spmf measure_map_spmf by(auto simp add: vimage_def split_def)
 text \<open>We use this to overestimate the probabillity of game1 by the probabilliuyt fo winning game2 
 plus the probabillity of the failure event happening\<close>
 ultimately have
    "\<bar>spmf (map_spmf fst (?sample (game1b I \<A>))) True - spmf (map_spmf fst (?sample (game2b I \<A>))) True\<bar>
    \<le> spmf (map_spmf snd (?sample (game1b I \<A>))) True"
    by simp
  then have "spmf (map_spmf fst (?sample (game1b I \<A>))) True \<le> spmf (map_spmf fst (?sample (game2b I \<A>))) True + spmf (map_spmf snd (?sample (game1b I \<A>))) True"
    by linarith
  then show ?thesis
    unfolding game1b game2b map_snd_game1_is_collision_game spmf_collision_game .
qed


text \<open>Step 3 of the proof:\<close>
lemma game2_to_game2_assert: 
  assumes "distinct I"
  and "length I = max_deg"
  and "length I < CARD('e)"
  shows 
"game2 I \<A> = game2_w_assert I \<A>"
  (is "?lhs = ?rhs")
proof -
  text \<open>We start the proof by extracting the return value, which is a bool, into an assert.\<close>
  have "?lhs =  TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
      TRY do {
        return_spmf (\<phi> = \<phi>')
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False"
  unfolding game2_def split_def Let_def
  by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
      TRY do {
        _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False"
    unfolding Let_def
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
    let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
    \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
    _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
    return_spmf True
  } ELSE return_spmf False"
   unfolding split_def Let_def
   by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
 text \<open>next we show that the assert \<phi> = \<phi>' implies `hd evals = poly \<phi>' (PickDistinct I)`, which is 
 asserted by the Dl reduction game. Hence we add `hd evals = poly \<phi>' (PickDistinct I)` to the 
 assert without changing the game.\<close>
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
    let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
    \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>' \<and> hd evals = poly \<phi>' (PickDistinct I));
  return_spmf True}
  ELSE return_spmf False"
  proof -
    have "\<And>evals \<phi>'. evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p)))  
      \<Longrightarrow> ((lagrange_interpolation_poly (zip (PickDistinct I#I) evals) = \<phi>' 
      \<longleftrightarrow> (lagrange_interpolation_poly (zip (PickDistinct I#I) evals)) = \<phi>' \<and> hd evals = poly \<phi>' (PickDistinct I)))"
    proof -
      fix evals :: "'e mod_ring list"
      fix \<phi>'
      assume "evals \<in> set_spmf (map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p)))"
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
              by (metis assms distinct_take map_fst_zip_take PickDistinct)
            show "\<phi>' = lagrange_interpolation_poly (zip (PickDistinct I#I) evals)"
              using asm[symmetric] .
            show "(PickDistinct I, hd evals) \<in> set (zip (PickDistinct I#I) evals)" 
              using assms(2) evals_length
              by (metis Nil_eq_zip_iff add_is_0 hd_in_set hd_zip length_0_conv list.discI list.sel(1) rel_simps(92))
          qed
        qed 
      qed simp
    qed
    then show ?thesis 
      unfolding split_def 
      using bind_spmf_cong
      by (smt (verit))
  qed
  text \<open>In the next part we split the conjuncture `\<phi> = \<phi>' \<and> hd evals = poly \<phi>' (PickDistinct I)` 
  into two separate assert statements, so we can use overestimation at a later step to get closer 
  to the DL game.\<close>
 also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
      TRY do {
        _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>' \<and> hd evals = poly \<phi>' (PickDistinct I));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False"
  unfolding split_def Let_def
  by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
 also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^ i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
      TRY do {
        _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>'); 
        _::unit \<leftarrow> assert_spmf (hd evals = poly \<phi>' (PickDistinct I));
        return_spmf True
      } ELSE return_spmf False
    } ELSE return_spmf False
  } ELSE return_spmf False
  } ELSE return_spmf False"
   by (simp add: assert_collapse)
 text \<open>Lastly we convert the later assert statement `hd evals = poly \<phi>' (PickDistinct I)` into a 
 return statement to mirror the DL game.\<close>
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
      TRY do {
      _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
        TRY do {
        _::unit \<leftarrow> assert_spmf (hd evals = poly \<phi>' i);
        return_spmf True}
        ELSE return_spmf False}
      ELSE return_spmf False}
    ELSE return_spmf False}
  ELSE return_spmf False}
  ELSE return_spmf False"
    unfolding split_def Let_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  TRY do {
    let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
    let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    TRY do {
      let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
      let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
      \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
      TRY do {
      _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
        TRY do {
        return_spmf (hd evals = poly \<phi>' i)}
        ELSE return_spmf False}
      ELSE return_spmf False}
    ELSE return_spmf False}
  ELSE return_spmf False}
  ELSE return_spmf False"
    unfolding Let_def split_def
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  evals \<leftarrow> map_spmf (map  (of_int_mod_ring \<circ> int)) (sample_uniform_list (max_deg+1) (order G\<^sub>p));
  let \<phi> = lagrange_interpolation_poly (zip (i#I) evals);
  let exp_evals = map (\<lambda>i. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> i) evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) exp_evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  _::unit \<leftarrow> assert_spmf (\<phi> = \<phi>');
  return_spmf (hd evals = poly \<phi>' i)}
  ELSE return_spmf False"
    unfolding split_def Let_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = ?rhs"
    unfolding game2_w_assert_def Let_def ..
  finally show ?thesis .
qed

text \<open>Step 4 of the proof.
We use overestiation to show that the probabillity that the adversary wins game_2_w_assert is
less than or equal to winning game2_wo_assert. We drop the assert statement that we extracted in 
the prior step.\<close>
lemma del_assert_game2: "spmf (game2_w_assert I \<A>) True \<le> spmf (game2_wo_assert I \<A>) True"
  unfolding game2_w_assert_def game2_wo_assert_def Let_def split_def
  apply (rule try_spmf_le)
  apply (rule bind_spmf_le)+
  apply (rule del_assert)
  done

text \<open>Step 5 of the proof\<close>
lemma game2_wo_assert_to_DL_reduction_game:"game2_wo_assert I \<A> =  DL_G\<^sub>p.game (reduction I \<A>)"
  (is "?lhs = ?rhs")
proof -
  text \<open>Firstly we erase \<phi> from game2_wo_assert, as \<phi> was only needed for game2_w_assert.\<close>
  have "?lhs = TRY do {
  let i = PickDistinct I;
  nat_evals \<leftarrow> sample_uniform_list (max_deg+1) (order G\<^sub>p);
  let evals = map (of_int_mod_ring \<circ> int) nat_evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (hd evals = poly \<phi>' i)} ELSE return_spmf False"
    unfolding game2_wo_assert_def Let_def by(simp add: bind_map_spmf o_def)
  text \<open>Next, we split the random sampled list up into a random point concatenated with a 
  one element shorter random list. The random point represents the DL value which creates later 
  the DL instance.\<close>
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  nat_evals \<leftarrow> do {x \<leftarrow> sample_uniform (order G\<^sub>p);
                   xs \<leftarrow> (sample_uniform_list max_deg (order G\<^sub>p));
                   return_spmf (x#xs)};
  let evals = map (of_int_mod_ring \<circ> int) nat_evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (hd evals = poly \<phi>' i)} ELSE return_spmf False" 
    using pretty_Cons_random_list_split p_gr_two CARD_G\<^sub>p by force
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  x \<leftarrow> sample_uniform (order G\<^sub>p);
  xs \<leftarrow> (sample_uniform_list max_deg (order G\<^sub>p));
  let nat_evals = (x#xs);
  let evals = map (of_int_mod_ring \<circ> int) nat_evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (hd evals = poly \<phi>' i)} ELSE return_spmf False"
    by force
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  a \<leftarrow> sample_uniform (order G\<^sub>p);
  nat_evals \<leftarrow> sample_uniform_list max_deg (order G\<^sub>p);
  let evals = map (of_int_mod_ring \<circ> int) (a#nat_evals);
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I (tl evals));
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (hd evals = poly \<phi>' i)} ELSE return_spmf False"
    unfolding Let_def ..
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  a \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  plain_evals \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let evals = a # plain_evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) (map (\<lambda>i. \<^bold>g ^ i) evals)) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I plain_evals);
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (a = poly \<phi>' i)} ELSE return_spmf False"
    by (force simp add: bind_map_spmf o_def)
  text \<open>Now we transform evals into a group value list. We concatenate the random value in a group
  (g^a, later the DL-instance) with the random list as group values\<close>
  also have "\<dots> = TRY do {
  let i = PickDistinct I;
  a \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  plain_evals \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let evals = \<^bold>g ^ a # map (\<lambda>i. \<^bold>g ^ i) plain_evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I plain_evals);
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (a = poly \<phi>' i)} ELSE return_spmf False"
    by auto
  text \<open>We rearrange the functions to mirror the DL game more closely.\<close>
  also have "\<dots> = TRY do {
  a \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  let i = PickDistinct I;
  plain_evals \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
  let evals = \<^bold>g ^ a # map (\<lambda>i. \<^bold>g ^ i) plain_evals;
  (\<alpha>, PK) \<leftarrow> Setup;
  let C = interpolate_on (zip (i#I) evals) \<alpha>;
  let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I plain_evals);
  \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
  return_spmf (a = poly \<phi>' i)} ELSE return_spmf False"
    by metis
  text \<open>Lastly, we extract the functions from the reduction adversary into an do-block to mirror 
  the DL game.\<close>
  also have "\<dots> = TRY do {
  a \<leftarrow> map_spmf (of_int_mod_ring \<circ> int) (sample_uniform (order G\<^sub>p));
  a' \<leftarrow> do {
    let i = PickDistinct I;
    plain_evals \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list max_deg (order G\<^sub>p));
    let evals = \<^bold>g ^ a # map (\<lambda>i. \<^bold>g ^ i) plain_evals;
    (\<alpha>, PK) \<leftarrow> Setup;
    let C = interpolate_on (zip (i#I) evals) \<alpha>;
    let witn_tupel = map (\<lambda>(x,y). (x,y,(C  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) (zip I plain_evals);
    \<phi>' \<leftarrow> \<A> PK C I witn_tupel;
    return_spmf (poly \<phi>' i)};
  return_spmf (a = a')} ELSE return_spmf False"
    by (simp add: Let_def split_def o_def del: PickDistinct.simps)
  also have "\<dots> = DL_G\<^sub>p.game (reduction I \<A>)"
    unfolding DL_G\<^sub>p.game_alt_def2 reduction.simps ..
  finally show ?thesis .
qed

text \<open>Finally we assemble all proof steps for the weak hiding theorem\<close>
theorem weak_hiding: 
  assumes lossless_\<A>: "\<And>Q C W . lossless_spmf (\<A> Q C I W)"
  and "distinct I"
  and "length I = max_deg"
  and "length I < CARD('e)"
shows "spmf (hiding_game I \<A>) True \<le> spmf (DL_G\<^sub>p.game (reduction I \<A>)) True + (max_deg+1)/p"
proof -
  have "spmf (hiding_game I \<A>) True = spmf (game1 I \<A>) True"
    using hiding_game_to_game1[OF assms(2,3,4)] by presburger
  also have "\<dots> \<le> spmf (game2 I \<A>) True + (max_deg+1)/p"
    using assms(1,2,3) fundamental_lemma_game1_game2 by blast
  also have "\<dots> = spmf (game2_w_assert I \<A>) True + (max_deg+1)/p"
    using game2_to_game2_assert[OF assms(2,3,4)] by presburger
  also have "\<dots> \<le> spmf (game2_wo_assert I \<A>) True + (max_deg+1)/p"
    using del_assert_game2 by auto
  also have "\<dots> = spmf (DL_G\<^sub>p.game (reduction I \<A>)) True + (max_deg+1)/p"
    using game2_wo_assert_to_DL_reduction_game by presburger
  finally show ?thesis .
qed

end











































locale KZG_PCS_weak_hiding = KZG_PCS_correct
begin

section \<open>Definitions for the weak hiding game\<close>

text \<open>The difference between the weak hiding game and the hiding game is that in the weak hiding 
game the polynomial is uniform random, not chosen by the adversary. Since arbitrary values can be 
modelled as uninitialized parameters in Isabelle, like the adversary in the hiding game, we can make
the arbitrary uninitialized adversary weaker by instantiating a part of it.\<close>

text \<open>The adversary chooses only the evaluation points, not the polynomial.\<close>
type_synonym ('r','vk', 'argument','state')  weak_eval_hiding_adversary1 = 
  "'vk' \<Rightarrow>  ('argument' list \<times> 'state') spmf"

text \<open>The polynomial is chosen uniform random. We also enforce two additional properties on the 
adversary outputs. With this construction we can use the predefined eval hiding game from 
Polynomial Commitment Scheme.\<close>
definition weak_eval_hiding_adversary1 :: "('e mod_ring,'a vk, 'e argument,'state) 
  weak_eval_hiding_adversary1 \<Rightarrow> ('e mod_ring,'a vk, 'e argument,'state) eval_hiding_adversary1"
  where 
  "weak_eval_hiding_adversary1 \<A> vk = do {
    (I,\<sigma>) \<leftarrow> \<A> vk;
    _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
    p::'e mod_ring poly \<leftarrow> sample_uniform_poly max_deg;
    return_spmf (p,I,\<sigma>)
    }"

text \<open>eval_hiding_game except the polynomial is chosen at uniform random and not by the adversary.\<close>
definition weak_eval_hiding_game ::  "('e mod_ring,'a vk, 'e argument, 'state) 
  weak_eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> bool spmf"
  where "weak_eval_hiding_game \<A>1 \<A>2 = eval_hiding_game (weak_eval_hiding_adversary1 \<A>1) \<A>2"

text \<open>The advantage of the adversary over the weak hiding game is the advantage of eval hiding with
the weak adversary.\<close>
definition weak_eval_hiding_advantage :: "('e mod_ring,'a vk, 'e argument, 'state) 
  weak_eval_hiding_adversary1 \<Rightarrow> 
  ('e mod_ring, 'a vk, 'a commit, 'e argument, 'e evaluation, 'a witness, 'state) 
  eval_hiding_adversary2 \<Rightarrow> real"
  where "weak_eval_hiding_advantage \<A>1 \<A>2 
    \<equiv> eval_hiding_advantage (weak_eval_hiding_adversary1 \<A>1) \<A>2"

subsection \<open>DL game\<close>

text \<open>We instantiate the DL game for the group Gp\<close>
sublocale DL_G\<^sub>p: DL G\<^sub>p "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding DL_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

text \<open>We instantiate the t-SDH game for the group Gp\<close>
sublocale t_SDH_G\<^sub>p: t_SDH G\<^sub>p max_deg "of_int_mod_ring \<circ> int" "pow_mod_ring G\<^sub>p"
  unfolding t_SDH_def 
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
  :: "('e mod_ring,'a vk, 'e argument, 'state) 
  weak_eval_hiding_adversary1 \<Rightarrow> 
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

fun reduction_tSDH :: "('e mod_ring,'a vk, 'e argument, 'state) weak_eval_hiding_adversary1 
\<Rightarrow> ('a,'e) t_SDH.adversary"
  where "reduction_tSDH \<A>1 PK = do {
  (I,\<sigma>) \<leftarrow> \<A>1 PK;
  let (\<alpha>'::'e mod_ring) = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = PK!1) (PickDistinct I #I)) of Some x => x | None => 1);
  return_spmf ((0::'e mod_ring), \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>((1::'e mod_ring)/\<alpha>'))
  }"

section \<open>Hiding proof\<close>

subsubsection \<open>helping lemmas\<close>

lemma PK1[simp]: "map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1 =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha>"
  by (metis (no_types) Suc_eq_plus1 add.commute d_pos diff_zero landau_product_preprocess(53) 
      less_Suc_eq_0_disj nth_map_upt power_one_right)

text \<open>The "find" in the tSDH reduction is successful.\<close>
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
   \<and> \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>(1/(case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1) (PickDistinct I#I)) of Some x => x | None => 1))"
proof 
  assume asm: " length I = max_deg \<and> distinct I \<and> \<alpha> \<in> set (PickDistinct I # I)"
  then have some: "Some \<alpha> =
    find (\<lambda>x. \<^bold>g ^ x = map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1] ! 1) (PickDistinct I # I)"
    apply (simp only: PK1)
    apply (rule in_set_impl_find)
    apply simp
    done
  show " length I = max_deg \<and>
    distinct I \<and>
    \<alpha> \<in> set (PickDistinct I # I) \<and>
    \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>(1/(case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]!1) (PickDistinct I#I)) of Some x => x | None => 1))"
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
  sorry

text \<open>Finnaly, conclude the statement that interpolate_on is equivalent to computing Commit.
This is what the prior 3 lemmas where building up to. TODO  rename Commit to g_pow_PK_Prod in lemma name\<close>
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
shows "map (\<lambda>i. (Eval (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (\<alpha> ^ t)) [0..<max_deg + 1]) () (lagrange_interpolation_poly  (zip (PickDistinct I # I) evals)) i)) I
    =  map2 (\<lambda>x y. (y,( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (lagrange_interpolation_poly  (zip (PickDistinct I # I) evals)) \<alpha>)  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/(\<alpha>-x)))) I (tl evals)"
 sorry
 

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
only game hops based on bridging steps in this step (see game-based proofs in the thesis paper for 
details on game-hops).
  
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
definition game1 :: "('e mod_ring,'a vk, 'e argument, 'state) weak_eval_hiding_adversary1 \<Rightarrow> 
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
definition game2 :: "('e mod_ring,'a vk, 'e argument, 'state) weak_eval_hiding_adversary1 \<Rightarrow> 
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

text \<open>game 2 with extracted \<phi> = \<phi>'-assert TODO this could be left out and we could just <= the 
previous to the next one\<close>
definition game2_w_assert :: "('e mod_ring,'a vk, 'e argument, 'state) weak_eval_hiding_adversary1 \<Rightarrow> 
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
definition game2_wo_assert :: "('e mod_ring,'a vk, 'e argument, 'state) weak_eval_hiding_adversary1 \<Rightarrow> 
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

lemma distinct_map_fst_zip: "distinct a \<Longrightarrow> distinct (map fst (zip a b))"
  by (simp add: map_fst_zip_take)

lemma card_eq_ord: "CARD('e) = order G\<^sub>p"
  using CARD_q CARD_G\<^sub>p by force

text \<open>Step 1 of the proof.\<close>
lemma hiding_game_to_game1:
shows "weak_eval_hiding_game \<A>1 \<A>2 = game1 \<A>1 \<A>2"
  (is "?lhs = ?rhs")
proof -
  text \<open>sample phi uniform random is sampling evaluation points for some I uniform random\<close>
  have "?lhs = TRY do {
  (ck, vk) \<leftarrow> key_gen;
  (p,I,\<sigma>) \<leftarrow> do {
    (I,\<sigma>) \<leftarrow> \<A>1 vk;
    p::'e mod_ring poly \<leftarrow> do {
    _ :: unit \<leftarrow> assert_spmf (length I = max_deg \<and> distinct I);
      evals::'e mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (max_deg+1) (CARD ('e)));
      let i = PickDistinct I;
      return_spmf (lagrange_interpolation_poly (zip (i#I) evals))};
    return_spmf (p,I,\<sigma>)
    };
  (c,d) \<leftarrow> commit ck p; 
  let W = map (\<lambda>i. Eval ck d p i) I; 
  p' \<leftarrow> \<A>2 vk \<sigma> c I W;
  return_spmf (p = p')} ELSE return_spmf False"
    unfolding weak_eval_hiding_game_def eval_hiding_game_def weak_eval_hiding_adversary1_def
    apply (rule unpack_try_spmf)
    apply (rule unpack_bind_spmf')+
    apply (rule ext; simp split: prod.splits add: split_paired_all del: return_bind_spmf bind_spmf_assoc 
        PickDistinct.simps)
    apply (rule unpack_bind_spmf)
    apply (rule unpack_bind_spmf')
    apply (rule ext; simp split: prod.splits add: split_paired_all del: PickDistinct.simps)
    apply (rule assert_based_eq)
    apply (drule PickDistinct_Prop) 
    apply (subst sample_uniform_evals_is_sample_poly[of "(PickDistinct a # a)" max_deg])
    apply simp+
    done
  text \<open>Now we bring the game in a nicer form and expose the Setup from key_gen\<close>
  also have "\<dots> = TRY do {
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
  return_spmf (p = p')} ELSE return_spmf False"
   by (simp add: bind_spmf_assoc key_gen_def bind_map_spmf o_def Setup_def split_def Let_def 
       del: PickDistinct.simps)
  text \<open>Now we replace the Commit computed with a valid public key PK by interpolate_on\<close>
  also have "\<dots> = TRY do {
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
  return_spmf (p = p')} ELSE return_spmf False"
    apply (simp only: Let_def split_def)
    apply (rule unpack_try_spmf; rule unpack_bind_spmf')+
    apply (rule ext; simp split: prod.splits add: split_paired_all 
        del: return_bind_spmf bind_spmf_assoc PickDistinct.simps One_nat_def; 
        rule unpack_bind_spmf'; rule ext)
    apply (rule assert_based_eq)
    apply (rule unpack_bind_spmf';rule ext; simp split: prod.splits add: split_paired_all 
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
  shows "spmf (game1 \<A>1 \<A>2) True \<le> spmf (game2 \<A>1 \<A>2) True + t_SDH_G\<^sub>p.advantage (reduction_tSDH \<A>1)"
proof -
  note [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD map_spmf_bind_spmf bind_spmf_const Let_def o_def
  note %invisible [cong del] = if_weak_cong 
   and [split del] = if_split
   and [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD map_spmf_bind_spmf bind_spmf_const
   and [if_distribs] = if_distrib[where f="\<lambda>x. try_spmf x _"] if_distrib[where f="weight_spmf"] if_distrib[where f="\<lambda>r. scale_spmf r _"]

  define game1b :: "('e mod_ring,'a vk, 'e argument, 'f) weak_eval_hiding_adversary1 \<Rightarrow> 
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

   define game2b :: "('e mod_ring,'a vk, 'e argument, 'f) weak_eval_hiding_adversary1 \<Rightarrow> 
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
  define collision_game :: "('e mod_ring,'a vk, 'e argument, 'f) weak_eval_hiding_adversary1 \<Rightarrow> bool spmf" where 
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
  t-SDH assumption\<close>
  have spmf_collision_game: "spmf (collision_game \<A>1) True
  \<le> t_SDH_G\<^sub>p.advantage (reduction_tSDH \<A>1)"
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
     _ :: unit \<leftarrow> assert_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>(1/\<alpha>')); 
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
      _ :: unit \<leftarrow> assert_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>(1/\<alpha>'));
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
     return_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>+0) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>(1/\<alpha>'))
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
     return_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>+0) = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>(1/\<alpha>'))
      } ELSE return_spmf False) True"
        by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
      also have "\<dots> = spmf (TRY do {
     \<alpha> \<leftarrow> sample_uniform (order G\<^sub>p);
     let (\<alpha>::'e mod_ring) = (of_int_mod_ring \<circ> int) \<alpha>;
     let PK =  map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
     (c,g) \<leftarrow> do {
        (I,\<sigma>) \<leftarrow> \<A>1 PK;
        let (\<alpha>'::'e mod_ring) = (case (find (\<lambda>x. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = PK!1) (PickDistinct I#I)) of Some x => x | None => 1);
        return_spmf (0, \<^bold>g ^\<^bsub>G\<^sub>p\<^esub>(1/\<alpha>'))};
     return_spmf (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> ((1::'e mod_ring)/\<alpha>+c) = g)
      } ELSE return_spmf False) True"
        unfolding Let_def split_def by force
      also have "\<dots> = t_SDH_G\<^sub>p.advantage (reduction_tSDH \<A>1)"
        unfolding t_SDH_G\<^sub>p.advantage_def t_SDH_G\<^sub>p.game_def reduction_tSDH.simps Let_def split_def
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
  \<le> DL_G\<^sub>p.advantage (reduction \<A>1 \<A>2) + t_SDH_G\<^sub>p.advantage (reduction_tSDH \<A>1)"
proof -
  have "weak_eval_hiding_advantage \<A>1 \<A>2 = spmf (game1 \<A>1 \<A>2) True"
    using hiding_game_to_game1
    unfolding weak_eval_hiding_advantage_def eval_hiding_advantage_def 
      weak_eval_hiding_adversary1_def weak_eval_hiding_game_def
    by metis 
  also have "\<dots> \<le> spmf (game2 \<A>1 \<A>2) True + t_SDH_G\<^sub>p.advantage (reduction_tSDH \<A>1)"
    using assms fundamental_lemma_game1_game2 by blast
  also have "\<dots> \<le> DL_G\<^sub>p.advantage (reduction \<A>1 \<A>2) + t_SDH_G\<^sub>p.advantage (reduction_tSDH \<A>1)"
    by (simp add: game2_le_DL)
  finally show ?thesis .
qed

end

end
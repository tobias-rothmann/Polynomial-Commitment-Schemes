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



definition hiding_game :: "'e eval_position list \<Rightarrow> 'e polynomial \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf"
  where "hiding_game eval_pos \<phi> \<A> = TRY do {
  _ :: unit \<leftarrow> assert_spmf (length eval_pos = max_deg);
  PK \<leftarrow> key_gen;
  let C = Commit PK \<phi>;
  let witn_tupel = map (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) eval_pos;
  \<phi>' \<leftarrow> \<A> C witn_tupel;
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"


definition hiding_game :: "'a commit \<Rightarrow>(('e,'a) witness_tuple) list \<Rightarrow> ('a, 'e) adversary 
  \<Rightarrow> bool spmf" where
  "hiding_game C witn_tpl_list \<A> = TRY do {
      \<phi>' \<leftarrow> \<A> C witn_tpl_list;
      PK \<leftarrow> key_gen;
      _::unit \<leftarrow> assert_spmf (\<exists>\<phi> eval_pos_list. C = Commit PK \<phi> 
           \<and> witn_tpl_list = map (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) eval_pos_list
           \<and> \<phi> = \<phi>');
      return_spmf True
    } ELSE return_spmf False"

text \<open>put C and eval_poses in parameter and assert\<close>

definition hiding_advantage :: "'e eval_position list \<Rightarrow>  'e polynomial \<Rightarrow> ('a, 'e) adversary \<Rightarrow> real"
  where "hiding_advantage eval_pos \<phi> \<A> \<equiv> spmf (hiding_game eval_pos \<phi> \<A>) True"

subsection \<open>DL game\<close>

sublocale DL_G\<^sub>p: DL G\<^sub>p "of_int_mod_ring \<circ> int" pow_mod_ring_G\<^sub>p
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

definition sample_coords :: "('e mod_ring \<times> 'e mod_ring) list spmf"
where 
  "sample_coords =
    map_spmf (map (\<lambda>(x,y). (of_int_mod_ring (int x),of_int_mod_ring (int y))))
    (sample_distinct_coordinates_uniform max_deg (order G\<^sub>p))"


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

fun reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e) DL.adversary"                     
where
  "reduction \<A> g_pow_a = do {
    (\<alpha>, PK) \<leftarrow> Setup;
    coords \<leftarrow> sample_coords;
    let exp_coords = (0,g_pow_a)#map (\<lambda>(x,y). (x,\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y)) coords;
    let g_pow_\<phi>_of_\<alpha> = compute_g_pow_\<phi>_of_\<alpha> exp_coords \<alpha>;
    let wtn_tuples = map (\<lambda>(x,y). (x,y,(g_pow_\<phi>_of_\<alpha>  \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>-x))) coords;
    \<phi>' \<leftarrow> \<A> g_pow_\<phi>_of_\<alpha> wtn_tuples;
    return_spmf (poly \<phi>' 0)}"


end





end 

end
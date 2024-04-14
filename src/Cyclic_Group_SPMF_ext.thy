theory Cyclic_Group_SPMF_ext

imports CryptHOL.Cyclic_Group_SPMF "HOL-Computational_Algebra.Polynomial" 
  Berlekamp_Zassenhaus.Finite_Field Polynomial_Interpolation.Lagrange_Interpolation
  Polynomial_Interpolation.Polynomial_Interpolation

begin

hide_const order

text \<open>We extend CryptHOL.Cyclic_Group_SPMF to sets and lists. 
We provide sampling of uniform random sets and lists. 
Additionally, we provide uniform sampling of polynomials over finite fields and show them equivalent 
to interpolating on a zipped list of coordinates where the evaluations are a uniformly random 
chosen list.\<close>

subsection \<open>sample uniform set\<close>

definition sample_uniform_set :: "nat \<Rightarrow> nat \<Rightarrow> nat set spmf"
  where "sample_uniform_set k n = spmf_of_set {x. x \<subseteq> {..<n} \<and> card x = k}"

lemma spmf_sample_uniform_set: "spmf (sample_uniform_set k n) x 
  = indicator {x. x \<subseteq> {..<n} \<and> card x = k} x / (n choose k)"
  by (simp add: n_subsets sample_uniform_set_def spmf_of_set)

lemma weight_sample_uniform_set: "weight_spmf (sample_uniform_set k n) = of_bool (k\<le>n)"
  apply (auto simp add: sample_uniform_set_def weight_spmf_of_set split: if_splits)
   apply (metis card_lessThan card_mono finite_lessThan)
  using card_lessThan by blast

lemma weight_sample_uniform_set_k_0 [simp]: "weight_spmf (sample_uniform_set 0 n) = 1"
  by (auto simp add: weight_sample_uniform_set)

lemma weight_sample_uniform_set_n_0 [simp]: "weight_spmf (sample_uniform_set k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_uniform_set)

lemma weight_sample_uniform_set_k_le_n [simp]: "k\<le>n \<Longrightarrow> weight_spmf (sample_uniform_set k n) = 1"
  by (auto simp add: weight_sample_uniform_set indicator_def gr0_conv_Suc)

lemma lossless_sample_uniform_set [simp]: "lossless_spmf (sample_uniform_set k n) \<longleftrightarrow> k \<le> n"
  by (auto simp add: lossless_spmf_def weight_sample_uniform_set intro: ccontr)

lemma set_spmf_sample_uniform_set [simp]: "set_spmf (sample_uniform_set k n) = {x. x \<subseteq> {..<n} \<and> card x = k}"
  by(simp add: sample_uniform_set_def)


subsection \<open>sample uniform list\<close>

definition sample_uniform_list :: "nat \<Rightarrow> nat \<Rightarrow> nat list spmf"
  where "sample_uniform_list k n = spmf_of_set {x. set x \<subseteq> {..<n} \<and> length x = k}"

lemma spmf_sample_uniform_list: "spmf (sample_uniform_list k n) x 
  = indicator {x. set x \<subseteq> {..<n} \<and> length x = k} x / (n^k)"
  by (simp add: card_lists_length_eq sample_uniform_list_def spmf_of_set)

lemma weight_sample_uniform_list: "weight_spmf (sample_uniform_list k n) = of_bool (k=0 \<or> 0<n)"
proof -
  have "0 < n \<longrightarrow> (\<exists>x. set x \<subseteq> {..<n} \<and> length x = k)"
  proof
    assume zero_l_n: "0 < n"
    show "\<exists>x. set x \<subseteq> {..<n} \<and> length x = k"
    proof 
      let ?x = "replicate k 0"
      show "set ?x \<subseteq> {..<n} \<and> length ?x = k"
        using zero_l_n by fastforce
    qed
  qed
  then show ?thesis 
    by (simp add: finite_lists_length_eq sample_uniform_list_def weight_spmf_of_set)
qed
  
lemma weight_sample_uniform_list_k_0 [simp]: "weight_spmf (sample_uniform_list 0 n) = 1"
  by (auto simp add: weight_sample_uniform_list)

lemma weight_sample_uniform_list_n_0 [simp]: "weight_spmf (sample_uniform_list k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_uniform_list)

lemma weight_sample_uniform_list_k_le_n [simp]: "k<n \<Longrightarrow> weight_spmf (sample_uniform_list k n) = 1"
  by (auto simp add: weight_sample_uniform_list less_iff_Suc_add)

lemma lossless_sample_uniform_list [simp]: "lossless_spmf (sample_uniform_list k n) \<longleftrightarrow> (k=0 \<or> 0<n)"
  by (auto simp add: lossless_spmf_def weight_sample_uniform_list intro: ccontr)

lemma set_spmf_sample_uniform_list [simp]: "set_spmf (sample_uniform_list k n) = {x. set x \<subseteq> {..<n} \<and> length x = k}"
  by (simp add: finite_lists_length_eq sample_uniform_list_def)

lemma "bind_spmf (spmf_of_set {X}) spmf_of_set = spmf_of_set X"
  by (simp add: spmf_of_set_singleton)

text \<open>the two following lemmas are helping lemmas for Cons_random_list_split\<close>

lemma set_spmf_lhs: "set_spmf (map_spmf ((#) x) (sample_uniform_list k p)) 
             = {xs. set (tl xs) \<subseteq> {..<p} \<and> length xs = k+1 \<and> hd xs = x}"
proof -
  fix x
  have "set_spmf (map_spmf ((#) x) (sample_uniform_list k p)) 
    = ((#) x) ` {xs. set xs \<subseteq> {..<p} \<and> length xs = k}" 
    unfolding sample_uniform_list_def
    by (simp add: finite_lists_length_eq)
  also have "\<dots> = {xs. set (tl xs) \<subseteq> {..<p} \<and> length xs = k+1 \<and> hd xs = x}"
    (* TODO cleanup in case*)
    apply auto
    by (smt (verit) Suc_length_conv image_Collect list.sel(1) list.sel(3) mem_Collect_eq)
  finally show "set_spmf (map_spmf ((#) x) (sample_uniform_list k p)) 
      = {xs. set (tl xs) \<subseteq> {..<p} \<and> length xs = k + 1 \<and> hd xs = x}"
    .
qed

lemma set_spmf_lhs_imp_length_gr_0: "xs \<in> set_spmf (map_spmf ((#) x) (sample_uniform_list k p)) 
  \<Longrightarrow> length xs > 0"
  unfolding set_spmf_lhs by force

text \<open>sampling a uniform random list can be split up into prepending a uniform random element
to a one element short uniform random list. 
Intuitively: sample_uniform_list (k+1) = Cons (sample_uniform) (sample_uniform_list k)\<close>
lemma Cons_random_list_split: 
  assumes "p>1"
  shows "do {x \<leftarrow> sample_uniform p;
            map_spmf ((#) x) (sample_uniform_list k p)} = sample_uniform_list (k+1) p"
  (is "?lhs = ?rhs")
proof -
  have "\<forall>s. spmf ?lhs s = spmf ?rhs s"
  proof 
    fix s
    have spmf_rhs: "spmf ?rhs s = indicator {x. set x \<subseteq> {..<p} \<and> length x = k+1} s / real p^(k+1)"
      unfolding spmf_sample_uniform_list ..
    have spmf_lhs: "spmf ?lhs s 
        = (\<Sum>x<p. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) 
        / of_nat (card {..<p})"
        unfolding ennreal_spmf_bind
        unfolding sample_uniform_def
        unfolding nn_integral_spmf_of_set
        ..
    show "spmf ?lhs s = spmf ?rhs s"
    proof (cases s)
      case Nil
      have "spmf ?lhs s = 0"
      proof -
        have "\<And>x. spmf (map_spmf ((#) x) (sample_uniform_list k p)) s = 0"
          using set_spmf_lhs set_spmf_lhs_imp_length_gr_0 spmf_eq_0_set_spmf
          unfolding Nil 
          by fast
        then show ?thesis 
         using spmf_lhs by force
      qed
      moreover have "spmf ?rhs s = 0"
        using spmf_rhs 
        unfolding Nil
        by force
      ultimately show ?thesis by presburger
    next
      case (Cons s_hd s_tl)
      then show ?thesis
      proof (cases "s_hd<p")
        case True
        have "spmf ?lhs s
          = (indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^(k+1)))"
        proof - 
          have spmf_is_sum: "spmf ?lhs s = 
              sum (\<lambda>x. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) {..<p} 
              / real (card {..<p})"
                unfolding spmf_lhs
                using ennreal_of_nat_eq_real_of_nat by presburger
          also have "sum (\<lambda>x. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) {..<p}
          = sum (\<lambda>x. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) (({..<p}-{s_hd}) \<union> {s_hd})"
            by (simp add: True insert_absorb)
          also have "\<dots> = sum (\<lambda>x. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) ({..<p}-{s_hd})
            + ennreal (spmf (map_spmf ((#) s_hd) (sample_uniform_list k p)) s)"
            by (metis (no_types, lifting) Un_insert_right add.commute dual_order.refl finite_nat_iff_bounded insert_Diff_single sum.insert_remove sup_bot.right_neutral)
          also have "\<dots> = ennreal (spmf (map_spmf ((#) s_hd) (sample_uniform_list k p)) s)"
          proof -
            have "\<And>x. x \<in> {..<p}-{s_hd} \<longrightarrow> ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s) = 0"
            proof 
              fix x 
              assume "x \<in> {..<p} - {s_hd}"
              then have "x \<noteq> s_hd" by blast
              then show "ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s) = 0"
                using set_spmf_lhs 
                unfolding Cons 
                by (simp add: spmf_eq_0_set_spmf)
            qed
            then show ?thesis by force
          qed
          also have "\<dots> = ennreal (spmf (sample_uniform_list k p) s_tl)"
            unfolding Cons
            using spmf_map_inj
            by (simp add: spmf_map_inj')
          also have "\<dots> = indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^k)"
            unfolding spmf_sample_uniform_list ..
          finally have "ennreal (spmf ?lhs s) = ennreal ((indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^k))) /  ennreal (real (card {..<p}))"
            by argo
          then have "spmf ?lhs s = (indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^k)) / (real (card {..<p}))"
            using assms(1) divide_ennreal by auto
          also have "\<dots> = (indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^(k+1)))"
            by auto
          finally show ?thesis .
        qed

        moreover have "spmf ?rhs s
          = (indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^(k+1)))"
        proof -
          have "(s_hd # s_tl) \<in> {x. set x \<subseteq> {..<p} \<and> length x = k + 1} 
          \<longleftrightarrow> s_tl \<in> {x. set x \<subseteq> {..<p} \<and> length x = k}"
            by (simp add: True)
          then show ?thesis
            unfolding spmf_sample_uniform_list Cons
            by (metis (no_types, lifting) indicator_simps(1) indicator_simps(2))
        qed
        ultimately show ?thesis by presburger
      next
        case False
        have "spmf ?lhs s = 0"
      proof -
        have "\<And>x. x<p \<longrightarrow> spmf (map_spmf ((#) x) (sample_uniform_list k p)) s = 0"
          unfolding Cons 
          using set_spmf_lhs spmf_eq_0_set_spmf False
          by fastforce
        then show ?thesis
         using spmf_lhs by force
      qed
      moreover have "spmf ?rhs s = 0"
        using spmf_rhs 
        unfolding Cons
        using False
        by fastforce
      ultimately show ?thesis by presburger
      qed
    qed
  qed
  then show ?thesis
    using spmf_eqI by blast
qed

text \<open>This corollary puts the last lemma in a more readable and thus workable definition.
Intuitively: sample_uniform_list (k+1) = Cons (sample_uniform) (sample_uniform_list k)\<close>
corollary pretty_Cons_random_list_split: 
  assumes "p>1"
  shows "sample_uniform_list (k+1) p =
    do {x \<leftarrow> sample_uniform p;
        xs \<leftarrow> (sample_uniform_list k p);
        return_spmf (x#xs)}"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = do {x \<leftarrow> sample_uniform p;
          map_spmf ((#) x) (sample_uniform_list k p)}"
    by (simp add: map_spmf_conv_bind_spmf)
  then show ?thesis 
    using Cons_random_list_split[symmetric, OF assms]
    by presburger
qed

subsection \<open>sample uniform polynomial\<close>

definition sample_uniform_poly :: "nat \<Rightarrow> 'a::zero poly spmf" 
  where "sample_uniform_poly t = spmf_of_set {p. degree p \<le> t}"

lemma of_int_mod_inj_on_ff: "inj_on (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e::prime_card mod_ring) {..<CARD ('e)}"
proof 
  fix x 
  fix y
  assume x: "x \<in> {..<CARD('e)}"
  assume y: "y \<in> {..<CARD('e)}"
  assume app_x_eq_y: "(of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) x = (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) y"
  show "x = y"
    using x y app_x_eq_y 
    by (metis comp_apply lessThan_iff nat_int of_nat_0_le_iff of_nat_less_iff to_int_mod_ring_of_int_mod_ring)
qed

text \<open>sampling a uniform random polynomial is equivalent to interpolating a polynomial from a list 
of uniform random chosen evaluations\<close>
lemma sample_uniform_evals_is_sample_poly:
  assumes "distinct I"
  and "length I = t+1"
  shows "(sample_uniform_poly t::'e mod_ring poly spmf) = do {
      evals::('e::prime_card) mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (t+1) (CARD ('e)));
      return_spmf (lagrange_interpolation_poly (zip I evals))}"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = do {
      evals \<leftarrow> spmf_of_set {x::'e mod_ring list. length x = t + 1};
      return_spmf (lagrange_interpolation_poly (zip I evals))}"
  proof - 
    have uni_list_set_is_card_set: "(\<Union> (set ` {x::nat list. set x \<subseteq> {..<CARD('e)} \<and> length x = t + (1::nat)})) 
      = {..<CARD('e)}"
    proof 
      show "{..<CARD('e)} \<subseteq> \<Union> (set ` {x::nat list. set x \<subseteq> {..<CARD('e)} \<and> length x = t + (1::nat)})"
      proof 
        fix x 
        assume "x \<in> {..<CARD('e)}"
        then have "replicate (t+1) x \<in> {x::nat list. set x \<subseteq> {..<CARD('e)} \<and> length x = t + (1::nat)}"
          by fastforce
        then show "x \<in> \<Union> (set ` {x::nat list. set x \<subseteq> {..<CARD('e)} \<and> length x = t + (1::nat)})"
          by fastforce
      qed
    qed auto
    have "map_spmf (map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) (sample_uniform_list (t + 1) CARD('e))
    = spmf_of_set ((map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) ` {x. set x \<subseteq> {..<CARD('e)} \<and> length x = t+1})"
    (is "?map = ?set")
      unfolding sample_uniform_list_def
      apply (rule map_spmf_of_set_inj_on)
      apply (rule inj_on_mapI)
      unfolding uni_list_set_is_card_set
      by (rule of_int_mod_inj_on_ff)
    also have "(map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring)) ` {x. set x \<subseteq> {..<CARD('e)} \<and> length x = t+1} 
      = {x::'e mod_ring list. length x = t + 1}"
    proof 
      show "{x::'e mod_ring list. length x = t + (1::nat)}
        \<subseteq> map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) ` {x::nat list. set x \<subseteq> {..<CARD('e)} \<and> length x = t + (1::nat)}"
      proof 
        fix x 
        assume asm: "x \<in> {x::'e mod_ring list. length x = t + (1::nat)}"
        obtain x_int where x_int : "x_int = map to_int_mod_ring x" by force
        have x_eq_map_x_int: "x = map of_int_mod_ring x_int"
          unfolding x_int 
          by (simp add: nth_equalityI)
        obtain x_nat where x_nat: "x_nat = map nat x_int" by simp
        have x_int_x_nat: "x_int = map int x_nat"
        proof -
          have "map int x_nat =  map (\<lambda>i. if i\<ge>0 then i else 0)  x_int"
            unfolding x_nat using int_nat_eq by simp
          moreover have "\<forall>x \<in> set x_int. x\<ge>0"
            unfolding x_int 
            using range_to_int_mod_ring
            by (metis atLeastLessThan_iff ex_map_conv rangeI)
          ultimately show ?thesis
            by (simp add: map_idI)
        qed
        have "x_nat \<in> {x::nat list. set x \<subseteq> {..<CARD('e)} \<and> length x = t + (1::nat)}"
          unfolding x_nat x_int
          apply auto 
           apply (metis range_to_int_mod_ring UNIV_I atLeastLessThan_iff image_iff nat_less_iff)
          using asm apply force
          done
        moreover have "x = map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) x_nat"
          by (simp add: x_eq_map_x_int x_int_x_nat)
        ultimately show "x \<in> map (of_int_mod_ring \<circ> int:: nat \<Rightarrow> 'e mod_ring) 
          ` {x::nat list. set x \<subseteq> {..<CARD('e)} \<and> length x = t + (1::nat)}"
          by blast
      qed
    qed auto
    finally show ?thesis by metis
  qed
  also have "\<dots> =  do {
      evals \<leftarrow> spmf_of_set {x::'e mod_ring list. length x = t + 1};
      let \<phi> = lagrange_interpolation_poly (zip I evals);
      return_spmf \<phi>}" unfolding Let_def ..
  also have "\<dots> = map_spmf (\<lambda>evals. lagrange_interpolation_poly (zip I evals)) 
                         (spmf_of_set {x::'e mod_ring list. length x = t + 1})"
    by (simp add: map_spmf_conv_bind_spmf)
  also have "\<dots> = spmf_of_set ((\<lambda>evals. lagrange_interpolation_poly (zip I evals)) ` {x::'e mod_ring list. length x = t + 1})"
  proof (rule map_spmf_of_set_inj_on)
    show "inj_on (\<lambda>evals::'e mod_ring list. lagrange_interpolation_poly (zip I evals))
     {x::'e mod_ring list. length x = t + (1::nat)}"
    proof 
      fix x y
      assume x_in:"x \<in> {x::'e mod_ring list. length x = t + (1::nat)}"
      assume y_in:"y \<in> {x::'e mod_ring list. length x = t + (1::nat)}"
      assume asm: "lagrange_interpolation_poly (zip I x) = lagrange_interpolation_poly (zip I y)"
      have poly_xi: "\<And>i. i<length I \<Longrightarrow> poly (lagrange_interpolation_poly (zip I x)) (I!i) = x!i"
        using lagrange_interpolation_poly[of "zip I x" "lagrange_interpolation_poly (zip I x)"]
        assms(1)
        by (smt (verit, del_insts) assms(2) length_zip map_fst_zip mem_Collect_eq min_less_iff_conj nth_mem nth_zip x_in)
      have poly_y: "\<And>i. i<length I \<Longrightarrow> poly (lagrange_interpolation_poly (zip I y)) (I!i) = y!i"
        using lagrange_interpolation_poly[of "zip I y" "lagrange_interpolation_poly (zip I y)"]
        assms(1)
        by (smt (verit, del_insts) assms(2) length_zip map_fst_zip mem_Collect_eq min_less_iff_conj nth_mem nth_zip y_in)
      then have "\<And>i. i<length I \<Longrightarrow> poly (lagrange_interpolation_poly (zip I x)) (I!i) = y!i"
        using asm by presburger
      then show "x=y"
        using poly_y assms(2) x_in y_in
        by (simp add: nth_equalityI poly_xi)
    qed
  qed
  also have "\<dots> = spmf_of_set {p. degree p \<le> t}"
    (is "?map = ?set")
  proof -
    have "{p. degree p \<le> t} = (\<lambda>evals::'e mod_ring list. lagrange_interpolation_poly (zip I evals)) `
      {x::'e mod_ring list. length x = t + (1::nat)}"
    proof 
      show "{p::'e mod_ring poly. degree p \<le> t}
    \<subseteq> (\<lambda>evals::'e mod_ring list. lagrange_interpolation_poly (zip I evals)) `
       {x::'e mod_ring list. length x = t + (1::nat)}"
      proof 
        fix x 
        assume asm: "x \<in> {p::'e mod_ring poly. degree p \<le> t}"
        obtain x_evals where x_evals: "x_evals = map (\<lambda>i. poly x i) I" by simp
        then have "length x_evals = t+1"
          by (simp add: assms(2))
        moreover have "x = lagrange_interpolation_poly (zip I x_evals)"
          apply (rule uniqueness_of_interpolation_point_list[of "zip I x_evals" x "lagrange_interpolation_poly (zip I x_evals)"])
              apply (simp add: assms(1) x_evals)
             apply (metis fst_eqD in_set_zip nth_map snd_eqD x_evals)
          using asm assms(2) calculation apply force
           apply (metis assms(1) assms(2) calculation lagrange_interpolation_poly map_fst_zip)
          apply (metis Suc_eq_plus1 assms(2) calculation degree_lagrange_interpolation_poly diff_Suc_1 le_refl length_zip less_Suc_eq min.absorb1 order.strict_trans1)
          done
        ultimately show "x \<in> (\<lambda>evals::'e mod_ring list. lagrange_interpolation_poly (zip I evals)) `
            {x::'e mod_ring list. length x = t + (1::nat)}"
          by blast
      qed
      show "(\<lambda>evals::'e mod_ring list. lagrange_interpolation_poly (zip I evals)) `
    {x::'e mod_ring list. length x = t + (1::nat)}
    \<subseteq> {p::'e mod_ring poly. degree p \<le> t}"
      proof 
        fix x 
        assume asm: "x \<in> (\<lambda>evals::'e mod_ring list. lagrange_interpolation_poly (zip I evals)) `
            {x::'e mod_ring list. length x = t + (1::nat)}"
        then show "x \<in> {p::'e mod_ring poly. degree p \<le> t}"
          using degree_lagrange_interpolation_poly
          by (smt (verit) Nat.le_diff_conv2 One_nat_def Suc_eq_plus1 add_leE diff_Suc_1 diff_is_0_eq image_iff le_trans length_zip mem_Collect_eq min.absorb1 min.absorb2 nat_le_linear plus_1_eq_Suc zero_le)
      qed
    qed
    then show ?thesis by argo
  qed
  finally show ?thesis 
    unfolding sample_uniform_poly_def by argo
qed


end
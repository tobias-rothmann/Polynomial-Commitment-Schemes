theory KZG_correct

imports KZG_Def 
begin

locale KZG_correct = KZG_Def
begin

section \<open>Correctness proving that the interaction of an honest prover and an honest verifier
always yields correct results.\<close>

text\<open>The outline for the correctness proof in this file is to be found in section 3.2 of the 
original paper "Constant-Size Commitments to Polynomials and Their Applications".
I strongly recommend reading the section 3.2 of the paper before trying to 
understand this correctness proof. 
You can find the paper here: https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf\<close>

text \<open>The KZG has two stages: 
1. the polynomial stage, 
where the prover commits to a polynomial and can open the commitment by revealing the 
polynomial.
2. the evaluation stage,
where the prover can commit and open commitments to single evaluations of the polynomial, which was 
already commited to, but which wasn't opened yet. \<close>

subsection \<open>Verifying stage 1:
that a correct Setup with a correct commit (to a polynomial) yields a correct verification of a polynomial commitment.\<close>

definition Poly_Commit_game:: "'e polynomial \<Rightarrow> bool spmf"
  where "Poly_Commit_game \<phi> = 
    do{
    (\<alpha>,PK) \<leftarrow> Setup;
    let C = Commit PK \<phi>;
    return_spmf (VerifyPoly PK C \<phi>)
    }"

lemma lossless_Setup: "lossless_spmf Setup"
  unfolding Setup_def 
  by (metis (no_types, lifting) G\<^sub>p.order_gt_0 lossless_bind_spmf lossless_return_spmf lossless_sample_uniform)

text \<open>theorem stating the goal of the subsection: 
Verifying that a correct Setup with a correct commit (to a polynomial) yields a correct verification\<close>
theorem Poly_Commit_correct: "spmf (Poly_Commit_game \<phi>) True = 1"
proof -
  have weight_Setup: "weight_spmf Setup = 1" using lossless_spmf_def lossless_Setup by fast
  have "(Poly_Commit_game \<phi>) = 
   do{
    (\<alpha>,PK) \<leftarrow> Setup;
    return_spmf True
    }"
  unfolding Poly_Commit_game_def Commit_def VerifyPoly_def by force
  also have "\<dots> = scale_spmf (weight_spmf Setup) (return_spmf True)"
    by (simp add: split_def)(rule bind_spmf_const)
  also have "\<dots> = return_spmf True" using weight_Setup by force
  finally show ?thesis by fastforce
qed

subsection \<open>Verifying stage 2:
that a correct Setup with a correct commit to a polynomial and a correctly computed 
evaluation witness, yields a correct verification of the evaluation\<close>

definition Eval_Commit_game:: "'e polynomial \<Rightarrow> 'e eval_position  \<Rightarrow> bool spmf"
  where "Eval_Commit_game \<phi> i = 
    do{
    (\<alpha>,PK) \<leftarrow> Setup;
    let C = Commit PK \<phi>;
    let (i, \<phi>_of_i, w_i) = CreateWitness PK \<phi> i;
    return_spmf (VerifyEval PK C i \<phi>_of_i w_i)
    }"

subsubsection \<open>helping lemmas for the computation of \<psi> (function \<psi>_of) in \<phi>(x)-\<phi>(c)=(x-c)*\<psi>(x), 
which is used to compute \<psi> in CreateWitness.\<close> 

lemma coeffs_n_length[simp]: "length (coeffs_n \<phi> u q_co n) = n"
  unfolding coeffs_n_def by fastforce

lemma coeffs_n_add_nth[simp]: "\<forall>i<n. coeffs_n \<phi> u l n ! i = nth_default 0 l i + poly.coeff \<phi> n * u ^ (n - Suc i)"
  unfolding coeffs_n_def by auto

lemma \<psi>_coeffs_length: "length (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) = n"
  by auto

lemma sum_split: "m\<le>n \<Longrightarrow> (\<Sum>i\<le>n. f i) = (\<Sum>i\<le>m. f i) + (\<Sum>i\<in>{m<..<Suc n}. f i)"
proof -
  assume "m\<le>n"
  then show "(\<Sum>i\<le>n. f i) = (\<Sum>i\<le>m. f i) + (\<Sum>i\<in>{m<..<Suc n}. f i)"
  proof (induction n arbitrary: m)
    case 0
    then show ?case
      using greaterThanLessThan_upt by fastforce
  next
    case (Suc n)
    then show ?case
      using greaterThanLessThan_upt
      by (metis Suc_le_mono atLeast0AtMost atLeastLessThanSuc_atLeastAtMost atLeastSucLessThan_greaterThanLessThan less_eq_nat.simps(1) sum.atLeastLessThan_concat)
  qed
qed

text \<open>state that the computed polynomial \<psi>, is of degree less equal to \<phi>.\<close>
lemma degree_q_le_\<phi>: "degree (\<psi>_of \<phi> u) \<le> degree \<phi>"
  unfolding \<psi>_of_def
  by (metis degree_Poly \<psi>_coeffs_length)

text \<open>This lemma is essentially resorting the summation according to the idea given in KZG_def 
above the CreateWitness definition.

The left-hand side co computes the coefficients horizontal, in the sense that it computes 
the coefficients from 0 to degree \<phi> = n, and adds (or could add) to each coefficient in every iteration:
0: 0 +
1: f1 +
2: f2*u + f2*x +
3: f3*u^2 + f3*u*x + f3*x^2
...
n: fn*u^(n-1) + ... fn*u^((n-1)-i)*x^i ...  + fn*x^(n-1)

The right-hand side captures the vertical summation in a sum in the sum. Hence computing the 
coefficient in the inner sum first, before multiplying it with x^i. Illustrated:
0: (0 + f1 + f2*u + f3*u^2 + ... + fn*u^(n-1))*x^0 + 
1: (0 + 0  + f2   + f3*u   + ... + fn*u^(n-2))*x^1
...
n: (0 +  0 +  0   +  0     + ... + fn)*x^(n-1)
\<close>
lemma sum_horiz_to_vert: "n\<le>degree (\<phi>::'e mod_ring poly) \<Longrightarrow> 
       (\<Sum>i\<le>n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) 
     = (\<Sum>i\<le>n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x^i)"
proof (induction n arbitrary: \<phi>)
  case 0
  have "(\<Sum>i\<le>0. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) = 0" by fastforce
  also have "(\<Sum>i\<le>0. (\<Sum>j\<in>{i<..<Suc 0}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) = 0"
    by (simp add: greaterThanLessThan_upt)
  ultimately show ?case by argo
next
  case (Suc n)
  have "(\<Sum>i\<le>Suc n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) 
      = (\<Sum>i\<le>n. poly.coeff \<phi> i * (\<Sum>j<i. u ^ (i - Suc j) * x ^ j)) 
      + poly.coeff \<phi> (Suc n) * (\<Sum>j<(Suc n). u ^ (Suc n - Suc j) * x ^ j)" by auto
  also have "\<dots> = (\<Sum>i\<le>n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) 
                + poly.coeff \<phi> (Suc n) * (\<Sum>j<(Suc n). u ^ (Suc n - Suc j) * x ^ j)"
    using Suc.IH Suc.prems Suc_leD by presburger
  also have "\<dots>=(\<Sum>i\<le>n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) 
                + (\<Sum>j<(Suc n). poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc j) * x ^ j)"
    by (metis (mono_tags, lifting) mult.assoc mult_hom.hom_sum sum.cong)
  also have "\<dots>=(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) 
                + (\<Sum>j<Suc n. poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc j) * x ^ j)"
    using lessThan_Suc_atMost by presburger
  also have "\<dots>=(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i 
                + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i) * x ^ i)"
    by (simp add: sum.distrib)
  also have "\<dots>=(\<Sum>i<Suc n. ((\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i))* x ^ i)"
    by (simp add: distrib_left mult.commute)
  also have "\<dots>=(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)" 
  proof -
    have "\<forall>(i::nat)<Suc n. ((\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i))
                   = (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i))"
    proof 
      fix i 
      show "i < Suc n \<longrightarrow>
         (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i) =
         (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i))"
      proof 
      let ?f = "(\<lambda>j. poly.coeff \<phi> j * u ^ (j - Suc i))"
      assume asmp: "i < Suc n"
      then show "(\<Sum>j\<in>{i<..<Suc n}. ?f j) + ?f (Suc n) = (\<Sum>j\<in>{i<..<Suc (Suc n)}. ?f j)"
        by (smt (verit) atLeastSucLessThan_greaterThanLessThan not_less_eq sum.op_ivl_Suc)
      qed
    qed
    then show "(\<Sum>i<Suc n. ((\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i)) * x ^ i) =
    (\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)"
      by fastforce
  qed
  also have "\<dots>=(\<Sum>i\<le>Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)"
  proof -
    have "(\<Sum>j\<in>{Suc n<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc (Suc n))) * x ^ (Suc n) = 0"
      by (simp add: greaterThanLessThan_upt)
    then have "(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)
              = (\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i) 
              + (\<Sum>j\<in>{Suc n<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc (Suc n))) * x ^ (Suc n)"
      by force
    also have "\<dots>=(\<Sum>i\<le>Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)"
      by (simp add: lessThan_Suc_atMost)
    ultimately show "(\<Sum>i<Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)
             = (\<Sum>i\<le>Suc n. (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x ^ i)"
      by argo
  qed
  ultimately show ?case using Suc.prems Suc_leD by argo
qed

text \<open>We now show that the inner sum from the last lemma, which calculates the i-th coefficient for \<psi>, 
is equal to the i-th coefficient calculated from the \<psi>_of function.\<close>
lemma \<psi>_of_ith_coeff_eq_sum_ith_coeff: "i<n \<Longrightarrow> foldl (coeffs_n \<phi> u) [] [0..<Suc n] ! i
                                        = (\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i))"
proof (induction n arbitrary: i)
  case 0
  then show ?case by blast
next
  case (Suc n)
  then show ?case
  proof (cases "i<n")
    case True
    have "foldl (coeffs_n \<phi> u) [] [0..<Suc (Suc n)] 
      = map (\<lambda>i. nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i))
     [0..<Suc n]"
      unfolding coeffs_n_def by force
    then have "foldl (coeffs_n \<phi> u) [] [0..<Suc (Suc n)] ! i 
        = nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i)"
      by (metis (lifting) Suc.prems add_0 diff_zero nth_map_upt)
    also have "\<dots>=(\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i)"
      using Suc.IH[of i] by (simp add: True nth_default_def)
    also have "\<dots>=(\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i))"
    proof -
      have "\<forall>x y f. x<y \<longrightarrow> (\<Sum>j\<in>{x<..<y}. f j) + f y = (\<Sum>j\<in>{x<..<Suc y}. f j)"
        by (metis Suc_le_eq atLeastSucLessThan_greaterThanLessThan sum.atLeastLessThan_Suc)
      then show "(\<Sum>j\<in>{i<..<Suc n}. poly.coeff \<phi> j * u ^ (j - Suc i)) + poly.coeff \<phi> (Suc n) * u ^ (Suc n - Suc i) =
    (\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i))" using Suc.prems by blast
    qed
    ultimately show ?thesis by argo
  next
    case False
    then have i_eq_n: "i=n" using Suc.prems by simp
    have "foldl (coeffs_n \<phi> u) [] [0..<Suc (Suc n)]
        = coeffs_n \<phi> u (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) (Suc n)" by simp
    also have "\<dots>=map (\<lambda>(i::nat). (nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i 
                       + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i))) [0..<Suc n]" 
      unfolding coeffs_n_def by blast 
    ultimately have "foldl (coeffs_n \<phi> u) [] [0..<Suc (Suc n)] ! i
                   = map (\<lambda>(i::nat). (nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i 
                       + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i))) [0..<Suc n] ! i"
      by argo
    also have "\<dots>= (nth_default 0 (foldl (coeffs_n \<phi> u) [] [0..<Suc n]) i 
                       + poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i))" 
      using Suc.prems calculation by auto
    also have "\<dots>=poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)"
      by (simp add: nth_default_eq_dflt_iff i_eq_n)
    also have "(\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) 
             = poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)"
    proof -
      have "{i<..<Suc (Suc n)} = {Suc n}"
      proof 
        show "{i<..<Suc (Suc n)} \<subseteq> {Suc n}"
          by (simp add: greaterThanLessThan_upt i_eq_n)
        show "{Suc n} \<subseteq> {i<..<Suc (Suc n)}"
          by (simp add: i_eq_n)
      qed
      then show "(\<Sum>j\<in>{i<..<Suc (Suc n)}. poly.coeff \<phi> j * u ^ (j - Suc i)) 
             = poly.coeff \<phi> (Suc n) * u ^ ((Suc n) - Suc i)"
        by simp
    qed
    ultimately show ?thesis by argo
  qed
qed


text \<open>We now take together the last few lemmas and definitions and show that \<psi>_of_poly 
calculates the correct \<psi>. 
With the sum_horiz_to_vert lemma, we restructure the left-hand side to calculate the 
coefficients of \<psi> before multiplying with x^i. 
With the \<psi>_of_ith_coeff_eq_sum_ith_coeff lemma, show the coefficients of the result of 
sum_horiz_to_vert equal to the coefficients calculated by \<psi>_of_poly and thus showing 
poly (\<psi>_of_poly \<phi> u) x equal to the result sum of sum_horiz_to_vert.\<close>
lemma \<phi>x_m_\<phi>u_eq_xmu_\<psi>x: "\<forall>\<phi>::'e mod_ring poly. poly \<phi> x - poly \<phi> u = (x-u) * poly (\<psi>_of \<phi> u) x"
proof
  fix \<phi>::"'e mod_ring poly"
  fix u x :: "'e mod_ring"
  show "poly \<phi> x - poly \<phi> u = (x-u) * poly (\<psi>_of \<phi> u) x"
  proof -
    let ?q_coeffs = "foldl (coeffs_n \<phi> u) [] [0..<Suc (degree \<phi>)]"
    let ?q_dirty ="(\<lambda>x. (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j)))"
    let ?q_vert  ="(\<lambda>x. (\<Sum>i\<le>degree \<phi>. (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) * x^i))"
    let ?q = "\<psi>_of \<phi> u"
    (*idee: über endl. Summen, see: poly_as_sum *)
    have "(\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * x ^ i) - (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * u ^ i) 
      = (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * (x ^ i - u ^ i))"
      by (simp add: sum_subtractf right_diff_distrib')
    also have "\<dots> = (\<Sum>i\<le>degree \<phi>. (x - u) * poly.coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j) * x^j))"
      by (simp add: mult.assoc mult.left_commute power_diff_sumr2)
    also have "\<dots> = (x - u) * (?q_dirty x)" 
      by (metis (mono_tags, lifting) mult.assoc mult_hom.hom_sum sum.cong)
    also have "\<dots>= (x-u) * (?q_vert x)" using sum_horiz_to_vert by auto
    also have "?q_vert x = poly ?q x"
    proof -
      (*  connect degree \<phi> sum and degree q sum  *)
      have "(\<Sum>i\<le>degree \<phi>. nth_default 0 ?q_coeffs i * x^i) 
          = (\<Sum>i\<le>degree ?q. nth_default 0 ?q_coeffs i * x^i)"
      proof -
        have "degree ?q \<le> degree \<phi>" by(rule degree_q_le_\<phi>) 
        also have "\<forall>n. n\<ge>degree ?q \<and> n\<le>degree \<phi> \<longrightarrow>  (\<Sum>i\<le>n. nth_default 0 ?q_coeffs i * x^i)
                                              = (\<Sum>i\<le>degree ?q. nth_default 0 ?q_coeffs i * x^i)"
        proof
          fix n
          show "n\<ge>degree ?q \<and> n\<le>degree \<phi> \<longrightarrow>  (\<Sum>i\<le>n. nth_default 0 ?q_coeffs i * x^i)
                                              = (\<Sum>i\<le>degree ?q. nth_default 0 ?q_coeffs i * x^i)"
          proof 
            let ?f = "nth_default 0 ?q_coeffs"
            assume asmp: "n\<ge>degree ?q \<and> n\<le>degree \<phi>"
            have "\<forall>i>degree ?q. ?f i = 0"
              using coeff_eq_0 coeffs_n_def
              by (metis \<psi>_of_def coeff_Poly_eq)
            then have "(\<Sum>i\<in>{degree ?q <..<Suc n}. ?f i * x^i) = 0"
              by fastforce
            also have "(\<Sum>i\<le>n. ?f i * x ^ i) = (\<Sum>i\<le>degree ?q. ?f i * x ^ i) + (\<Sum>i\<in>{degree ?q <..<Suc n}. ?f i * x^i)"
              using sum_split asmp by blast
            ultimately show "(\<Sum>i\<le>n. nth_default 0 ?q_coeffs i * x ^ i) 
                     = (\<Sum>i\<le>degree ?q. nth_default 0 ?q_coeffs i * x ^ i)"
              using asmp by auto
          qed
        qed
        ultimately show "(\<Sum>i\<le>degree \<phi> . nth_default 0 ?q_coeffs i * x^i) 
                 = (\<Sum>i\<le>degree ?q. nth_default 0 ?q_coeffs i * x^i)"
          by blast
      qed
      also have "?q_vert x = (\<Sum>i\<le>degree \<phi>. nth_default 0 ?q_coeffs i * x^i)"
      proof -
        have "\<forall>i\<le>degree \<phi>. (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) 
                          = nth_default 0 ?q_coeffs i"
        proof 
          fix i
          show "i \<le> degree \<phi> \<longrightarrow>
           (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) =
           nth_default 0 ?q_coeffs i"
          proof 
            assume asmp: "i \<le> degree \<phi>"
            then show "(\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) =
              nth_default 0 ?q_coeffs i"
            proof (cases "i<degree \<phi>")
              case True
              have "length ?q_coeffs = degree \<phi>" by simp
              then have "nth_default 0 ?q_coeffs i 
                  = ?q_coeffs ! i"
                by (simp add: True nth_default_nth)
              then show ?thesis using True \<psi>_of_ith_coeff_eq_sum_ith_coeff by presburger
            next
              case False
              then have "i=degree \<phi>" using asmp by fastforce
              have "length ?q_coeffs = degree \<phi>" by simp
              then have "nth_default 0 ?q_coeffs i = 0"
                by (simp add: \<open>i = degree \<phi>\<close> nth_default_beyond)
              also have "(\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. poly.coeff \<phi> j * u ^ (j - Suc i)) 
                        = 0"  using False greaterThanLessThan_upt by auto
              ultimately show ?thesis by argo
            qed
          qed
        qed
        then show "?q_vert x = (\<Sum>i\<le>degree \<phi>. nth_default 0 ?q_coeffs i * x^i)"
          by force
      qed
      ultimately show "?q_vert x = poly ?q x" 
        by (metis (no_types, lifting) \<psi>_of_def coeff_Poly_eq poly_altdef sum.cong) 
    qed
    ultimately show "poly \<phi> x - poly \<phi> u = (x-u) * poly (\<psi>_of \<phi> u) x"
      by (simp add: poly_altdef)
  qed
qed

text \<open>Taking the result to the bilinear function. 
We know \<phi>(x)-\<phi>(u)=(x-u)\<psi>(x) from the previous corollary, now we show the equality is also valid with 
the billinear function e.\<close>
lemma eq_on_e: "(e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (\<psi>_of \<phi> i) \<alpha>))  (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) 
      \<otimes>\<^bsub>G\<^sub>T\<^esub> (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>)^\<^bsub>G\<^sub>T\<^esub> (poly \<phi> i) 
      = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi> \<alpha>)) \<^bold>g\<^bsub>G\<^sub>p\<^esub>"
proof -
  have e_in_carrier: "(e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ) \<in> carrier G\<^sub>T" using e_symmetric by blast
  have "e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>_of \<phi> i) \<alpha>) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly \<phi> i 
      = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>_of \<phi> i) \<alpha>) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha> - i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly \<phi> i"
    using mod_ring_pow_mult_inv_G\<^sub>p by force
  also have "\<dots>= (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ) ^\<^bsub>G\<^sub>T\<^esub> ((poly (\<psi>_of \<phi> i) \<alpha>) * (\<alpha>-i))  \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly \<phi> i"
    using G\<^sub>p.generator_closed e_bilinear by presburger 
  also have "\<dots>= (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ) ^\<^bsub>G\<^sub>T\<^esub> ((poly (\<psi>_of \<phi> i) \<alpha>) * (\<alpha>-i) + poly \<phi> i)"
    using mod_ring_pow_mult_G\<^sub>T e_in_carrier by presburger
  also have "\<dots>= (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ) ^\<^bsub>G\<^sub>T\<^esub> (poly \<phi> \<alpha>)"
    by (metis Groups.mult_ac(2) \<phi>x_m_\<phi>u_eq_xmu_\<psi>x diff_add_cancel)
  also have "\<dots>= e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi> \<alpha>)) \<^bold>g\<^bsub>G\<^sub>p\<^esub>"
    by (simp add: e_linear_in_fst)
  finally show "e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>_of \<phi> i) \<alpha>) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> \<div>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i) \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly \<phi> i =
    e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly \<phi> \<alpha>) \<^bold>g\<^bsub>G\<^sub>p\<^esub>"
    .
qed

subsubsection \<open>helping lemmas about the public parameters PK\<close>

text \<open>Lemma that proves that the construction to calculate the public parameters in Isabelle 
actually computes the public parameters. 
Shwoing that the ith public parameter is actually the ith wṕublic parameter (g^(\<alpha>^i))\<close>
lemma PK_i: "i\<le>t \<Longrightarrow> map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<t + 1] ! i =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^i)"
proof (induction t)
  case 0
  then show ?case by force
next
  case (Suc t)
  then show ?case 
  proof (cases "i\<le>t")
    case True
    then show ?thesis
      by (metis (no_types, lifting) Groups.add_ac(2) Suc(1) Suc(2) diff_zero le_imp_less_Suc nth_map_upt plus_1_eq_Suc)
      next
        case False
        then show ?thesis
          by (metis (no_types, lifting) Suc(2) add_Suc_shift le_SucE le_imp_less_Suc less_diff_conv nth_map_upt plus_1_eq_Suc semiring_norm(51))
  qed
qed

text \<open>show 
(\<Prod>PK. \<phi>) = g * g^(\<alpha> ^ 1st coefficient of \<phi>) * g^((\<alpha>^2) ^ 2nd coefficient of \<phi>) * ... * g^((\<alpha>^t) ^ t-th coefficient of \<phi>)
Which is the first prestep to showing (\<Prod>PK. \<phi>) = g^\<phi>(\<alpha>).\<close>
lemma g_pow_PK_Prod_to_fold[simp]: "degree \<phi> \<le> t \<Longrightarrow> g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<t + 1]) \<phi> 
  = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^pk)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
proof -
  let ?PK = "map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<t + 1]"
  let ?g_pow_PK = "g_pow_PK_Prod ?PK \<phi>"
  assume asmpt: "degree \<phi> \<le> t"
  have "?g_pow_PK = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> ?PK!pk ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>" 
    by auto
  also have "fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (?PK)!pk ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>
           = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^pk)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>" 
  proof(rule List.fold_cong)
    show "\<one>\<^bsub>G\<^sub>p\<^esub> = \<one>\<^bsub>G\<^sub>p\<^esub>" by simp
    show "[0..<Suc (degree \<phi>)] = [0..<Suc (degree \<phi>)]" by blast
    show "\<And>x. x \<in> set [0..<Suc (degree \<phi>)] \<Longrightarrow>
         (\<lambda>g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> ?PK ! x       ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> x) 
       = (\<lambda>g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> x)"
    proof 
      fix x::nat
      fix g::'a
      assume "x \<in> set [0..<Suc (degree \<phi>)]"
      then have "?PK ! x = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x)" 
        using PK_i asmpt by auto
      then show "g \<otimes>\<^bsub>G\<^sub>p\<^esub> ?PK ! x ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> x = g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> x" 
        by presburger
    qed
  qed
  ultimately show "g_pow_PK_Prod ?PK \<phi> = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ pk) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff \<phi> pk) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
    by argo
qed

text \<open>show 
g^(\<Sum>i\<le>n. coeff \<phi> i * \<alpha>^i)
= g * g^(\<alpha> ^ 1st coefficient of \<phi>) * g^((\<alpha>^2) ^ 2nd coefficient of \<phi>) * ... * g^((\<alpha>^t) ^ t-th coefficient of \<phi>)
Which is the first prestep to showing (\<Prod>PK. \<phi>) = g^\<phi>(\<alpha>).\<close>
lemma poly_altdef_to_fold[symmetric]: "n\<le>degree \<phi>  \<Longrightarrow> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>n. poly.coeff \<phi> i * \<alpha> ^ i) 
                          = fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc n] \<one>\<^bsub>G\<^sub>p\<^esub>"
proof (induction n)
  case 0
  have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>0. poly.coeff \<phi> i * \<alpha> ^ i) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> 0 * \<alpha> ^ 0)"
    by force
  moreover have "fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc 0] \<one>\<^bsub>G\<^sub>p\<^esub> 
    =  \<one>\<^bsub>G\<^sub>p\<^esub> \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (0::nat) * \<alpha> ^ (0::nat))" by force
  moreover have "\<one>\<^bsub>G\<^sub>p\<^esub> \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (0::nat) * \<alpha> ^ (0::nat)) 
      = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (0::nat) * \<alpha> ^ (0::nat))" using G\<^sub>p.generator_closed G\<^sub>p.generator G\<^sub>p.l_one by simp 
  ultimately show ?case by argo
next
  case (Suc n)
  have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>Suc n. poly.coeff \<phi> i * \<alpha> ^ i) 
      = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((\<Sum>i\<le>n. poly.coeff \<phi> i * \<alpha> ^ i) 
      + poly.coeff \<phi> (Suc n) * \<alpha> ^ (Suc n))" by force
  also have "\<dots>= \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>n. poly.coeff \<phi> i * \<alpha> ^ i) 
     \<otimes>\<^bsub>G\<^sub>p\<^esub>  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (Suc n) * \<alpha> ^ (Suc n))" 
    using mod_ring_pow_mult_G\<^sub>p by fastforce
  also have "\<dots> = fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc n] \<one>\<^bsub>G\<^sub>p\<^esub>
                \<otimes>\<^bsub>G\<^sub>p\<^esub>  \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> (Suc n) * \<alpha> ^ (Suc n))" 
    using Suc by auto
  also have "\<dots>=fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc (Suc n)] \<one>\<^bsub>G\<^sub>p\<^esub>"
    by simp
  finally show ?case .
qed

text \<open>finally pull the last two lemmas together to show that the public parameters can be used 
to calculate g^\<phi>(\<alpha>) from the public parameters, (\<Prod>PK. \<phi>) = g^\<phi>(\<alpha>).
With lemma g_pow_PK_Prod_to_fold, we form the g_pow_PK_Prod part, which represents (\<Prod>PK. \<phi>), into 
g * g^(\<alpha> ^ 1st coefficient of \<phi>) * g^((\<alpha>^2) ^ 2nd coefficient of \<phi>) * ... * g^((\<alpha>^t) ^ t-th coefficient of \<phi>).
Which we further form into g^(\<Sum>i\<le>n. coeff \<phi> i * \<alpha>^i), which is nothing else then g^\<phi>(\<alpha>) (poly_altdef), 
with the poly_altdef_to_fold lemma\<close>
lemma g_pow_PK_Prod_correct: "degree \<phi> \<le> t 
  \<Longrightarrow> g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<t + 1]) \<phi> 
      = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi> \<alpha>)"
proof -
  let ?g_pow_PK = "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<t + 1]) \<phi>"
  assume asmpt: "degree \<phi> \<le> t"
  have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly \<phi> \<alpha> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<Sum>i\<le>degree \<phi>. poly.coeff \<phi> i * \<alpha> ^ i)"
    by (simp add: poly_altdef)
  moreover have "?g_pow_PK = fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
  proof -
    have "?g_pow_PK = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^pk)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
      using g_pow_PK_Prod_to_fold asmpt by blast
    moreover have "\<forall>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^n)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n) 
              = g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)"
      by (simp add: mod_ring_pow_pow_G\<^sub>p mult.commute G\<^sub>p.int_pow_pow)
    ultimately show "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<t + 1]) \<phi> 
    = fold (\<lambda>n g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> n * \<alpha> ^ n)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"
      by presburger
  qed
  ultimately show "g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<t + 1]) \<phi> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> poly \<phi> \<alpha>" 
    using poly_altdef_to_fold[of "degree \<phi>" \<phi> \<alpha>] by fastforce
qed

subsubsection \<open>The actual theorem\<close>
(* TODO assms*)
text \<open>theorem stating the goal of the subsection: 
that a correct Setup with a correct commit to a polynomial and a correctly computed 
evaluation witness, yields a correct verification of the evaluation.
We use the restriction that a polynomial can only be of degree max_deg, which is according to 
the KZG.\<close>
theorem Eval_Commit_correct:  
  assumes "degree \<phi> \<le> max_deg"
  shows "spmf (Eval_Commit_game \<phi> i) True = 1"
proof -
  let ?\<alpha> = "\<lambda>x. of_int_mod_ring (int x)"
  let ?PK = "\<lambda>x. (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> ?\<alpha> x ^ t) [0..<max_deg+1])"
  have "spmf (Eval_Commit_game \<phi> i) True 
  = spmf ( do{
    (\<alpha>,PK) \<leftarrow> do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    return_spmf (of_int_mod_ring (int x)::'e sk, map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> ((of_int_mod_ring (int x)::'e sk)^t)) [0..<max_deg+1]) 
    };
    let C = Commit PK \<phi>;
    let (i, \<phi>_of_i, w_i) = CreateWitness PK \<phi> i;
    return_spmf (VerifyEval PK C i \<phi>_of_i w_i)
    }) True"
    unfolding Eval_Commit_game_def Setup_def by metis
  also have "\<dots> = spmf ( do {
      x::nat \<leftarrow> sample_uniform (order G\<^sub>p);
      return_spmf
             (e (g_pow_PK_Prod (?PK x) (\<psi>_of \<phi> i))((?PK x)!1 \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) 
              \<otimes>\<^bsub>G\<^sub>T\<^esub> e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>T\<^esub> poly \<phi> i 
                  = e (g_pow_PK_Prod (?PK x) \<phi>) \<^bold>g\<^bsub>G\<^sub>p\<^esub>)})
     True" 
    unfolding Commit_def CreateWitness_def VerifyEval_def
    by (auto simp del: g_pow_PK_Prod.simps)
  also have "\<dots> = spmf ( do {
      x::nat \<leftarrow> sample_uniform (order G\<^sub>p);
      return_spmf
             (e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (\<psi>_of \<phi> i) (?\<alpha> x))) (( \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (?\<alpha> x))  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> (poly \<phi> i )) 
                   = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi> (?\<alpha> x))) \<^bold>g\<^bsub>G\<^sub>p\<^esub>)})
     True"
  proof -
    let ?g_pow_\<phi> = "\<lambda>x. g_pow_PK_Prod (?PK x) \<phi>"
    let ?g_pow_\<psi> = "\<lambda>x. g_pow_PK_Prod (?PK x) (\<psi>_of \<phi> i)"
    let ?g_pow_\<alpha> = "\<lambda>x. (?PK x)!1"
    have g_pow_\<phi>: "?g_pow_\<phi> = (\<lambda>x. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly \<phi> (?\<alpha> x)))"
      using g_pow_PK_Prod_correct[OF assms] by presburger
    have degree_\<psi>: "degree (\<psi>_of \<phi> i) \<le> max_deg" 
      using assms degree_q_le_\<phi> le_trans by blast
    have g_pow_\<psi>: "?g_pow_\<psi> = (\<lambda>x. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (\<psi>_of \<phi> i) (?\<alpha> x)))"
      using g_pow_PK_Prod_correct[OF degree_\<psi>] by presburger
    have g_pow_\<alpha>: "?g_pow_\<alpha> = (\<lambda>x. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (?\<alpha> x))"
      using PK_i d_pos by auto
    show ?thesis using g_pow_\<phi> g_pow_\<psi> g_pow_\<alpha> by metis
    qed
  also have "\<dots>= spmf ( do {
      x::nat \<leftarrow> sample_uniform (order G\<^sub>p);
      return_spmf True}) True" 
    using eq_on_e by presburger
  also have "\<dots> = spmf (scale_spmf (weight_spmf (sample_uniform (order G\<^sub>p))) (return_spmf True)) True" 
    using bind_spmf_const by metis
  also have "\<dots> = 1" by (simp add: G\<^sub>p.order_gt_0)
  finally show ?thesis .
qed

end

end
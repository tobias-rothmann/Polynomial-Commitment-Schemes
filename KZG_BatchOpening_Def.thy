theory KZG_BatchOpening_Def

imports KZG_correct Polynomial_Interpolation.Lagrange_Interpolation Polynomial_Interpolation.Polynomial_Interpolation

begin

section \<open>Batch Opening Definition\<close>

locale KZG_BatchOpening_def = KZG_Def 
begin

text \<open>We define the batched version of the KZG according to the orginal KZG paper [KZG10]:
https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf

The batched version allows to verifiably open a commitment
to a polynomial for up to max_deg points using only one witness. Note, that this batch
version is different from the one mentioned in the Sonic[Mal+19] and Plonk[GWC19]
SNARK, where multiple commitments can be batch opened for one point. The [KZG10]
batched version is an extension of the KZG as defined in chapter 3 for the two
functions CreateWitnessBatch and VerifyEvalBatch, which we define below.\<close>

subsection \<open>polynomial operations and prerequisits\<close>

text \<open>calculate the remainder polynomial of \<phi>/\<Prod>i\<in>B.(x-i) i.e. r = \<phi> mod \<Prod>i\<in>B.(x-i)\<close>
fun r :: "'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow>'e polynomial" where
  "r B \<phi> = do {
  let prod_B = prod (\<lambda>i. [:-i,1:])  B;
  \<phi> mod prod_B}"

lemma deg_r: "degree (r B \<phi>) \<le> degree \<phi>"
  by (smt (verit) add.right_neutral bot_nat_0.not_eq_extremum degree_0 degree_mod_less' div_poly_eq_0_iff less_or_eq_imp_le mod_div_mult_eq mult_eq_0_iff nat_le_linear order_trans_rules(21) r.simps)

text \<open>calculate (\<phi>(x) - r(x))/\<Prod>i\<in>B.(x-i)\<close>
fun \<psi>\<^sub>B :: "'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow> 'e polynomial" where
  "\<psi>\<^sub>B B \<phi> = do {
    let prod_B = prod (\<lambda>i. [:-i,1:])  B;
    (\<phi> - (r B \<phi>)) div prod_B}"

text \<open>\<phi>(x)= (\<phi>(x)/\<Prod>i\<in>B.(x-i)) * \<Prod>i\<in>B.(x-i) + \<phi> mod \<Prod>i\<in>B.(x-i)\<close>
lemma "\<phi> = \<psi>\<^sub>B B \<phi> * (prod (\<lambda>i. [:-i,1:])  B) + r B \<phi>"
  by simp

text \<open>degree of \<Prod>i\<in>B.(x-i) is |B|\<close>
lemma deg_Prod: "degree (\<Prod>i\<in>B. [:- i, 1:]) = card (B::'e eval_position set)"
proof -
  have "finite B \<Longrightarrow> degree (\<Prod>i\<in>B. [:- i, 1:]) = card (B::'e eval_position set)"
  proof (induct B rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert a S)
    have "degree ([:- a, 1:] * (\<Prod>i\<in>S. [:- i, 1:])) = degree ([:- a, 1:]) + degree (\<Prod>i\<in>S. [:- i, 1:])"
      by (rule degree_mult_eq)auto
    then show ?case
      by (metis (no_types, lifting) One_nat_def card.insert degree_pCons_eq_if eq_numeral_extra(2) local.insert(1) local.insert(2) local.insert(3) one_pCons plus_1_eq_Suc prod.insert)
  qed
  then show ?thesis by fastforce
qed

lemma deg_r_B_le: "degree (r B \<phi>) \<le> card B"
  by (metis (no_types, lifting) card_0_eq deg_Prod degree_0 degree_mod_less' less_or_eq_imp_le not_gr0 prod.empty prod.infinite r.simps verit_eq_simplify(24))

lemma deg_r_B_less: "B \<noteq> {} \<Longrightarrow> degree \<phi> > card B \<Longrightarrow> degree (r B \<phi>) < card B"
  by (metis card_eq_0_iff card_gt_0_iff deg_Prod degree_0 degree_mod_less' finite r.simps)

lemma deg_div: "degree ((x::'e polynomial) div y) \<le> degree x"
  by (metis (no_types, lifting) Polynomial.degree_div_less add_diff_cancel_left' bot_nat_0.extremum_strict degree_0 degree_mod_less' degree_mult_right_le diff_zero div_poly_eq_0_iff gr0I less_or_eq_imp_le mod_div_mult_eq)

lemma deg_\<psi>\<^sub>B: "degree (\<psi>\<^sub>B B \<phi>) \<le> degree \<phi>"
  by (simp add: poly_div_diff_left deg_div)

text \<open>e \<in> B implies \<Prod>i\<in>B.(x-i) is 0 at e\<close>
lemma i_in_B_prod_B_zero[simp]: 
  assumes"(i::'e eval_position) \<in> B "
  shows "poly (prod (\<lambda>i. [:-i,1:])  B) i = 0"
proof -
  have i_is_zero: "(\<lambda>x. poly [:-x,1:] i) i = 0" by simp
  have "poly (prod (\<lambda>i. [:-i,1:])  B) i 
      = (prod (\<lambda>x. poly [:-x,1:] i)  B)"
    using poly_prod by fast
  also have "prod (\<lambda>x. poly [:-x,1:] i)  B = 0"
  proof (rule prod_zero)
    show "finite B"
      by simp
    show "\<exists>a\<in>B. poly [:- a, 1:] i = 0"
      using i_is_zero assms by fast
  qed
  finally show "poly (prod (\<lambda>i. [:-i,1:])  B) i = 0" .
qed

text \<open>r(i)=\<phi>(i) for all i \<in> B\<close>
lemma r_eq_\<phi>_on_B:
  assumes "(i::'e eval_position) \<in> B"
  shows "poly (r B \<phi>) i = poly \<phi> i"
proof -
  let ?prod_B = "prod (\<lambda>i. [:-i,1:]) B"
  have "poly \<phi> i = poly (\<phi> div ?prod_B * ?prod_B) i + poly (\<phi> mod ?prod_B) i"
    by (metis div_mult_mod_eq poly_hom.hom_add)
  moreover have "poly (\<phi> div ?prod_B * ?prod_B) i = 0"
    using i_in_B_prod_B_zero[OF assms] by simp
  ultimately have "poly \<phi> i = poly (\<phi> mod ?prod_B) i"
    by fastforce
  then show "poly (r B \<phi>) i = poly \<phi> i"
    by simp
qed

lemma "(\<Prod>i\<in>B. [:- i, 1:]) dvd \<phi> \<Longrightarrow> \<phi> mod (\<Prod>i\<in>B. [:- i, 1:]) = 0 "
  by fastforce  

subsection \<open>Function definitions\<close>

text \<open>We define CreateWitnessBatch according to [KZG10] section 3.4 Batch Opening.
The function reveals all points (i,\<phi>(i)) for i \<in> B using only one witness value. 
It returns (B,r(x),w_i), where B is the provided set of positions, r(x) is a polynomial holding all 
evaluations (i.e. r(i)=\<phi>(i) for all i \<in> B), and w_B is the witness for B and r(x).\<close>
definition CreateWitnessBatch :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> 'e eval_position set
  \<Rightarrow> ('e eval_position set \<times> 'e polynomial \<times> 'a eval_witness)"
where 
  "CreateWitnessBatch PK \<phi> B =( 
    let r = r B \<phi>; \<comment>\<open>remainder of \<phi>(x)/(\<Prod>i\<in>B. (x-i)) i.e. \<phi>(x) mod (\<Prod>i\<in>B. (x-i))\<close>
        \<psi> = \<psi>\<^sub>B B \<phi>; \<comment>\<open>(\<phi>(x) - r(x)) / (\<Prod>i\<in>B. (x-i))\<close>
        w_B = g_pow_PK_Prod PK \<psi> \<comment>\<open>g^\<psi>(\<alpha>)\<close>
    in
    (B, r, w_B) \<comment>\<open>(B, r(x), g^\<psi>(\<alpha>))\<close>
  )" 

text \<open>We define VerifyEvalBatch according to [KZG10] section 3.4 Batch Opening.
The function verifies the witness w_B for a set B, a polynomial r(x), and a commitment C to a 
polynomial \<phi>(x).\<close>
definition VerifyEvalBatch :: "'a pk \<Rightarrow> 'a commit \<Rightarrow> 'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow> 'a eval_witness 
  \<Rightarrow> bool"
where 
  "VerifyEvalBatch PK C B r_x w\<^sub>B = (
    let g_pow_prod_B = g_pow_PK_Prod PK (prod (\<lambda>i. [:-i,1:]) B);
        g_pow_r = g_pow_PK_Prod PK r_x in
    (e g_pow_prod_B w\<^sub>B \<otimes>\<^bsub>G\<^sub>T\<^esub> (e \<^bold>g g_pow_r) = e C \<^bold>g))
    \<comment>\<open>e(g^(\<Prod>i\<in>B. (\<alpha>-i)), g^\<psi>(\<alpha>)) \<otimes> e(g,g^r(\<alpha>)) = e(C, g)\<close>"

end

end
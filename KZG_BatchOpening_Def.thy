theory KZG_BatchOpening_Def

imports KZG_correct

begin

section \<open>Batch Opening Definition\<close>

locale KZG_BatchOpening_def = KZG_Def
begin

(*TODO remove*)
value "degree [:(0::nat), 1:]"
value "poly ([:(-2::int), 1:]) 2"

subsection \<open>polynomial operations and prerequisits\<close>

fun r :: "'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow>'e polynomial" where
  "r B \<phi> = do {
  let prod_B = prod (\<lambda>i. [:-i,1:])  B;
  \<phi> mod prod_B}"

fun \<psi>\<^sub>B :: "'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow> 'e polynomial" where
  "\<psi>\<^sub>B B \<phi> = do {
    let prod_B = prod (\<lambda>i. [:-i,1:])  B;
    (\<phi> - (r B \<phi>)) div prod_B}"


lemma "\<phi> = \<psi>\<^sub>B B \<phi> * (prod (\<lambda>i. [:-i,1:])  B) + r B \<phi>"
  by simp

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

subsection \<open>Function definitions\<close>

definition CreateWitnessBatch :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> 'e eval_position set
  \<Rightarrow> ('e eval_position set \<times> 'e polynomial \<times> 'a eval_witness)"
where 
  "CreateWitnessBatch PK \<phi> B =( 
    let r = r B \<phi>; \<comment>\<open>remainder of \<phi>(x)/(\<Prod>i\<in>B. (x-i)) i.e. \<phi>(x) mod (\<Prod>i\<in>B. (x-i))\<close>
        \<psi> = \<psi>\<^sub>B B \<phi>; \<comment>\<open>(\<phi>(x) - r(x)) / (\<Prod>i\<in>B. (x-i))\<close>
        w_i = g_pow_PK_Prod PK \<psi> \<comment>\<open>g^\<psi>(\<alpha>)\<close>
    in
    (B, r ,w_i) \<comment>\<open>(B, r(x), g^\<psi>(\<alpha>))\<close>
  )" 

definition VerifyEvalBatch :: "'a pk \<Rightarrow> 'a commit \<Rightarrow> 'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow> 'a eval_witness 
  \<Rightarrow> bool"
where 
  "VerifyEvalBatch PK C B r_x w\<^sub>B = (
    let g_pow_prod_B = g_pow_PK_Prod PK (prod (\<lambda>i. [:-i,1:]) B);
        g_pow_r = g_pow_PK_Prod PK r_x in
    (e g_pow_prod_B w\<^sub>B \<otimes>\<^bsub>G\<^sub>T\<^esub> (e \<^bold>g g_pow_r) = e C \<^bold>g) \<and> degree r_x = card B)
    \<comment>\<open>e(g^(\<Prod>i\<in>B. (\<alpha>-i)), g^\<psi>(\<alpha>)) \<otimes> e(g,g^r(\<alpha>)) = e(C, g)\<close>" 

end 

end
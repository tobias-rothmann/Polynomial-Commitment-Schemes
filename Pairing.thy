theory Pairing 

imports  "CryptHOL.CryptHOL" "CryptHOL.Cyclic_Group" Berlekamp_Zassenhaus.Finite_Field
  "Sigma_Commit_Crypto.Cyclic_Group_Ext" "HOL-Number_Theory.Cong"
begin

hide_const Polynomial.order

text\<open> We formalize symmetric parings for cryptography following the textbook:
'A Graduate Course in Applied Cryptography' by Boneh and Shoup
https://toc.cryptobook.us/book.pdf\<close>

locale pairing =
G\<^sub>p : cyclic_group G\<^sub>p + G\<^sub>T : cyclic_group G\<^sub>T 
for G\<^sub>p :: "('a, 'b) cyclic_group_scheme" (structure) 
and G\<^sub>T:: "('c, 'd) cyclic_group_scheme"  (structure) 
+
fixes p::int
  and e
assumes
p_prime : "prime p" and
CARD_G\<^sub>p: "int (order G\<^sub>p) = p" and
CARD_G\<^sub>T: "int (order G\<^sub>T) = p" and
e_symmetric: "e \<in> carrier G\<^sub>p \<rightarrow> carrier G\<^sub>p \<rightarrow> carrier G\<^sub>T" and 
e_bilinearity[simp]: "\<forall>a b::int . \<forall>P Q. P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p \<longrightarrow> 
   e (P [^]\<^bsub>G\<^sub>p\<^esub> a) (Q [^]\<^bsub>G\<^sub>p\<^esub> b) 
= (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (a*b)" and 
e_non_degeneracy[simp]: "\<not>(\<forall>P Q. P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p \<longrightarrow> e P Q = \<one>\<^bsub>G\<^sub>T\<^esub>)"
begin

text \<open>The pairing function e is linear in the first component\<close>
lemma e_linear_in_fst: 
  assumes "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
  shows "e (P [^]\<^bsub>G\<^sub>p\<^esub> (a::int)) Q = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> a"
proof -
  have "e (P [^]\<^bsub>G\<^sub>p\<^esub> a) Q = e (P [^]\<^bsub>G\<^sub>p\<^esub> a) (Q [^]\<^bsub>G\<^sub>p\<^esub> (1::int))" using assms by simp
  also have "... = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (a*(1::int))" using assms e_bilinearity by fast
  also have "\<dots>=(e P Q) [^]\<^bsub>G\<^sub>T\<^esub> a" by simp
  finally show "e (P [^]\<^bsub>G\<^sub>p\<^esub> a) Q = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> a" .
qed

text \<open>The pairing function e is linear in the second component\<close>
lemma e_linear_in_snd: 
  assumes "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
  shows "e P (Q [^]\<^bsub>G\<^sub>p\<^esub> (a::int)) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> a"
proof -
  have "e P (Q  [^]\<^bsub>G\<^sub>p\<^esub> a) = e (P [^]\<^bsub>G\<^sub>p\<^esub> (1::int)) (Q [^]\<^bsub>G\<^sub>p\<^esub> a)" using assms by simp
  also have "... = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> ((1::int)*a)" using assms e_bilinearity by fast
  also have "\<dots>=(e P Q) [^]\<^bsub>G\<^sub>T\<^esub> a" by simp
  finally show "e P (Q [^]\<^bsub>G\<^sub>p\<^esub> a) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> a" .
qed

lemma addition_in_exponents_on_e[simp]: 
  assumes "x \<in> carrier G\<^sub>p \<and> y \<in> carrier G\<^sub>p "
  shows "(e x y) [^]\<^bsub>G\<^sub>T\<^esub> (a::int) \<otimes>\<^bsub>G\<^sub>T\<^esub> (e x y) [^]\<^bsub>G\<^sub>T\<^esub> (b::int) = (e x y) [^]\<^bsub>G\<^sub>T\<^esub> (a+b)"
  by (metis G\<^sub>T.int_pow_mult assms PiE e_symmetric)

text \<open>this follows from non-degeneracy\<close>
lemma e_from_generators_ne_1: "e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<noteq> \<one>\<^bsub>G\<^sub>T\<^esub>"
proof 
  assume asm: "e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> = \<one>\<^bsub>G\<^sub>T\<^esub>"
  have "\<forall>P Q. P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p \<longrightarrow> e P Q = \<one>\<^bsub>G\<^sub>T\<^esub>" 
  proof(intro allI)
    fix P Q
    show "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p \<longrightarrow> e P Q = \<one>\<^bsub>G\<^sub>T\<^esub> "
    proof 
      assume "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
      then obtain p q::int where "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> p = P \<and> \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> q = Q"
        by (metis G\<^sub>p.generatorE int_pow_int)
      then have "e P Q = e (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> p) (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> q)"
        by blast
      also have "\<dots> = e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> (p*q)"
        by force
      also have "\<dots> =  \<one>\<^bsub>G\<^sub>T\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> (p*q)"
        using asm by argo
      also have "\<dots> =  \<one>\<^bsub>G\<^sub>T\<^esub>"
        by fastforce
      finally show "e P Q = \<one>\<^bsub>G\<^sub>T\<^esub>" .
    qed
  qed
  then show "False" using e_non_degeneracy by blast
qed

lemma e_g_g_in_carrier_GT[simp]: "e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<in> carrier G\<^sub>T"
  using e_symmetric by fast

text \<open>mod relations on the exponent (typically useful for cryptographic proofs)\<close>

lemma pow_on_eq_card_GT[simp]: "(\<^bold>g\<^bsub>G\<^sub>T\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> (x::int) = \<^bold>g\<^bsub>G\<^sub>T\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> (y::int)) = ([x= y] (mod p))"
 by (metis (no_types, lifting) CARD_G\<^sub>T G\<^sub>T.finite_carrier G\<^sub>T.gen_power_0 G\<^sub>T.generator_closed G\<^sub>T.int_pow_eq G\<^sub>T.ord_ge_1 G\<^sub>T.ord_le_group_order G\<^sub>T.pow_ord_eq_1 One_nat_def add_diff_inverse_nat arith_extra_simps(6) cong_iff_dvd_diff diff_is_0_eq' less_eq_Suc_le
      zero_order(5))

lemma pow_on_eq_card_GT_carrier_ext'[simp]: 
  "((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>)) [^]\<^bsub>G\<^sub>T\<^esub> x = ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>)) [^]\<^bsub>G\<^sub>T\<^esub> y \<longleftrightarrow> [x= y] (mod p)"
  by (metis CARD_G\<^sub>T G\<^sub>T.finite_carrier G\<^sub>T.int_pow_eq G\<^sub>T.ord_dvd_group_order G\<^sub>T.ord_eq_1 G\<^sub>T.ord_id G\<^sub>T.pow_ord_eq_ord_iff G\<^sub>T.pow_order_eq_1 cong_iff_dvd_diff dvd_antisym e_from_generators_ne_1 e_g_g_in_carrier_GT p_prime prime_imp_coprime prime_nat_int_transfer)

end

end
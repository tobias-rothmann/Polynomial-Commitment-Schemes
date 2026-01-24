theory Primitives

imports Pairing  
begin

text \<open>We define the mathematical primitives used trough out our formalization as well as some 
useful lemmas (mostly identities).\<close>
locale math_primitives = pairing G\<^sub>p  G\<^sub>T p e
  for G\<^sub>p :: "('a, 'b) cyclic_group_scheme" (structure)
  and G\<^sub>T:: "('c, 'd) cyclic_group_scheme"  (structure)
  and p::int
  and e::"'a \<Rightarrow> 'a \<Rightarrow> 'c"
+ 
fixes "type_q" :: "('q :: prime_card) itself"
and max_deg::nat
assumes
p_gr_two: "p > 2" and
d_pos: "max_deg > 0" and
CARD_q: "int (CARD('q)) = p" and
d_l_p: "max_deg < p"
begin

abbreviation pow_mod_ring (infixr "^\<index>" 75)
  where "x ^\<index> y \<equiv>  x [^]\<index> (to_int_mod_ring (y::'q mod_ring))"

abbreviation div_in_grp (infixr "\<div>\<index>" 70)
  where "x \<div>\<index> y \<equiv> x \<otimes>\<index> inv\<index> y"

subsubsection \<open>mod_ring operations on pow of Gp\<close>

lemma carrier_pow_mod_order_G\<^sub>p: 
  assumes "g \<in> carrier G\<^sub>p"
  shows "g [^]\<^bsub>G\<^sub>p\<^esub> x = g [^]\<^bsub>G\<^sub>p\<^esub> (x mod p)"
proof -
  have "p=(order G\<^sub>p)" by (simp add: CARD_G\<^sub>p)
  also have "g [^]\<^bsub>G\<^sub>p\<^esub> x = g [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)"
  proof -
    have "g [^]\<^bsub>G\<^sub>p\<^esub> x \<in> carrier G\<^sub>p" by (simp add: assms)
    let ?d = "x div (order G\<^sub>p)"
    have "g [^]\<^bsub>G\<^sub>p\<^esub> x = g [^]\<^bsub>G\<^sub>p\<^esub> (?d * order G\<^sub>p + x mod order G\<^sub>p)" 
      using div_mult_mod_eq by presburger
    also have "\<dots>= g [^]\<^bsub>G\<^sub>p\<^esub> (?d * order G\<^sub>p) \<otimes>\<^bsub>G\<^sub>p\<^esub>  g [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)"
      using G\<^sub>p.int_pow_mult assms by blast
    also have "\<dots>=\<one>\<^bsub>G\<^sub>p\<^esub> \<otimes>\<^bsub>G\<^sub>p\<^esub> g [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)"
      by (metis G\<^sub>p.int_pow_closed G\<^sub>p.int_pow_pow G\<^sub>p.pow_order_eq_1 assms int_pow_int)
    finally show "g [^]\<^bsub>G\<^sub>p\<^esub> x = g [^]\<^bsub>G\<^sub>p\<^esub> (x mod order G\<^sub>p)"
      using assms by fastforce
  qed
  finally show "g [^]\<^bsub>G\<^sub>p\<^esub> x = g [^]\<^bsub>G\<^sub>p\<^esub> (x mod p)" .
qed

lemma pow_mod_order_G\<^sub>p: "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (x mod p)"
  using carrier_pow_mod_order_G\<^sub>p by blast

lemma mod_ring_pow_mult_inv_G\<^sub>p[symmetric]:" (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>p\<^esub> inv\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
  =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a-b))"
proof -
  have "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>p\<^esub> inv\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
        = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (- to_int_mod_ring b))"
    by (simp add: G\<^sub>p.int_pow_neg)
  also have "\<dots>=(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> ((to_int_mod_ring a + -to_int_mod_ring b) mod CARD ('q)))"
    using pow_mod_order_G\<^sub>p CARD_q G\<^sub>p.generator_closed G\<^sub>p.int_pow_mult by presburger
  also have "\<dots>=(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> ((to_int_mod_ring a - to_int_mod_ring b) mod CARD ('q)))"
    by fastforce
  also have "\<dots>=  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a - b)"
    by (simp add: minus_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  finally show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>p\<^esub> inv\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a - b)" .
qed

lemma mod_ring_pow_mult_G\<^sub>p[symmetric]:" (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
  =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a+b))"
proof -
  have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b =  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a + to_int_mod_ring b)"
    by (simp add: G\<^sub>p.int_pow_mult)
  also have "\<dots>=  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> ((to_int_mod_ring a + to_int_mod_ring b) mod (CARD ('q)))" 
    using pow_mod_order_G\<^sub>p CARD_q by blast
  also have "\<dots>=  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a + b)"
    by (simp add: plus_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  finally show "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a + b)" .
qed

lemma mod_ring_pow_pow_G\<^sub>p[symmetric]: "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (b::'q mod_ring)) 
                       = \<^bold>g\<^bsub>G\<^sub>p\<^esub>[^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a*b::'q mod_ring))"
proof -
  have "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a * to_int_mod_ring b))"
    using G\<^sub>p.int_pow_pow by auto
  also have "\<dots> = (\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> ((to_int_mod_ring a * to_int_mod_ring b) mod CARD ('q)))"
    using CARD_q pow_mod_order_G\<^sub>p by blast
  also have "\<dots>=  \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a * b)"
    by (simp add: times_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  finally show "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring b 
               = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (a * b)" .
qed

lemma to_int_mod_ring_ge_0: "to_int_mod_ring x \<ge> 0" 
  using range_to_int_mod_ring by fastforce

lemma pow_on_eq_card: "(\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> y) = (x=y)"
proof 
  assume assm: "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y"
  then have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring x = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring y"
    using assm by blast
  then have "\<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> nat (to_int_mod_ring x) = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> nat (to_int_mod_ring y)" 
    using to_int_mod_ring_ge_0[of "x"] to_int_mod_ring_ge_0[of "y"] by fastforce
  then have "[nat (to_int_mod_ring x) = nat (to_int_mod_ring y)] (mod order G\<^sub>p)"
    using G\<^sub>p.pow_generator_eq_iff_cong G\<^sub>p.finite_carrier by fast
  then have "[to_int_mod_ring x = to_int_mod_ring y] (mod order G\<^sub>p)" 
    using to_int_mod_ring_ge_0[of "x"] to_int_mod_ring_ge_0[of "y"]
    by (metis cong_int_iff int_nat_eq)
  then have "[to_int_mod_ring x = to_int_mod_ring y] (mod p)" 
    using CARD_G\<^sub>p by fast
  then have "to_int_mod_ring x = to_int_mod_ring y" using range_to_int_mod_ring CARD_q
    by (metis Rep_mod_ring_mod to_int_mod_ring.rep_eq unique_euclidean_semiring_class.cong_def)
  then show "x = y" by force
next 
  assume "x = y"
  then show "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y" by fast
qed

lemma g_pow_to_int_mod_ring_of_int_mod_ring: " \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring x =  \<^bold>g [^] x"
proof -
  have "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring x =  \<^bold>g [^] (x mod p)"
    by (simp add: CARD_q of_int_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  also have "\<dots>= \<^bold>g [^] x" using CARD_G\<^sub>p G\<^sub>p.pow_generator_mod_int by presburger
  finally show ?thesis .
qed

lemma g_pow_to_int_mod_ring_of_int_mod_ring_pow_t: "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> of_int_mod_ring x ^ (t::nat) =  \<^bold>g [^] x ^ t"
  by (metis g_pow_to_int_mod_ring_of_int_mod_ring of_int_of_int_mod_ring of_int_power)

lemma carrier_inj_on_multc: "c \<noteq> 0 \<Longrightarrow> inj_on (\<lambda>x. x ^\<^bsub>G\<^sub>p\<^esub> c) (carrier G\<^sub>p)"
proof 
  fix x y
  assume c: "c \<noteq> 0"
  assume x: " x \<in> carrier G\<^sub>p"
  assume y: " y \<in> carrier G\<^sub>p"
  assume asm: " x ^ c = y ^ c"
  obtain x_pow where x_pow: "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x_pow = x"
    using x 
    by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)
  obtain y_pow where y_pow: "\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y_pow = y"
    using y 
    by (metis G\<^sub>p.generatorE g_pow_to_int_mod_ring_of_int_mod_ring int_pow_int)
  then have "(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> x_pow) ^\<^bsub>G\<^sub>p\<^esub> c = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> y_pow) ^\<^bsub>G\<^sub>p\<^esub> c"
    using asm x_pow y_pow by blast
  then have "(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (x_pow*c))= (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> (y_pow*c))"
    using mod_ring_pow_pow_G\<^sub>p by presburger
  then have "x_pow * c = y_pow*c"
    using pow_on_eq_card by force
  then have "x_pow = y_pow"
    using c by simp
  then show "x=y"
    using x_pow y_pow by blast
qed

subsubsection\<open>mod_ring operations on pow of GT\<close>

lemma pow_mod_order_G\<^sub>T: "g \<in> carrier G\<^sub>T \<Longrightarrow> g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod p)" 
proof -
  assume asmpt: "g \<in> carrier G\<^sub>T"
  have "p=(order G\<^sub>T)" by (simp add: CARD_G\<^sub>T)
  also have "g[^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
  proof -
    have "g [^]\<^bsub>G\<^sub>T\<^esub> x \<in> carrier G\<^sub>T" using asmpt by simp
    let ?d = "x div (order G\<^sub>T)"
    have "g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (?d * order G\<^sub>T + x mod order G\<^sub>T)" 
      using div_mult_mod_eq by presburger
    also have "\<dots>=g [^]\<^bsub>G\<^sub>T\<^esub> (?d * order G\<^sub>T) \<otimes>\<^bsub>G\<^sub>T\<^esub>  g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
      using G\<^sub>T.int_pow_mult asmpt by fast
    also have "\<dots>=\<one>\<^bsub>G\<^sub>T\<^esub> \<otimes>\<^bsub>G\<^sub>T\<^esub> g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
      by (metis G\<^sub>T.int_pow_one G\<^sub>T.int_pow_pow G\<^sub>T.pow_order_eq_1 int_pow_int mult.commute asmpt)
    finally show "g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod order G\<^sub>T)"
      using asmpt by fastforce
  qed
  finally show "g [^]\<^bsub>G\<^sub>T\<^esub> x = g [^]\<^bsub>G\<^sub>T\<^esub> (x mod p)" .
qed


lemma mod_ring_pow_mult_G\<^sub>T[symmetric]:" x \<in> carrier G\<^sub>T \<Longrightarrow> (x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a::'q mod_ring))) \<otimes>\<^bsub>G\<^sub>T\<^esub> (x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring b)) 
  =  x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a+b))"
proof -
  assume asmpt: "x \<in> carrier G\<^sub>T"
  have "x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>T\<^esub> x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring b =  x [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a + to_int_mod_ring b)"
    by (simp add: G\<^sub>T.int_pow_mult asmpt)
  also have "\<dots>=  x [^]\<^bsub>G\<^sub>T\<^esub> ((to_int_mod_ring a + to_int_mod_ring b) mod (CARD ('q)))" 
    using pow_mod_order_G\<^sub>T CARD_q asmpt by blast
  also have "\<dots>=  x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring (a + b)"
    by (simp add: plus_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  finally show "x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring a \<otimes>\<^bsub>G\<^sub>T\<^esub> x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring b = x [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring (a + b)" .
qed

subsubsection \<open>bilinearity operations for mod_ring elements\<close>

lemma e_bilinear[simp]: "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p \<Longrightarrow> 
   e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) (Q [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
= (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a*b))"
proof -
  assume asm: "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
  then have "e (P [^] to_int_mod_ring a) (Q [^] to_int_mod_ring b) = e P Q [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a * to_int_mod_ring b)"
    by simp
   also have "\<dots> = (e P Q [^]\<^bsub>G\<^sub>T\<^esub> ((to_int_mod_ring a * to_int_mod_ring b) mod CARD ('q)))"
     using CARD_q pow_mod_order_G\<^sub>T asm e_symmetric by blast
   also have "\<dots>= e P Q [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring (a * b)"
     by (simp add: times_mod_ring.rep_eq to_int_mod_ring.rep_eq)
   finally  show "e (P [^] to_int_mod_ring a) (Q [^] to_int_mod_ring b) = e P Q [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring (a * b)"
     .
qed

lemma e_linear_in_fst: 
  assumes "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
  shows "e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) (Q) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)"
proof -
  have "e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) Q = e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (1::'q mod_ring))" using assms by simp
  also have "... = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a*(1::'q mod_ring)))" using assms e_bilinear by fast
  also have "\<dots>=(e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" by simp
  finally show "e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a)) Q = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" .
qed

lemma e_linear_in_snd: 
assumes "P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p"
shows "e (P) (Q [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (a::'q mod_ring))) = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)"
proof -
have "e P (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) = e (P [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring (1::'q mod_ring)) (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a)" using assms by simp
  also have "... = (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring ((1::'q mod_ring)*a))" using assms e_bilinear by fast
  also have "\<dots>=(e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring a)" by simp
  finally show "e P (Q [^]\<^bsub>G\<^sub>p\<^esub> to_int_mod_ring a) = e P Q [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring a" .
qed

lemma addition_in_exponents_on_e[simp]: 
  assumes "x \<in> carrier G\<^sub>p \<and> y \<in> carrier G\<^sub>p "
  shows "(e x y) ^\<^bsub>G\<^sub>T\<^esub> a \<otimes>\<^bsub>G\<^sub>T\<^esub> (e x y) ^\<^bsub>G\<^sub>T\<^esub> b = (e x y) ^\<^bsub>G\<^sub>T\<^esub> (a+b)"
  using assms
  by (metis PiE e_symmetric mod_ring_pow_mult_G\<^sub>T)

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

lemma pow_on_eq_card_GT[simp]: "(\<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> x = \<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> y) = (x=y)"
proof
  assume assm: "\<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> x = \<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> y"
  then have "\<^bold>g\<^bsub>G\<^sub>T\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring x = \<^bold>g\<^bsub>G\<^sub>T\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> to_int_mod_ring y"
    using assm by blast
  then have "\<^bold>g\<^bsub>G\<^sub>T\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> nat (to_int_mod_ring x) = \<^bold>g\<^bsub>G\<^sub>T\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> nat (to_int_mod_ring y)" 
    using to_int_mod_ring_ge_0[of "x"] to_int_mod_ring_ge_0[of "y"] by fastforce
  then have "[nat (to_int_mod_ring x) = nat (to_int_mod_ring y)] (mod order G\<^sub>T)"
    using G\<^sub>T.pow_generator_eq_iff_cong G\<^sub>T.finite_carrier by fast
  then have "[to_int_mod_ring x = to_int_mod_ring y] (mod order G\<^sub>T)" 
    using to_int_mod_ring_ge_0[of "x"] to_int_mod_ring_ge_0[of "y"]
    by (metis cong_int_iff int_nat_eq)
  then have "[to_int_mod_ring x = to_int_mod_ring y] (mod p)" 
    using CARD_G\<^sub>T by fast
  then have "to_int_mod_ring x = to_int_mod_ring y" using range_to_int_mod_ring CARD_q
    by (metis arith_simps(49) to_int_mod_ring_add to_int_mod_ring_hom.hom_0_iff
        unique_euclidean_semiring_class.cong_def)
  then show "x = y" by force
next 
  assume "x = y"
  then show "\<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> x = \<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> y" by fast
qed

lemma pow_on_eq_card_GT_carrier_ext'[simp]: 
  "((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>))^\<^bsub>G\<^sub>T\<^esub> x = ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>))^\<^bsub>G\<^sub>T\<^esub> y \<longleftrightarrow> x=y"
proof 
  assume g_pow_x_eq_g_pow_y: "e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> x = e \<^bold>g \<^bold>g ^\<^bsub>G\<^sub>T\<^esub> y"
  obtain g_exp::nat where "e \<^bold>g \<^bold>g = \<^bold>g\<^bsub>G\<^sub>T\<^esub> [^]\<^bsub>G\<^sub>T\<^esub> g_exp"
    using G\<^sub>T.generatorE e_g_g_in_carrier_GT by blast
  then have g_exp: "e \<^bold>g \<^bold>g = \<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> (of_int_mod_ring (int g_exp))"
    by (metis CARD_G\<^sub>T G\<^sub>T.pow_generator_mod_int math_primitives.CARD_q math_primitives_axioms int_pow_int of_int_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  let ?g_exp = "of_int_mod_ring (int g_exp)"
  have "(e \<^bold>g \<^bold>g)^\<^bsub>G\<^sub>T\<^esub> x =  \<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> (of_int_mod_ring (int g_exp) * x)"
    using g_exp
    by (metis CARD_G\<^sub>T G\<^sub>T.generator_closed G\<^sub>T.int_pow_pow G\<^sub>T.pow_generator_mod_int math_primitives.CARD_q math_primitives_axioms times_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  moreover have "(e \<^bold>g \<^bold>g)^\<^bsub>G\<^sub>T\<^esub> y = \<^bold>g\<^bsub>G\<^sub>T\<^esub> ^\<^bsub>G\<^sub>T\<^esub> (of_int_mod_ring (int g_exp) * y)"
    using g_exp
    by (metis CARD_G\<^sub>T G\<^sub>T.generator_closed G\<^sub>T.int_pow_pow G\<^sub>T.pow_generator_mod_int math_primitives.CARD_q math_primitives_axioms times_mod_ring.rep_eq to_int_mod_ring.rep_eq)
  ultimately show "x =y"
    using g_pow_x_eq_g_pow_y pow_on_eq_card_GT e_from_generators_ne_1 g_exp by force
next 
    assume "x = y"
    then show "(e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> x = (e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> y" 
      by blast
  qed

end

end
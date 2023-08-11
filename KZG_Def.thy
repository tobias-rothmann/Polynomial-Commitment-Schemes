theory KZG_Def

imports "CryptHOL.CryptHOL" "CryptHOL.Cyclic_Group" "CRYSTALS-Kyber.Kyber_spec" "Sigma_Commit_Crypto.Commitment_Schemes"
  "Berlekamp_Zassenhaus.Finite_Field_Factorization" "Sigma_Commit_Crypto.Cyclic_Group_Ext" Complex_Main

begin

locale crypto_primitives = 
G\<^sub>p : cyclic_group G\<^sub>p + G\<^sub>T : cyclic_group G\<^sub>T 
for G\<^sub>p  (structure) and G\<^sub>T  (structure) +
fixes "type_a" :: "('q :: qr_spec) itself"
  and d p::int
  and e
and deg_t::nat
assumes
p_gr_two: "p > 2" and
p_prime : "prime p" and
(* Bilinear Group Assumptions *)
CARD_G\<^sub>p: "int (order G\<^sub>p) = p" and
CARD_G\<^sub>T: "int (order G\<^sub>T) = p" and
e_symmetric: "e \<in> carrier G\<^sub>p \<rightarrow> carrier G\<^sub>p \<rightarrow> carrier G\<^sub>T" and 
e_bilinear: "\<forall>a b::'q mod_ring . \<forall>P Q. P \<in> carrier G\<^sub>p \<and> Q \<in> carrier G\<^sub>p \<longrightarrow> 
   e (P [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring a)) (Q [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring b)) 
= (e P Q) [^]\<^bsub>G\<^sub>T\<^esub> (to_int_mod_ring (a*b))" and 
(*$(\mathbb{Z}_p[x])^{<d}$ Assumptions*)
d_pos: "d > 0" and
CARD_q: "int (CARD('q)) = p" and
qr_poly'_eq: "qr_poly' TYPE('q) = Polynomial.monom 1 (nat d) - 1" and
deg_t_le_p: "deg_t \<le> p" 
\<comment>\<open>and t_SDH_GP: "t_SDH GP"\<close>
begin

abbreviation pow_mod_ring_G\<^sub>p :: "'a \<Rightarrow>'q mod_ring \<Rightarrow> 'a" (infixr "^\<^bsub>G\<^sub>p\<^esub>" 75)
  where "x ^\<^bsub>G\<^sub>p\<^esub> q \<equiv> x [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring q)"

end

locale KZG_Def = crypto_primitives
begin

type_synonym 'q' sk = "'q' mod_ring"
type_synonym 'a' pk = "'a' list"
type_synonym 'e' polynomial = "'e' qr"
type_synonym 'a' commit = "'a'"

definition Setup :: "nat \<Rightarrow> ('e sk \<times> 'a pk) spmf"
where 
  "Setup t = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x) in
    return_spmf (\<alpha>, map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<t+1]) 
  }" 

fun g_pow_PK_Prod :: "'a list \<Rightarrow>'e mod_ring poly \<Rightarrow> 'a" where
  "g_pow_PK_Prod PK \<phi> = fold (\<lambda>pk g. g \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!pk ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> pk)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"

definition Commit :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> ('a commit) spmf"
where 
  "Commit PK \<phi> = do {
    return_spmf (g_pow_PK_Prod PK (of_qr \<phi>)) 
  }" 

lemma "set_spmf (Commit PK \<phi>) = {g_pow_PK_Prod PK (of_qr \<phi>)}"
  unfolding Commit_def by force

definition VerifyPoly :: "'a pk \<Rightarrow> 'a commit \<Rightarrow> 'e polynomial \<Rightarrow> bool spmf"
where 
  "VerifyPoly PK C \<phi> = do {
    return_spmf (C = g_pow_PK_Prod PK (of_qr \<phi>)) 
  }" 

subsubsection \<open>extract \<psi> in \<phi> x - \<phi> u = (x-u) * \<psi> x\<close>
text \<open>Idea:
the polynomial \<phi> can be represented as a sum, hence:
\<phi> x - \<phi> u 
= (\<Sum>i\<le>degree \<phi>. coeff \<phi> i * x^i) - (\<Sum>i\<le>degree \<phi>. coeff \<phi> i * x^i)
= (x-u)(\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j)) 
(for the last step see the lemma power_diff_sumr2)
Hence: \<psi> x = (\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j))
However, to build a polynomial \<psi> in Isabelle, we need the individual coefficients for every power 
of x (i.e. bring the sum into a form of (\<Sum>i\<le>degree \<phi>. coeff_i*x^i) where coeff_i is the individual
coefficients for every power i of x. This translation is the main-purpose of the extractor function. 
The key idea is reordering the summation obtained from the power_diff_sumr2 lemma:

One can imagine the summation of power_diff_sumr2 to be horizontal, in the sense that it computes 
the coefficients from 0 to degree \<phi> = n, and adds (or could add) to each coefficient in every iteration:
0: 0 +
1: f1 +
2: f2*u + f2*x +
3: f3*u^2 + f3*u*x + f3*x^2
...
n: fn*u^(n-1) + ... fn*u^((n-1)-i)*x^i ...  + fn*x^(n-1)
we order it to compute the coefficients one by one (to compute vertical)
1: 0 + f1          + ... + fn*u^(n-1)         +
2: 0 + f2 * x      + ... + fn*u^((n-1)-1) * x +
...
n: 0 + fn * x^(n-1)

In formulas:
(\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j)) =
(\<Sum>i\<le>degree \<phi>. (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. coeff \<phi> j * u^(j-Suc i)) * x^i)
\<close>

text \<open>q_coeffs is a accumulator for the fold function.
fold coeffs_n creates a vertical summation by going through the power_diff_sumr2 and instead of 
adding the horizontal row, mapping it into a list, which is added onto the previous list of 
coefficients, hence summing the coefficients vertical in a list. Illustration:

0: [0                     ]  
=> map (+)
1: [f1                    ]
=> map(+)
2: [f1 + f2*u             , f2*x        ] 
=> map(+)
3: [f1 + f2*u + f3*u^2    , f2*x+f3*u*x , f3*x^2]
...
n: [f1 + ... + fn*u^(n-1) , ... , f(i-1)*x^i +...+fn*u^((n-1)-i)*x^i , ... , fn*x^(n-1)]

Hence the resulting list represents the vertical sum with coefficient i at position (i-1).
The correctness proof is to be found in the correctness theory KZG_correct.
\<close>
definition coeffs_n :: "'e mod_ring poly \<Rightarrow> 'e mod_ring \<Rightarrow> 'e mod_ring list \<Rightarrow> nat \<Rightarrow> 'e mod_ring list"
  where "coeffs_n \<phi> u = (\<lambda>q_coeffs. \<lambda>n. map (\<lambda>(i::nat). (nth_default 0 q_coeffs i + poly.coeff \<phi> n * u ^ (n - Suc i))) [0..<n])"

definition \<psi>_of :: "'e qr \<Rightarrow> 'e mod_ring \<Rightarrow> 'e mod_ring poly" 
  where "\<psi>_of \<phi> u = (let 
     \<psi>_coeffs = foldl (coeffs_n (of_qr \<phi>) u) [] [0..<Suc (degree (of_qr \<phi>))]
    in Poly \<psi>_coeffs)"

subsubsection \<open>actual CreateWitness with compute_q: CreateWitness(PK, \<phi>, i) ==> (i, \<phi>(i), g^(\<psi>(\<alpha>)))
 where PK is Setup t \<alpha>\<close>

type_synonym 'e' eval_position = "'e' mod_ring"
type_synonym 'e' eval_value = "'e' mod_ring"
type_synonym 'a' eval_witness = "'a'"

definition CreateWitness :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> 'e eval_position 
  \<Rightarrow> ('e eval_position \<times> 'e eval_value \<times> 'a eval_witness) spmf"
where 
  "CreateWitness PK \<phi> i = do { 
    let \<phi>_of_i = poly (of_qr \<phi>) i;
        \<psi> = \<psi>_of \<phi> i;
        g_pow_\<psi>_of_\<alpha> = g_pow_PK_Prod PK \<psi>
    in
    return_spmf (i, \<phi>_of_i,g_pow_\<psi>_of_\<alpha>) 
  }" 
end

end
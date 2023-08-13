theory KZG_poly_bind

imports KZG_Def "Sigma_Commit_Crypto.Commitment_Schemes" tSDH_assumption
(*maybe*)  "Berlekamp_Zassenhaus.Finite_Field_Factorization" Complex_Main

begin

section \<open>polynomial binding\<close>
text \<open>We show that the KZG is polynomial binding for every polynomial of degree <= deg_t.
We use the Sigma_Commit_Crypto template to prove the binding game.\<close>

locale bind_game_def = KZG_Def
begin

subsection \<open>Function definitions for the binding game, mirroring the KZG poly commit phase\<close>

text \<open>The abstract commitment scheme from Sigma_Commit_Crypto uses 4 functions.\<close>

text\<open>1. The key_gen function, that distributes the key's for prover and verifier. Those keys are in the 
case of the KZG both the same public key (remember the KZG uses a trusted setup.) Hence we copy the 
Setup function from KZG_Def but let it return the the public key for prover and verifier\<close>
definition SCC_key_gen:: "('a pk \<times> 'a pk) spmf" where
  "SCC_key_gen = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x);
    PK = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1] in
    return_spmf (PK, PK)
  }"

text \<open>2. the Commit function, that commits to the plain text (polynomials in the KZG case).
The Sigma_Commit_Crypto Commit function gives the Commitment, just like the KZG defined Commit 
function, and a opening (the polynomial in the KZG case) that was commitment to 
(unlike the KZG's Commit function).
Hence the Commit function from KZG_Def is extended to also return the polynomial that is commited 
to.\<close>
definition SCC_Commit :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> ('a commit \<times> 'e polynomial) spmf"
where 
  "SCC_Commit PK \<phi> = do {
    return_spmf (g_pow_PK_Prod PK (of_qr \<phi>), \<phi>)
  }" 

text \<open>3. the Verify function, that verifies that the commitment was actually made to the plain-text, 
using the opening, which in the KZG case is equivalent to the plain-text. Since the opening is 
cryptographic irrelevant (i.e. binding is evaluated on commitments to plain texts) and equivalent 
to the plain text, it does not hold relevant information and can be neglected.
The function is copied from KZG_Def with erxtended parameter opening. 
Furthermore, it does not return a bool spmf, like in the KZG_Def, but a just a bool. The two 
are still equivalent though as the bool spmf is depended on C and \<phi> either {1} or {0} 
(for spmf _ True).
\<close>
definition SCC_Verify :: "'a pk \<Rightarrow> 'e polynomial \<Rightarrow> 'a commit \<Rightarrow> 'e polynomial \<Rightarrow> bool"
where 
  "SCC_Verify PK \<phi> C _ \<equiv> (C = g_pow_PK_Prod PK (of_qr \<phi>))"

text \<open>4. the valid_msg function, that checks wether a provided plaintext / polynomial is actually 
a valid/allwoed message. For the KZG, a polynomial must be of degree less or equal than the maximum 
degree max_deg. This however is already ensured by the type qr that is a quotient ring over 
polynomials for degree max_deg. Hence the valid_msg function is True\<close>
definition SCC_valid_msg :: "'e polynomial \<Rightarrow> bool"
where 
  "SCC_valid_msg _ \<equiv> True" 

subsubsection \<open>putting together the binding game\<close>
                                                        
sublocale bind_commit: abstract_commitment SCC_key_gen SCC_Commit SCC_Verify SCC_valid_msg .

text \<open>bind_commit.bind_game is the binding game we will reduce to the t-SDH assumption, thus showing 
that cracking the KZG's polynomial binding is at least as hard as solving the t-SDH problem. Hence 
proving the security of the KZG in groups where the t-SDH is difficult. \<close>

subsubsection \<open>Defining a reduction game to t-SDH\<close>

text \<open>Intuetively what we want to show is that if we have an adversary that can compute two 
polynomials such that they have the same commitment in polynomial time, we can construct an 
algorithm, using that adversary, that can solve the t-SDH in polynomial time, thus breaking the 
t-SDH assumption.\<close>

(*TODO finite_field_factorization works only for square-free polys \<rightarrow> add step for non-sf to sf*)
fun find_\<alpha>_square_free :: "'a \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring" where
  "find_\<alpha>_square_free g_pow_\<alpha> \<phi> = (let (c, polys) = finite_field_factorization \<phi>;
    deg1_polys = filter (\<lambda>f. degree f = 1) polys;
    root_list = map (\<lambda>p. poly.coeff p 0) deg1_polys;
    \<alpha>_roots = filter (\<lambda>r. g_pow_\<alpha> = \<^bold>g\<^bsub>G\<^sub>p\<^esub> [^]\<^bsub>G\<^sub>p\<^esub> r) root_list
in \<alpha>_roots!0)"

fun bind_reduction
  :: "('a list, 'e qr, 'a, 'e qr)  bind_adversary \<Rightarrow> 'a t_SDH.adversary"                     
where
  "bind_reduction \<A> PK = do {
  (C, \<phi>, _, \<phi>', _) \<leftarrow> \<A> PK;
  _ :: unit \<leftarrow> assert_spmf(\<phi> \<noteq> \<phi>' \<and> SCC_valid_msg \<phi> \<and> SCC_valid_msg \<phi>');
  let \<alpha> = find_\<alpha>_square_free (PK!1) (of_qr \<phi> - of_qr \<phi>');
  return_spmf (0::nat, \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (1/\<alpha>))}"

end


subsection \<open>proving the bind_game from Sigma_Commit_Crypto\<close>

locale bind_game_proof = bind_game_def
begin 



end


end
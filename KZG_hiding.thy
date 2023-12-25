theory KZG_hiding

imports KZG_correct DL_assumption Cyclic_Group_SPMF_ext

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
  "'a' commit \<Rightarrow> ('e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness) set \<Rightarrow> 
 'e' polynomial spmf"

declare [[show_types]]
definition hiding_game :: "'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf"
  where "hiding_game eval_pos_set \<phi> \<A> = TRY do {
  _ :: unit \<leftarrow> assert_spmf (card eval_pos_set = max_deg);
  PK \<leftarrow> key_gen;
  let C = Commit PK \<phi>;
  let witn_tupel_set = (\<lambda>i. (i, poly \<phi> i, createWitness PK \<phi> i)) ` eval_pos_set;
  \<phi>' \<leftarrow> \<A> C witn_tupel_set;
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"

definition hiding_advantage :: "'e eval_position set \<Rightarrow>  'e polynomial \<Rightarrow> ('a, 'e) adversary \<Rightarrow> real"
  where "hiding_advantage eval_pos_set \<phi> \<A> \<equiv> spmf (hiding_game eval_pos_set \<phi> \<A>) True"

subsection \<open>DL game\<close>

sublocale DL_G\<^sub>p: DL G\<^sub>p "of_int_mod_ring \<circ> int" pow_mod_ring_G\<^sub>p
  unfolding DL_def 
  by (rule G\<^sub>p.cyclic_group_axioms)

subsection \<open>Reduction\<close>

fun reduction
  :: "('a, 'e) adversary \<Rightarrow> ('a,'e) DL.adversary"                     
where
  "reduction \<A> g_pow_\<alpha> = do {
    (\<alpha>::'e sk, PK::'a pk) \<leftarrow> Setup;
     eval_pos_set \<leftarrow> sample_k_uniform max_deg (order G\<^sub>p);
     evals_set \<leftarrow> sample_k_uniform max_deg (order G\<^sub>p);
  _ :: unit \<leftarrow> assert_spmf (\<phi>_of_i \<noteq> \<phi>'_of_i 
                            \<and> valid_msg \<phi>_of_i w_i
                            \<and> valid_msg \<phi>'_of_i w'_i
                            \<and> VerifyEval PK C i \<phi>_of_i w_i 
                            \<and> VerifyEval PK C i \<phi>'_of_i w'_i
                            ); 
  return_spmf (-i::'e mod_ring)}"


end





end 

end
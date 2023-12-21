theory KZG_hiding

imports KZG_correct "DL_assumption"

begin

locale hiding_game_def = KZG_correct
begin

text \<open>Although the binding game will look similar to the Sigma_Commit_Crypto bind_game, 
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
  "'a' commit \<Rightarrow> ('e' eval_position \<times> 'e' eval_value \<times> 'a' eval_witness) list\<Rightarrow> 
 'e' polynomial spmf"

definition hiding_game :: "'e polynomial \<Rightarrow> ('a, 'e) adversary \<Rightarrow> bool spmf"
  where "hiding_game \<phi> \<A> = TRY do {
  PK \<leftarrow> key_gen;
  \<phi>' \<leftarrow> \<A> C ;
  _ :: unit \<leftarrow> assert_spmf (True); 
  return_spmf (\<phi> = \<phi>')} ELSE return_spmf False"

end 

end
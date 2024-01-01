theory KZG_BatchOpening_Def

imports KZG_correct

begin

locale KZG_BatchOpening_def = KZG_Def
begin

value "degree [:(0::nat), 1:]"

thm pseudo_divmod_field

fun r :: "'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow>'e polynomial" where
  "r B \<phi> = do {
  let prod_B = Prod ((\<lambda>i. [:i,1:]) ` B);
  let (_,r) = pseudo_divmod \<phi> prod_B;
  let c = Polynomial.coeff prod_B (degree prod_B) ^ (Suc (degree \<phi>) - degree prod_B);
  smult c r}"

fun \<psi>\<^sub>B :: "'e eval_position set \<Rightarrow> 'e polynomial \<Rightarrow> 'e polynomial" where
  "\<psi>\<^sub>B B \<phi> = do {
    let prod_B = Prod ((\<lambda>i. [:i,1:]) ` B);
    (\<phi> - (r B \<phi>)) div prod_B
    }"

lemma "\<phi> = \<psi>\<^sub>B B \<phi> * (Prod ((\<lambda>i. [:i,1:]) ` B)) + r B \<phi>"
  unfolding \<psi>\<^sub>B.simps r.simps Let_def

end 

end
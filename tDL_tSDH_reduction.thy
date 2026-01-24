theory tDL_tSDH_reduction

imports tDL_assumption tSDH_assumption Algebraic_Group_Model
   "Berlekamp_Zassenhaus.Finite_Field_Factorization" 
   "Elimination_Of_Repeated_Factors.ERF_Algorithm"

begin

locale tDL_to_tSDH_reduction = G : cyclic_group G
  for G:: "('a, 'b) cyclic_group_scheme" (structure) 
  and t::nat  
  and to_type :: "nat \<Rightarrow> ('c::prime_card) mod_ring"
  and exp :: "'a \<Rightarrow> 'c mod_ring \<Rightarrow> 'a"
begin

sublocale tDL: t_DL G t to_type exp ..

sublocale tSDH: t_SDH G t to_type exp ..

interpretation Algebraic_Algorithm G "listS G.groupS" "prodC noConstrain G.groupC" 
  by (unfold_locales) 


type_synonym ('grp,'mr) tSDH_agm_adversary = "'grp list \<Rightarrow> ('mr mod_ring * ('grp * int list)) spmf"

text \<open>The t-SDH game states that given a t+1-long tuple in the form of (g,g^\<alpha>,g^\<alpha>^2,...,g^\<alpha>^t)
the Adversary has to return an element c and g^(1/(c+\<alpha>)).\<close>
definition game :: "('a,'c) tSDH_agm_adversary \<Rightarrow> bool spmf" where 
  "game \<A> = TRY do { 
    \<alpha> \<leftarrow> sample_uniform (Coset.order G);
    (c, (g,gvec)) \<leftarrow> restrict \<A> (map (\<lambda>t'. exp \<^bold>g ((to_type \<alpha>)^t')) [0..<t+1]);
    return_spmf (exp \<^bold>g (1/((to_type \<alpha>)+c)) = g \<and> g \<in> carrier G) 
  } ELSE return_spmf False"

text\<open>Preliminaries\<close>

text \<open>This functions purpose is to extract \<alpha> based on the inputs g^\<alpha> and \<phi>, where \<phi> has a root at \<alpha>. 
The function factorizes \<phi> and filters for all roots. Since \<alpha>'s mod_ring is of the same cardinality 
as g's group's order, we can conclude that if g^r = g^\<alpha> then r=\<alpha>\<close>
fun find_\<alpha>_square_free :: "'a \<Rightarrow> 'c mod_ring poly \<Rightarrow> 'c mod_ring" where
  "find_\<alpha>_square_free g_pow_\<alpha> \<phi> = (let (c, polys) = finite_field_factorization \<phi>;
    deg1_polys = filter (\<lambda>f. degree f = 1) polys;
    root_list = map (\<lambda>p. poly.coeff p 0) deg1_polys;
    \<alpha>_roots = filter (\<lambda>r. g_pow_\<alpha> = exp \<^bold>g (-r)) root_list
in -\<alpha>_roots!0)"

text \<open>The radical is executable via the formalization of the 
'Elimination of Repeated Factors Algorithm' in the AFP 
(see https://www.isa-afp.org/entries/Elimination_Of_Repeated_Factors.html)\<close>
fun find_\<alpha> :: "'a \<Rightarrow> 'c mod_ring poly \<Rightarrow> 'c mod_ring" where
  "find_\<alpha> g_pow_\<alpha> \<phi> = find_\<alpha>_square_free g_pow_\<alpha> (radical \<phi>)"


definition reduction :: "('a,'c) tSDH_agm_adversary \<Rightarrow> ('a,'c) tDL.adversary"
  where "reduction \<A> instc = do {
      (c,(g,gvec)) \<leftarrow> \<A> instc;
      let p = Poly (map of_int_mod_ring gvec);
      return_spmf (find_\<alpha> (instc!1) p)
  }"

end

end
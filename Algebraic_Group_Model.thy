theory Algebraic_Group_Model 
  imports CryptHOL.CryptHOL Restrictive_Comp
  keywords
  "lift_to_algebraicT" :: thy_decl
and  "AGMLifting" :: thy_decl
and "lift_to_algebraic" :: thy_decl
and "lift_to_AGM" :: thy_decl
begin

text \<open>This theory extends CryptHOL for the Algebraic Group Model according to 
Fuchsbauer, Kiltz, and Loss: The Algebraic Group Model and its Applications
https://eprint.iacr.org/2017/620.pdf

Adversaries in CryptHOL are modelled as uninitialized parameters (arbitrary functions), thus we 
cannot ensure that the adversary algorithm itself is algebraic. Instead we enforce the algebraic 
rules on the outputs of the adversary, counting rule breaking as losing the game. Hence, every 
adversary with non-negligible advantage has to be an algebraic algorithm.

We formalize the algebraic rules in the functions 'constrain' and 'constrain_list', which enforce 
the algebraic rules for one/resp. a list of output pair/s.

We provide ML functions to enforce the rules of an algebraic algorithm on specific and
arbitrary algorithms thereby practically lifting adversaries from the standard model to the AGM. 
Finally, we provide the ML function 'lift_to_agm' that takes any game in the standard model and 
automatically derives it's definition in the AGM.
\<close>

(* General methodology: 
select - filters the relevant group elements from the inputs in a generic way so ML can use the 
things
constrain::'b list \<Rightarrow> 'c \<Rightarrow> bool - enforces constrains on a single element 

Built relevant lemmas about lists and prods around this
Built one manual AGM encapsulating do {assert and return} block in Isabelle/HOL
The ML task is to assemble all these from a big game in one call *)
(* TODO implement ML part to infer the part within the control arrows for select and constrain 
e.g. prodC (listC gC) gC from ([g,g^2,g^3], g)*)

locale algebraic_algorithm = cyclic_group 
begin

text \<open>group elements are the single important type we want to select.\<close>
definition groupS :: "('a,'a) restrictive_comp_sel"
  where "groupS \<equiv> \<lparr>select = (\<lambda>x. [x])\<rparr>"

text \<open>atomic types don't harbour group elements\<close>

definition boolS :: "(bool,'a) restrictive_comp_sel"
  where "boolS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

definition unitS :: "(unit,'a) restrictive_comp_sel"
  where "unitS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

definition natS :: "(nat,'a) restrictive_comp_sel"
  where "natS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

definition intS :: "(int,'a) restrictive_comp_sel"
  where "intS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

definition ratS :: "(rat,'a) restrictive_comp_sel"
  where "ratS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

definition realS :: "(real,'a) restrictive_comp_sel"
  where "realS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

definition complexS :: "(complex,'a) restrictive_comp_sel"
  where "complexS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

definition charS :: "(char,'a) restrictive_comp_sel"
  where "charS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

definition stringS :: "(string,'a) restrictive_comp_sel"
  where "stringS \<equiv> \<lparr>select = (\<lambda>x. [])\<rparr>"

text \<open>The above definitions can be composed with the existing data structure extensions from 
Restrictive_Comp and should cover a wide range of possible inputs. In case some case is missing, 
the Restrictive_Comp records can be extended to more data structures (see Restrictive_Comp for 
examples) and this locale can be extended for more atomic type definitions.\<close>


text \<open>check the rules of an algebraic algorithm i.e. given the elements g, a group element, 
and the vector vec=[c_0,...c_n] from the algorithm ensure that g=s_0 [^] c_0 \<otimes> ... \<otimes>
s_0 [^] c_0, where [s_0,...,s_n]=seen are the group values the algorithm was supplied with.
\<close>
definition constrain_grp :: "'a list \<Rightarrow> ('a \<times> int list) \<Rightarrow> bool" 
  where "constrain_grp seen_vec res \<equiv> 
    let (g,c_vec) = res in
    (length seen_vec = length c_vec 
    \<and> g = fold (\<lambda> i acc. acc \<otimes> seen_vec!i [^] (c_vec!i)) [0..<length seen_vec] \<one>)"

definition groupC :: "(('a \<times> int list), 'a) restrictive_comp_con"
  where "groupC \<equiv> \<lparr>constrain = (\<lambda>ip op. constrain_grp ip op)\<rparr>"

text \<open>We don't need to constrain atomic types\<close>

definition constrain_atomic :: "'a list \<Rightarrow> 'b \<Rightarrow> bool" 
  where "constrain_atomic seen_vec res \<equiv> True"

definition boolC :: "(bool, 'a) restrictive_comp_con"
  where "boolC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

definition unitC :: "(unit,'a) restrictive_comp_con"
  where "unitC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

definition natC :: "(nat, 'a) restrictive_comp_con"
  where "natC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

definition intC :: "(int, 'a) restrictive_comp_con"
  where "intC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

definition ratC :: "(rat, 'a) restrictive_comp_con"
  where "ratC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

definition realC :: "(real, 'a) restrictive_comp_con"
  where "realC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

definition complexC :: "(complex, 'a) restrictive_comp_con"
  where "complexC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

definition charC :: "(char, 'a) restrictive_comp_con"
  where "charC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

definition stringC :: "(string, 'a) restrictive_comp_con"
  where "stringC \<equiv> \<lparr>constrain = (\<lambda>ip op. True)\<rparr>"

text \<open>group values that follow the rules of an algebraic algorithm are actually in the group\<close>
lemma constrain_grp_is_in_carrier:
  assumes "\<forall>g \<in> set seen_vec. g \<in> carrier G"
  and "constrain_grp seen_vec (g,c_vec)"
shows "g \<in> carrier G"
proof -
  have "g = fold (\<lambda> i acc. acc \<otimes> seen_vec!i [^] (c_vec!i)) [0..<length seen_vec] \<one>"
    using assms(2) constrain_grp_def by auto
  also have "length seen_vec = length c_vec"
    using assms(2) constrain_grp_def by fastforce
  then have "fold (\<lambda> i acc. acc \<otimes> seen_vec!i [^] (c_vec!i)) [0..<length seen_vec] \<one> \<in> carrier G" 
    using assms(1)
  proof (induct seen_vec c_vec rule: rev_induct2)
    case (4 x xs y ys)
    then have fold_xs_carrier: "fold (\<lambda>i acc. acc \<otimes> xs ! i [^] ys ! i) [0..<length xs] \<one> \<in> carrier G"
      by fastforce
    moreover have "x [^] y \<in> carrier G"
      by (simp add: 4(3))
    moreover have "fold (\<lambda>i acc. acc \<otimes> (xs @ [x]) ! i [^] (ys @ [y]) ! i) [0..<length (xs @ [x])] \<one> 
      =  (fold (\<lambda>i acc. acc \<otimes> xs ! i [^] ys ! i) [0..<length xs] \<one>) \<otimes> x [^] y"
    proof -
      let ?fyys = "\<lambda>xs::'a list. (\<lambda>i acc. acc \<otimes> xs ! i [^] (ys @ [y]) ! i)"
      have "fold (\<lambda>i acc. acc \<otimes> (xs @ [x]) ! i [^] (ys @ [y]) ! i) [0..<length (xs @ [x])] \<one> 
        = fold (?fyys (xs@[x])) [0..<length (xs @ [x])] \<one>" by blast
      moreover have "\<dots> = (fold (?fyys (xs@[x])) [length (xs @ [x]) - 1] \<circ> fold (?fyys (xs@[x])) [0..<length (xs)]) \<one>"
        by auto
      moreover have "\<dots> = ((\<lambda>acc. acc \<otimes> x [^] y)  \<circ> fold (?fyys (xs@[x])) [0..<length (xs)]) \<one>"
        by (smt (verit, del_insts) "4"(2) One_nat_def add_Suc_right append.right_neutral diff_Suc_Suc diff_zero fold.simps(1) fold_Cons id_comp
            length_append list.size(3,4) nth_append_length o_apply)
      moreover have "\<dots> = (fold (?fyys (xs@[x])) [0..<length (xs)] \<one>) \<otimes> x [^] y"
        by force
      moreover have "\<dots> = (fold (\<lambda>i acc. acc \<otimes> xs ! i [^] ys ! i) [0..<length (xs)] \<one>) \<otimes> x [^] y"
      proof - 
        have "fold (?fyys (xs@[x])) [0..<length (xs)] \<one>
          = fold (\<lambda>i acc. acc \<otimes> xs ! i [^] ys ! i) [0..<length xs] \<one>"
        proof(rule fold_cong)
          fix xa
          assume "xa \<in> set [0..<length xs]"
          then have xs_le_xs: "xa < length xs" 
            by force
          then have "(xs @ [x]) ! xa = xs ! xa"
            using nth_append_left by blast
          moreover have "(ys @ [y]) ! xa = ys ! xa"
            using 4(2) nth_append_left xs_le_xs by auto
          ultimately show "(\<lambda>acc. acc \<otimes> (xs @ [x]) ! xa [^] (ys @ [y]) ! xa) = (\<lambda>acc. acc \<otimes> xs ! xa [^] ys ! xa)"
            by presburger
        qed force+
        then show ?thesis by presburger
      qed
      ultimately show ?thesis by argo
    qed
    ultimately show ?case
      by auto
  qed force+
  finally show "g \<in> carrier G" by blast
qed

end 

locale algebraic_algorithm_examples = algebraic_algorithm
begin 

text \<open>To obtain an algebraic algorithm one needs to simply instantiate the restrictive_comp locale 
with the record composition that one needs and apply the non-algebraic algorithm to the obtained 
restrictive_comp.restrict.\<close>

text\<open>The trivial example of only one group element as in and output.\<close>
text \<open>For simplicity let the adversary be id\<close>

definition \<A>_id :: "'a \<Rightarrow> ('a \<times> int list) spmf" 
  where "\<A>_id = (\<lambda>x. return_spmf (x, [1::int]))"

interpretation id: restrictive_comp groupS groupC .

lemma 
  assumes "g \<in> carrier G"
  shows "id.restrict \<A>_id g
    = \<A>_id g"
  unfolding \<A>_id_def restrictive_comp.restrict_def
  unfolding groupS_def groupC_def constrain_grp_def
  by (simp add: assms)
  
text \<open>Now the same for a list of input elements and and output elements\<close>

definition \<A>_list_fst :: "'a list \<Rightarrow> ('a \<times> int list) list spmf" 
  where "\<A>_list_fst = (\<lambda>x. return_spmf (map (\<lambda>_. (x!0, [1::int,0,0])) x))"

interpretation list_id: restrictive_comp "(listS groupS)" "listC groupC" .

lemma 
  assumes "g1 \<in> carrier G \<and> g2 \<in> carrier G \<and> g3 \<in> carrier G"
  shows "list_id.restrict \<A>_list_fst [g1,g2,g3]
    = \<A>_list_fst [g1,g2,g3]"
  unfolding \<A>_list_fst_def restrictive_comp.restrict_def
  unfolding groupS_def groupC_def listS_def listC_def constrain_grp_def
  by (simp add: assms)

end
















context cyclic_group
begin

text \<open>check the rules of an algebraic algorithm i.e. given the elements g, a group element, 
and the vector vec=[c_0,...c_n] from the algorithm ensure that g=s_0 [^] c_0 \<otimes> ... \<otimes>
s_0 [^] c_0, where [s_0,...,s_n]=seen are the group values the algorithm was supplied with.
\<close>
fun constrain :: "'a list \<Rightarrow> 'a \<Rightarrow> (int list) \<Rightarrow> bool"
  where "constrain seen_vec g c_vec = (length seen_vec = length c_vec 
    \<and> g = fold (\<lambda> i acc. acc \<otimes> seen_vec!i [^] (c_vec!i)) [0..<length seen_vec] \<one>)"

text \<open>Given a list of (seen) group elements and vectors from an algebraic algorithm, 
constrain all of them to the rules of algebraic algorithms\<close>
fun constrain_list :: "'a list \<Rightarrow> ('a \<times> int list) list \<Rightarrow> bool"
  where "constrain_list seen xs = list_all (\<lambda>(g, c_vec). constrain seen g c_vec) xs"

text \<open>group values that follow the rules of an algebraic algorithm are actually in the group\<close>
lemma constrain_is_in_carrier:
  assumes "\<forall>g \<in> set seen_vec. g \<in> carrier G"
  and "constrain seen_vec g c_vec"
shows "g \<in> carrier G"
proof -
  have "g = fold (\<lambda> i acc. acc \<otimes> seen_vec!i [^] (c_vec!i)) [0..<length seen_vec] \<one>"
    using assms(2) by simp
  also have "length seen_vec = length c_vec"
    using assms(2) by fastforce
  then have "fold (\<lambda> i acc. acc \<otimes> seen_vec!i [^] (c_vec!i)) [0..<length seen_vec] \<one> \<in> carrier G" 
    using assms(1)
  proof (induct seen_vec c_vec rule: rev_induct2)
    case (4 x xs y ys)
    then have fold_xs_carrier: "fold (\<lambda>i acc. acc \<otimes> xs ! i [^] ys ! i) [0..<length xs] \<one> \<in> carrier G"
      by fastforce
    moreover have "x [^] y \<in> carrier G"
      by (simp add: 4(3))
    moreover have "fold (\<lambda>i acc. acc \<otimes> (xs @ [x]) ! i [^] (ys @ [y]) ! i) [0..<length (xs @ [x])] \<one> 
      =  (fold (\<lambda>i acc. acc \<otimes> xs ! i [^] ys ! i) [0..<length xs] \<one>) \<otimes> x [^] y"
    proof -
      let ?fyys = "\<lambda>xs::'a list. (\<lambda>i acc. acc \<otimes> xs ! i [^] (ys @ [y]) ! i)"
      have "fold (\<lambda>i acc. acc \<otimes> (xs @ [x]) ! i [^] (ys @ [y]) ! i) [0..<length (xs @ [x])] \<one> 
        = fold (?fyys (xs@[x])) [0..<length (xs @ [x])] \<one>" by blast
      moreover have "\<dots> = (fold (?fyys (xs@[x])) [length (xs @ [x]) - 1] \<circ> fold (?fyys (xs@[x])) [0..<length (xs)]) \<one>"
        by auto
      moreover have "\<dots> = ((\<lambda>acc. acc \<otimes> x [^] y)  \<circ> fold (?fyys (xs@[x])) [0..<length (xs)]) \<one>"
        by (smt (verit, del_insts) "4"(2) One_nat_def add_Suc_right append.right_neutral diff_Suc_Suc diff_zero fold.simps(1) fold_Cons id_comp
            length_append list.size(3,4) nth_append_length o_apply)
      moreover have "\<dots> = (fold (?fyys (xs@[x])) [0..<length (xs)] \<one>) \<otimes> x [^] y"
        by force
      moreover have "\<dots> = (fold (\<lambda>i acc. acc \<otimes> xs ! i [^] ys ! i) [0..<length (xs)] \<one>) \<otimes> x [^] y"
      proof - 
        have "fold (?fyys (xs@[x])) [0..<length (xs)] \<one>
          = fold (\<lambda>i acc. acc \<otimes> xs ! i [^] ys ! i) [0..<length xs] \<one>"
        proof(rule fold_cong)
          fix xa
          assume "xa \<in> set [0..<length xs]"
          then have xs_le_xs: "xa < length xs" 
            by force
          then have "(xs @ [x]) ! xa = xs ! xa"
            using nth_append_left by blast
          moreover have "(ys @ [y]) ! xa = ys ! xa"
            using 4(2) nth_append_left xs_le_xs by auto
          ultimately show "(\<lambda>acc. acc \<otimes> (xs @ [x]) ! xa [^] (ys @ [y]) ! xa) = (\<lambda>acc. acc \<otimes> xs ! xa [^] ys ! xa)"
            by presburger
        qed force+
        then show ?thesis by presburger
      qed
      ultimately show ?thesis by argo
    qed
    ultimately show ?case
      by auto
  qed force+
  finally show "g \<in> carrier G" by blast
qed

subsection \<open>Algebraic Algorithm\<close>

text \<open>ML functions that enforce algebraic rules on different objects.

lift_to_algebraicT operates on the type level, lifiting standard model function types into their 
corresponding type as an algebraic algorithm. I.e. extend the outputs that are group elements 
with a vector.

enforce_alg enforces the algebraic rules on a specific probabilistic algorithm. 
Effectively turning any probabilistic algorithm into an algebraic algorithm.
Probabilistic in this case means the algorithm has to return a spmf value. If the algorithm breaks the 
algebraic rules, enforce_alg returns None.

build_alg_fun takes a certain type T and builds a function that takes any probabilistic 
(probabilistic defined as before) algorithm \<A> of that type and returns the algebraic algorithm 
obtained by computing enforce_alg for \<A>.

lift_to_agm takes a game in standard model and turns it into a game in the algebraic group model.
\<close>

ML \<open>
signature ALGEBRAIC_ALGORITHM =
sig 


val lift_to_algebraicT : typ -> typ -> typ -> typ

val extract_type_params : typ -> string list

val enforce_alg: Name.context -> term -> term -> term

val build_alg_fun : Name.context -> term -> typ -> term

val lift_to_agm : theory -> Proof.context -> term -> term -> term list -> term list -> term

end;

structure Algebraic_Algorithm : ALGEBRAIC_ALGORITHM = 
struct

(* Functions relevant for lifting a standard model adversary type to an algebraic adversary type 
i.e lift_to_algebraicT *)

fun rcodomain_transf f (Type ("fun", [T, U])) = (Type ("fun", [T, rcodomain_transf f U]))
  | rcodomain_transf f T = f T;

fun adjoin t vec = fn T => if T = t then Type ("Product_Type.prod", [T, vec]) else T

fun lift_to_algebraicT grpT vec = (rcodomain_transf o Term.map_atyps) (adjoin grpT vec)

(* Functions relevant for enforcing algebraic rules on a concrete (suitable typed) algorithm. I.e. 
lift_to_algebraic *)

fun strip_spmfT T = T 
    |> Term.dest_Type_args 
    |> hd 
    |> Term.dest_Type_args 
    |> hd 

fun return_spmf t = 
  let 
    val T = Term.fastype_of t 
  in 
    \<^Const>\<open>return_pmf \<^Type>\<open>option T\<close> for \<^Const>\<open>Some T for t\<close>\<close>
  end

fun extract_type_params t = Term.add_tfree_namesT t []

fun rapply [] t = t
  | rapply (x::xs) t = rapply xs (t $ x) 

fun rabs [] t = t 
  | rabs (x::xs) t = rabs xs (Term.lambda x t)

fun create_names_prod_cases nctxt  (Type ("Product_Type.prod", [T1, T2])) = 
    let 
      val (T2_res,nctxt') = create_names_prod_cases nctxt T2
      val (T1_res, nctxt'') = create_names_prod_cases nctxt' T1
    in 
      (T1_res@T2_res, nctxt'')
    end
  | create_names_prod_cases nctxt T = 
    let 
      val (name,nctxt') = Name.variant "" nctxt
    in 
      ([Term.Free (name, T)], nctxt') 
    end;

fun extract_vec_pair_list T (Term.Free(t1N,t1T)::Term.Free(t2N,t2T)::xs) 
    = if t1T = T andalso t2T = @{typ "int list"} then
        let 
          val intlistT =  @{typ "int list"} 
          val listT = \<^Type>\<open>Product_Type.prod T intlistT\<close>
          val res = (extract_vec_pair_list T xs)
          val t1 = Term.Free(t1N,t1T)
          val t2 = Term.Free(t2N,t2T)
         in 
          \<^Const>\<open>List.Cons listT for \<^Const>\<open>Pair T intlistT for t1 t2\<close> res\<close>
         end
      else extract_vec_pair_list T xs
    | extract_vec_pair_list T (_::xs) = extract_vec_pair_list T xs
    | extract_vec_pair_list T _ =
      let 
        val intlistT =  @{typ "int list"} 
        val listT = \<^Type>\<open>Product_Type.prod T intlistT\<close>
      in 
         \<^Const>\<open>list.Nil listT\<close>
      end

fun extract_seen_list T (Term.Free(tN,tT)::prams) = 
  let
    val pram = Term.Free(tN,tT)
    val seen = extract_seen_list T prams
  in
    if 
      tT = T
    then 
       \<^Const>\<open>List.Cons T for pram seen\<close>
    else if
      tT = \<^Type>\<open>list T\<close>
    then 
      \<^Const>\<open>append T for pram seen\<close>
    else 
      seen
  end
  | extract_seen_list T _ = \<^Const>\<open>list.Nil T\<close>

fun get_grpTs grp_desc = 
  let 
    fun last_type_arg t = t |> Term.dest_Type_args |> tl |> hd
    val fst_grpT = Term.fastype_of grp_desc |> Term.dest_Type_args |> hd
    val snd_grpT = Term.fastype_of grp_desc |> last_type_arg |> last_type_arg |> last_type_arg
  in 
    (fst_grpT, snd_grpT)
  end

fun constrain_pairs nctxt grp_desc resT prams = 
  let 
    val (grpT1,grpT2) = get_grpTs grp_desc
    val xs = resT 
        |> create_names_prod_cases nctxt 
        |> fst 
        |> extract_vec_pair_list grpT1
    val seen = extract_seen_list grpT1 prams
  in
     \<^Const>\<open>cyclic_group.constrain_list grpT1 grpT2 for grp_desc seen xs\<close>
  end

fun create_assert nctxt grp_desc resT prams = 
  let 
    val _ = writeln (@{make_string} resT);
    val assert_term = constrain_pairs nctxt grp_desc resT prams
  in 
    \<^Const>\<open>SPMF.assert_spmf for assert_term\<close>
  end

fun build_ret_term_rec nctxt (Type ("Product_Type.prod", [T1, T2])) = 
  let 
    val (t2,nctxt') = build_ret_term_rec nctxt T2
    val (t1,nctxt'') = build_ret_term_rec nctxt' T1
  in 
    (\<^Const>\<open>Pair T1 T2 for t1 t2\<close>, nctxt'')
  end 
  | build_ret_term_rec nctxt T = 
  let 
    val (name,nctxt') = Name.variant "" nctxt
  in 
    (Term.Free (name, T), nctxt') 
  end;

fun build_ret_term nctxt T = 
   build_ret_term_rec nctxt T |> fst |> return_spmf

fun abs_typ_over_term_rec (Type ("Product_Type.prod", [T1, T2])) (t,nctxt) = 
  let 
    val restT = t |> Term.fastype_of
    val (rest,nctxt') = abs_typ_over_term_rec T2 (t,nctxt) |> abs_typ_over_term_rec T1
  in
     (\<^Const>\<open>Product_Type.prod.case_prod T1 T2 restT\<close> $ rest, nctxt') (*abs T1 (abs T2)*)
  end
  | abs_typ_over_term_rec T (t,nctxt) = 
  let 
    val (name,nctxt') = Name.variant "" nctxt
  in 
    (Term.absfree (name, T) t, nctxt') 
  end;

fun abs_typ_over_term nctxt T t = abs_typ_over_term_rec T (t,nctxt) |> fst

fun extract_params nctxt T = 
  let 
    val (pramsT, _) = Term.strip_type T;
    val (pNames,nctxt') = Name.invent' "" (length pramsT) nctxt;
    val prams = map (fn (n,T) => Term.Free (n, T)) (pNames ~~ pramsT)
  in 
    (prams, nctxt') 
  end

fun supply_prams t prams = rapply prams t

fun build_assert_fun nctxt grp_desc retT prams t = 
  let 
    val unitT = @{typ unit}
    val assert_term = create_assert nctxt grp_desc retT prams
    val t' = Term.absdummy unitT t
  in
   \<^Const>\<open>bind_spmf unitT retT for assert_term t'\<close>
  end

fun build_body_fun nctxt grp_desc T prams = 
  build_ret_term nctxt T |> build_assert_fun nctxt grp_desc T prams |> abs_typ_over_term nctxt T

fun enforce_alg nctxt grp_desc t = 
  let 
    val (prams,nctxt') = Term.fastype_of t |> extract_params nctxt
    val spmf = supply_prams t prams
    val retT = Term.fastype_of spmf |> strip_spmfT
    val body_term = build_body_fun nctxt' grp_desc retT prams
    val fun_term = \<^Const>\<open>bind_spmf retT retT for spmf body_term\<close>
  in 
    rabs (rev prams) fun_term
  end

(* function that enforces algebraic rules for an arbitrary (suitably typed) algorithm *)

fun build_alg_fun nctxt grp_desc T = 
  let
    (* create params to abstract over*)
    val (prams,nctxt') = extract_params nctxt T
    (* instantiate the adversary*)
    val (advN, _) = Name.variant "\<A>" nctxt'
    val adv = Term.Free(advN,T)
    (* create the fun term to enforce the agm for the adversary *)
    val fun_term = enforce_alg nctxt grp_desc adv
  in 
    Term.lambda adv fun_term
  end

(* functions relevant for turning a standard model game in a game in the AGM i.e. lift_to_agm *)

fun get_def_thm thy def = 
    let 
      val def_stripped = Term.head_of def
      val name = (Term.dest_Const_name def_stripped) ^ "_def_raw"
      val def_thm = Thm.axiom thy name
    in
      def_thm
    end

fun get_def_thm_rhs thy def = 
    let 
      val def_thm = get_def_thm thy def
      val def_content = Thm.concl_of def_thm
      val rhs = def_content |> Logic.dest_equals |> snd
    in
      rhs
    end

fun get_def_thm_lhs thy def = 
    let 
      val def_thm = get_def_thm thy def
      val def_content = Thm.concl_of def_thm
      val lhs = def_content |> Logic.dest_equals |> fst
    in
      lhs
    end

exception MATCH;

(* t1 is the term do be matched on a subterm of t2 *)
fun match_subterms ctxt t1 t2 = 
   let
    fun ex t2 = 
    Thm.match (Thm.cterm_of ctxt t1,Thm.cterm_of ctxt t2)
    handle Pattern.MATCH => 
      (case t2 of
        t $ u => (ex t handle Pattern.MATCH => ex u)
      | Abs (_, _, t) => ex t
      | _ => raise MATCH);
  in ex t2 end;

fun unfold_def thy ctxt def = 
  let 
    val thm_lhs = get_def_thm_lhs thy def 
    val raw_game_cterm = get_def_thm_rhs thy def |> Thm.cterm_of ctxt
    val tables = match_subterms ctxt thm_lhs def
    val game_cterm = Thm.instantiate_beta_cterm tables raw_game_cterm
    val game = Thm.term_of game_cterm
  in
    game
  end

(* deconstructs term combination until a subterm in t2 matches t1 *)
fun match_combs ctxt t1 t2 =
    let
        fun match_helper t2 =
            (Thm.match (Thm.cterm_of ctxt t1, Thm.cterm_of ctxt t2);
             [])
            handle Pattern.MATCH =>
                (case t2 of
                    t $ u => u :: match_helper t
                  | Abs (_, _, t) => match_helper t
                  | _ => [])
    in
       match_helper t2 |> rev
    end;

fun get_combs thy ctxt def =
  let 
    val thm_lhs = get_def_thm_lhs thy def 
    val tables = match_subterms ctxt thm_lhs def
    val thm_lhs_cterm = Thm.cterm_of ctxt thm_lhs
    val lhs = Thm.instantiate_beta_cterm tables thm_lhs_cterm
    val combs = match_combs ctxt (Thm.term_of lhs) def
  in
    combs
  end

fun agm_combs (c::combs) (adv::advs) (agm::agm_advs) (extr::extrs) = 
  if c=adv 
  then agm::agm_combs combs advs agm_advs (extr::extrs)
  else if c=extr
       then extr::agm_combs combs (adv::advs) (agm::agm_advs) extrs 
       else agm_combs combs (adv::advs) (agm::agm_advs) (extr::extrs)
  | agm_combs (c::combs) (adv::advs) (agm::agm_advs) extrs =  
  if c=adv 
  then agm::agm_combs combs advs agm_advs extrs
  else agm_combs combs (adv::advs) (agm::agm_advs) extrs
  | agm_combs (c::combs) advs agm_advs (extr::extrs) = 
  if c=extr 
  then extr::agm_combs combs advs agm_advs extrs 
  else agm_combs combs advs agm_advs (extr::extrs)
  | agm_combs combs _ _ _ = combs
  
exception ADV_PARAM;

(* combs with the adversary lifted type to an algebraic algorithm *)
fun lift_to_agmT ctxt grp_desc combs advs extrs = 
  let 
    val nctxt = Variable.names_of ctxt
    val grpT = Term.fastype_of grp_desc |> Term.dest_Type_args |> hd;
    val vecT = @{typ "int list"}
    val agm_advs = map (fn (Term.Free(name,T)) => (Term.Free(name, lift_to_algebraicT grpT vecT T)) | _ => raise ADV_PARAM) advs
    val combs' = agm_combs combs advs agm_advs extrs
  in 
    combs'
  end

exception AGMTYPE1;
exception AGMTYPE2 of typ*(string*typ);

fun repair_agmT_abs nctxt (\<^Type>\<open>Product_Type.prod T1 T2\<close>) (Const ("Product_Type.prod.case_prod", T3) $ t) T2list
  = let 
      val (fixed_t, nctxt', agm_vars) = repair_agmT_abs nctxt T1 t (T2::T2list)
      val retT = Term.body_type T3
    in 
       (\<^Const>\<open>Product_Type.prod.case_prod T1 T2 retT\<close> $ fixed_t, nctxt', agm_vars)
    end
  | repair_agmT_abs nctxt (\<^Type>\<open>Product_Type.prod T1 T2\<close>) (Abs(aN,aT,t)) T2list = 
      if T1 = aT andalso T2 = @{typ "int list"} then 
        let 
          val (vecN,nctxt') = Name.variant (aN ^ "vec") nctxt 
          val (fixed_t, nctxt'', agm_vars) = case T2list of (T2::T2tl) => repair_agmT_abs nctxt' T2 t T2tl
          | [] => (t,nctxt, [])
          val retT = Term.fastype_of t
          val vec = Free (vecN,T2)
          val agm_var = (Free(aN,aT), vec)
          val abs_vec = fixed_t |> Term.incr_boundvars 1 |> Term.lambda vec
        in
          (\<^Const>\<open>Product_Type.prod.case_prod T1 T2 retT\<close> $ Abs(aN, aT, abs_vec), nctxt'', agm_var::agm_vars)
        end
      else raise AGMTYPE1
  | repair_agmT_abs nctxt T1 (Abs(varN, varT, t)) (T2::T2list) =
    if T1 <> varT then 
      raise AGMTYPE2(T1, (varN,varT))
    else 
      let 
        val (fixed_t, nctxt', agm_vars) = repair_agmT_abs nctxt T2 t T2list
      in
        (Abs(varN, varT, fixed_t), nctxt',agm_vars)
      end
  | repair_agmT_abs nctxt _ t  _ = (t,nctxt,[])
  

fun repair_agm_abs nctxt spmf abs = 
  let 
    val spmfT = Term.head_of spmf |> Term.fastype_of |> Term.body_type |> strip_spmfT
  in
    repair_agmT_abs nctxt spmfT abs []
  end

fun repair_agm_abss grpT nctxt t advs = 
  case t of 
    Const("SPMF.bind_spmf",bindT) $ spmf $ abs => 
    let 
      val (fixed_abs,nctxt', agm_vars) = repair_agm_abss grpT nctxt abs advs
    in 
      if List.exists (fn a => Term.head_of spmf = a) advs then 
        let 
          val (fix,nctxt'', agm_vars') = repair_agm_abs nctxt' spmf fixed_abs
          val bindT_fix = Term.map_atyps (adjoin grpT @{typ "int list"}) bindT
        in 
          (Const("SPMF.bind_spmf",bindT_fix) $ spmf $ fix, nctxt'', agm_vars' @ agm_vars) 
        end
        else (Const("SPMF.bind_spmf",bindT) $ spmf $ fixed_abs, nctxt', agm_vars) 
    end
  | Abs(aT,aN,t) => 
    let 
      val (fixed_t, nctxt', agm_vars) = repair_agm_abss grpT nctxt t advs
    in 
      (Abs(aT,aN,fixed_t),nctxt', agm_vars)
    end
   | t1 $ t2 => 
      let 
        val (fixed_t1,nctxt', agm_vars) = repair_agm_abss grpT nctxt t1 advs;
        val (fixed_t2,nctxt'', agm_vars') = repair_agm_abss grpT nctxt' t2 advs;
      in 
        ((fixed_t1 $ fixed_t2), nctxt'', agm_vars @ agm_vars')
      end
    | t => (t,nctxt,[])

exception EXTR_FREE_VAR;

fun lift_extr_to_agm extrs agm_vars (Abs(aN,aT,t)) = 
  let 
    val (pram,inst) = Term.dest_abs_global (Abs(aN,aT,t))
    val res = lift_extr_to_agm extrs agm_vars inst
    val rest = fst res
    val extrs' = snd res
    val var = Free(pram)
  in 
    (Term.lambda var rest, extrs')
  end
  | lift_extr_to_agm extrs agm_vars t = 
  let
    val (f,combs) = Term.strip_comb t
    val extr = List.find (fn e => Term.head_of f = e) extrs
  in
    case extr of SOME extr => 
    let 
      val combs' = map (fn c => 
        case List.find (fn (a,_) =>  a = c) agm_vars of SOME (a,avec) => 
        let 
          val aT = Term.fastype_of a
          val avecT = Term.fastype_of avec
        in
          \<^Const>\<open>Product_Type.Pair aT avecT for a avec\<close> 
        end
        | NONE => c) combs
      val f' = case extr of Free (fN, fT) => Free(fN, (map Term.fastype_of combs') ---> Term.body_type fT)
        | _ => raise EXTR_FREE_VAR
    in
      (Term.list_comb (f', combs'), [f'])
    end
    | NONE => 
    let 
      val res = map (lift_extr_to_agm extrs agm_vars) combs
      val combs' = map fst res
      val extrs' = List.concat (map snd res)
    in
      (Term.list_comb (f,combs'), extrs')
    end
  end


exception ADV_FREE_VAR;

fun insert_agm_constraints nctxt grp_desc advs (Free(fN,fT)) = 
  if List.exists (fn Free(aN,_) => aN = fN | _ => raise ADV_FREE_VAR) advs then
     enforce_alg nctxt grp_desc (Free(fN,fT))
  else Free(fN,fT)
  | insert_agm_constraints nctxt grp_desc advs (Abs(aN,aT,t)) = 
    (Abs(aN,aT,insert_agm_constraints nctxt grp_desc advs t))
  | insert_agm_constraints nctxt grp_desc advs (t1 $ t2) = 
   insert_agm_constraints nctxt grp_desc advs t1 $ (insert_agm_constraints nctxt grp_desc advs t2)
  | insert_agm_constraints _ _ _ t = t


fun lift_to_agm thy ctxt grp_desc def advs extrs = 
  let 
    val nctxt = Variable.names_of ctxt
    val game = unfold_def thy ctxt def
    val combs = get_combs thy ctxt def
    val combs' = lift_to_agmT ctxt grp_desc combs advs extrs
    val grpT = Term.fastype_of grp_desc |> Term.dest_Type_args |> hd;
    val vecT = @{typ "int list"}
    val agm_advs = map (fn (Term.Free(name,T)) => (Term.Free(name, lift_to_algebraicT grpT vecT T)) | _ => raise ADV_PARAM) advs
    val game' = Term.betapplys (game,combs')
    val (game'',_,agm_vars) = repair_agm_abss grpT nctxt game' agm_advs
    val (game''', extrs') = lift_extr_to_agm extrs agm_vars game''
    val combs'' = map (fn Free(combN,combT) => 
      (case List.find (fn Free(eN,eT) => eN = combN | _ => raise ADV_FREE_VAR) extrs' 
        of SOME e => e 
        | NONE => Free(combN,combT)) 
      | _ => raise ADV_FREE_VAR) combs'
    val game'''' = insert_agm_constraints nctxt grp_desc advs game'''
    val agm_game = fold (fn comb => fn game => Term.lambda comb game) (rev combs'') game''''
    val agm_cterm = Thm.cterm_of ctxt agm_game
  in
    agm_game
  end

end;
\<close>

text \<open>This takes any algorithm/function type and lifts it to the algebraic algorithm equivalent type.
For examples take a look at the end of this file.\<close>
ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>lift_to_algebraicT\<close> "lift to algebraic type"
    (Parse.typ -- (Parse.term -- (\<^keyword>\<open>=>\<close> |--Parse.binding)) >> 
      (fn (alg,(grp,b)) => fn lthy => Local_Theory.raw_theory (fn thy =>
      let
        val algT = Syntax.read_typ lthy alg;
        val grp_desc = Syntax.read_term lthy grp;
        val grpT = Term.fastype_of grp_desc |> Term.dest_Type_args |> hd;
        val agmT = Algebraic_Algorithm.lift_to_algebraicT grpT @{typ "int list"} algT;
        val tps = Algebraic_Algorithm.extract_type_params agmT;
        val thy' = Sign.add_type_abbrev lthy (b, tps, agmT) thy
      in thy' end) lthy));
\<close>

text \<open>This takes any algorithm/function and enforces the rules of an algebraic algorithm on all 
suitable output pairs (g,gvec).
For examples take a look at the end of this file.\<close>
ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>lift_to_algebraic\<close> "lift to algebraic type"
    (Parse.term -- (Parse.term -- (\<^keyword>\<open>=>\<close> |--Parse.binding)) >> 
      (fn (a,(grp,b)) => fn lthy => 
      let
        val nctxt = Variable.names_of lthy
        val alg = Syntax.read_term lthy a;
        val grp_desc = Syntax.read_term lthy grp;
        val agm_term = Algebraic_Algorithm.enforce_alg nctxt grp_desc alg;
        val (def, thy') = Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), agm_term)) lthy;
      in thy' end));
\<close>

text \<open>This takes any function/algorithm type T and computes a function that enforces the algebraic 
algorithm rules on concrete algorithms of the algebraic algorithm equivalent type of T. To be used 
to turn adversaries from the standard model into the algebraic group model.
For examples take a look at the end of this file.\<close>
ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>AGMLifting\<close> "lift to algebraic type"
    (Parse.typ -- (Parse.term -- (\<^keyword>\<open>=>\<close> |--Parse.binding)) >> 
      (fn (adv,(grp,b)) => fn lthy =>
      let
        val nctxt = Variable.names_of lthy
        val advT = Syntax.read_typ lthy adv;
        val grp_desc = Syntax.read_term lthy grp;
        val grpT = Term.fastype_of grp_desc |> Term.dest_Type_args |> hd;
        val agm_advT = Algebraic_Algorithm.lift_to_algebraicT grpT @{typ "int list"} advT;
        val agm_term = Algebraic_Algorithm.build_alg_fun nctxt grp_desc agm_advT;
        val (def, thy') = Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), agm_term)) lthy;
      in thy' end));
\<close>

text \<open>This takes a game in the standard model and lifts it into the AGM.
Syntax: Group game | adversaries | extra(ctors) = *new_game_name*
The game should be supplied with free variable parameters. A subset of these parameters will be the 
adversaries, which may be explicitly lifted into the AGM by listing them in the "adversaries" 
section, separated by commas - the same applies to the extra(ctors) (typically extractors), which 
are algorithms that should also receive the AGM vector for values from a adversary. 
For an Example take a look at KZG_knowledge_soundness.thy\<close>
ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>lift_to_AGM\<close> "lift game to Algeraic Group Model"
    (Parse.term -- (Parse.term -- (\<^keyword>\<open>|\<close> |-- ((Parse.enum "," Parse.term ) -- 
      (\<^keyword>\<open>|\<close> |-- ((Parse.enum "," Parse.term ) -- (\<^keyword>\<open>=\<close> |-- Parse.binding)))))) >> 
      (fn (grp,(game_name,(advl, (extrl,b)))) => fn lthy => 
      let
        val thy = Proof_Context.theory_of lthy;
        val game_ref = Syntax.read_term lthy game_name;
        val advs = Syntax.read_terms lthy advl;
        val extrs = Syntax.read_terms lthy extrl;
        val grp_desc = Syntax.read_term lthy grp;
        val agm_term = Algebraic_Algorithm.lift_to_agm thy lthy grp_desc game_ref advs extrs;
        val (def, lthy') = Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), agm_term)) lthy;
      in lthy' end));
\<close>

subsection \<open>Examples\<close>

text\<open>Example to enforce the algebraic rules on an arbitrary adversary.\<close>

type_synonym ('a')adv = "'a' list \<Rightarrow> 'a' \<Rightarrow> nat \<Rightarrow> ('a' * int * nat) spmf"

declare [[show_types]]
AGMLifting  "('a) adv" "G" => agm_adv
thm agm_adv_def

lift_to_algebraicT "('a)adv" G => agm_advT

ML \<open>
val agm_adv_typ = @{typ "('a)agm_advT"}
\<close>

lemma "agm_adv \<equiv> \<lambda>(A::('a)agm_advT) a b c. do { 
      ((g,gvec),e,d) \<leftarrow> A a b c;
      _::unit \<leftarrow> assert_spmf((length (a @ [b]) = length gvec 
        \<and> g = fold (\<lambda> i acc. acc \<otimes> (a @ [b])!i [^] (gvec!i)) [0..<length (a @ [b])] \<one>));
      return_spmf ((g,gvec),e,d) 
    }"
  unfolding agm_adv_def by fastforce

text \<open>Example to enforce algebraic rules on the outputs of a specific adversary of correct type\<close>

definition \<A>::"('a) agm_advT"
  where "\<A> a b c = return_spmf((\<one>,[0,0]),-1,1)"

lift_to_algebraic \<A> G => \<A>_algebraic
thm \<A>_algebraic_def

lemma 
  "\<A>_algebraic \<equiv> \<lambda>a b c. do { 
      ((g,gvec),e,d) \<leftarrow> \<A> a b c;
      _::unit \<leftarrow> assert_spmf((length (a @ [b]) = length gvec 
        \<and> g = fold (\<lambda> i acc. acc \<otimes> (a @ [b])!i [^] (gvec!i)) [0..<length (a @ [b])] \<one>));
      return_spmf ((g,gvec),e,d) 
    }"
  unfolding \<A>_algebraic_def by fastforce

text \<open>For an example to lift a game into the AGM take a look at KZG_knowledge_soundness.thy\<close>

end

end
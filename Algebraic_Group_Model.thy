theory Algebraic_Group_Model 
  imports CryptHOL.CryptHOL
  keywords
  "lift_to_agmT" :: thy_decl
and  "AGMLifting" :: thy_decl
and "lift_to_agm" :: thy_decl
begin

text \<open>This theory captures the definition of an algebraic algorithm according to 
Fuchsbauer, Kiltz, and Loss: The Algebraic Group Model and its Applications
https://eprint.iacr.org/2017/620.pdf

(* Erwähne functions *)

We provide dynamic ML functions to enforce the rules of an algebraic algorithm on 
arbitrary algorithms thereby practically lifting adversaries from the standard model 
to the algebraic group model.
\<close>

context cyclic_group
begin 

text \<open>check the rules of an algebraic algorithm i.e. given the elements g, agroup element, 
and the vector vec_c=[c_0,...c_n] from the algorithm ensure that g=s_0 [^] c_0 \<otimes> ... \<otimes>
s_0 [^] c_0, where [s_0,...,s_n]=seen are the group values the algorithm was supplied with.
\<close>
fun constrain :: "'a list \<Rightarrow> 'a \<Rightarrow> (int list) \<Rightarrow> bool"
  where "constrain seen_vec g c_vec = (length seen_vec = length c_vec 
    \<and> g = fold (\<lambda> i acc. acc \<otimes> seen_vec!i [^] (c_vec!i)) [0..<length seen_vec] \<one>)"

text \<open>Given a list of group elements and vectors from an algebraic algorithm, 
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

ML \<open>
signature ALGEBRAIC_ALGORITHM =
sig 

val lift_to_algebraicT : typ -> typ -> typ -> typ

val extract_type_params : typ -> string list

val enforce_alg: Name.context -> term -> term -> term

val build_alg_fun : Name.context -> term -> typ -> term

end;

structure Algebraic_Algorithm (*TODO uncomment : ALGEBRAIC_ALGORITHM*) = 
struct

fun rcodomain_transf f (Type ("fun", [T, U])) = (Type ("fun", [T, rcodomain_transf f U]))
  | rcodomain_transf f T = f T;

fun adjoin t vec = fn T => if T = t then Type ("Product_Type.prod", [T, vec]) else T

fun lift_to_algebraicT grpT vec = (rcodomain_transf o Term.map_atyps) (adjoin grpT vec)

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

end;
\<close>

text \<open>This takes any algorithm/function type and lifts it to the algebraic algorithm equivalent type.
For examples take a look at the end of this file.\<close>
ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>lift_to_agmT\<close> "lift to algebraic type"
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
  Outer_Syntax.local_theory \<^command_keyword>\<open>lift_to_agm\<close> "lift to algebraic type"
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

subsection \<open>Examples\<close>

text\<open>Example to enforce the algebraic rules on an arbitrary adversary.\<close>

type_synonym ('a')adv = "'a' list \<Rightarrow> 'a' \<Rightarrow> nat \<Rightarrow> ('a' * int * nat) spmf"

declare [[show_types]]
AGMLifting  "('a) adv" "G" => agm_adv
thm agm_adv_def

lift_to_agmT "('a)adv" G => agm_advT

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

lift_to_agm \<A> G => \<A>_algebraic
thm \<A>_algebraic_def

lemma 
  "\<A>_algebraic \<equiv> \<lambda>a b c. do { 
      ((g,gvec),e,d) \<leftarrow>  \<A> a b c;
      _::unit \<leftarrow> assert_spmf((length (a @ [b]) = length gvec 
        \<and> g = fold (\<lambda> i acc. acc \<otimes> (a @ [b])!i [^] (gvec!i)) [0..<length (a @ [b])] \<one>));
      return_spmf ((g,gvec),e,d) 
    }"
  unfolding \<A>_algebraic_def by fastforce

end

end
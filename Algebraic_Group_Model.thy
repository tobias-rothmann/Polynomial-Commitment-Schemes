theory Algebraic_Group_Model 
  imports CryptHOL.CryptHOL
  keywords
  "lift_to_algebraicT" :: thy_decl
and  "AGMLifting" :: thy_decl
and "lift_to_algebraic" :: thy_decl
and "lift_to_AGM" :: thy_decl 
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

text \<open>check the rules of an algebraic algorithm i.e. given the elements g, a group element, 
and the vector vec=[c_0,...c_n] from the algorithm ensure that g=s_0 [^] c_0 \<otimes> ... \<otimes>
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
      val name = (Term.dest_Const_name def_stripped) ^ "_def_raw" (*TODO  exception if not found?*)
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

(* TODO unify *)
exception AGMTYPE1;
exception AGMTYPE2 of typ*(string*typ);

fun repair_agmT_abs nctxt (\<^Type>\<open>Product_Type.prod T1 T2\<close>) (Const ("Product_Type.prod.case_prod", T3) $ t) T2list
  = let 
      val retT = Term.body_type T3
      val (fixed_t, nctxt') = repair_agmT_abs nctxt T1 t (T2::T2list)
    in 
       (\<^Const>\<open>Product_Type.prod.case_prod T1 T2 retT\<close> $ fixed_t, nctxt')
    end
  | repair_agmT_abs nctxt (\<^Type>\<open>Product_Type.prod T1 T2\<close>) (Abs(aN,aT,t)) T2list = 
      if T1 = aT andalso T2 = @{typ "int list"} then 
        let 
          val (vecN,nctxt') = Name.variant (aN ^ "vec") nctxt 
          val (fixed_t, nctxt'') = case T2list of (T2::T2tl) => repair_agmT_abs nctxt' T2 t T2tl
          | [] => (t,nctxt)
          val retT = Term.fastype_of t |> Term.body_type
          val vec = Free (vecN,T2)
          val abs_vec = fixed_t |> Term.incr_boundvars 1 |> Term.lambda vec  (* TODO maybe the incr needs switching*)
        in
          (\<^Const>\<open>Product_Type.prod.case_prod T1 T2 retT\<close> $ Abs(aN, aT, abs_vec), nctxt'') (* TODO here extract to backtrack vecN*)
        end
      else raise AGMTYPE1
  | repair_agmT_abs nctxt T1 (Abs(varN, varT, t)) (T2::T2list) =
    if T1 <> varT then 
      raise AGMTYPE2(T1, (varN,varT))
    else 
      let 
        val (fixed_t, nctxt') = repair_agmT_abs nctxt T2 t T2list
      in
        (Abs(varN, varT, fixed_t), nctxt')
      end
 (* | repair_agmT_abs nctxt T1 (Abs(varN, varT, t)) (T2::T2list) =
    if T1 <> dummyT andalso T1 = varT then
      let 
        val (fixed_t, nctxt') = repair_agmT_abs nctxt dummyT t (T2::T2list)
      in
        (Abs(varN, varT, fixed_t), nctxt')
      end 
    else if T1 = dummyT andalso T2 = varT then
      let 
        val (fixed_t, nctxt') = repair_agmT_abs nctxt dummyT t T2list
      in 
        (Abs(varN, varT, fixed_t), nctxt')
      end
    else raise AGMTYPE2(T1, (varN,varT), T2)*)
  | repair_agmT_abs nctxt _ t  _ = (t,nctxt)
  

fun repair_agm_abs nctxt spmf abs = 
  let 
    val spmfT = Term.head_of spmf |> Term.fastype_of |> Term.body_type |> strip_spmfT
  in
    repair_agmT_abs nctxt spmfT abs []
  end

fun repair_agm_abss grpT nctxt t advs = 
  case t of 
    Const("SPMF.bind_spmf",bindT) $ spmf $ abs => (* TODO correct bindT in res*)
    let 
      val (fixed_abs,nctxt') = repair_agm_abss grpT nctxt abs advs
    in 
      if List.exists (fn a => Term.head_of spmf = a) advs then 
        let 
          val (fix,nctxt'') = repair_agm_abs nctxt' spmf fixed_abs
          val bindT_fix = Term.map_atyps (adjoin grpT @{typ "int list"}) bindT
        in 
          (Const("SPMF.bind_spmf",bindT_fix) $ spmf $ fix, nctxt'') 
        end
        else (Const("SPMF.bind_spmf",bindT) $ spmf $ fixed_abs, nctxt') 
    end
  | Abs(aT,aN,t) => 
    let 
      val (fixed_t, nctxt') = repair_agm_abss grpT nctxt t advs
    in 
      (Abs(aT,aN,fixed_t),nctxt')
    end
   | t1 $ t2 => 
      let 
        val (fixed_t1,nctxt') = repair_agm_abss grpT nctxt t1 advs;
        val (fixed_t2,nctxt'') = repair_agm_abss grpT nctxt' t2 advs;
      in 
        ((fixed_t1 $ fixed_t2), nctxt'')
      end
    | t => (t,nctxt)


(*
fun extract_AGM_combs ctxt grp_desc combs advs extrs = 
  let 
    
    val nctxt = Variable.names_of ctxt
    val agm_advs = map (fn a => enforce_alg nctxt grp_desc a) advs
    val combs' = agm_combs combs advs agm_advs extrs
  in 
    combs'
  end*)

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

text \<open>This takes a game in the standard model and lifts it into the AGM.\<close>
ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>lift_to_AGM\<close> "lift game to Algeraic Group Model"
    (Parse.term -- (\<^keyword>\<open>=>\<close> |--Parse.binding) >> 
      (fn (game_name,b) => fn lthy => 
      let
        val thy = Proof_Context.theory_of lthy;
        val game_ref = Syntax.read_term lthy game_name;
        val agm_term = Algebraic_Algorithm.unfold_def thy lthy game_ref;
        val (def, lthy') = Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), agm_term)) lthy;
      in lthy' end));
\<close>



subsection \<open>Examples\<close>

text \<open>Example to lift a game into the AGM\<close>


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

end

end
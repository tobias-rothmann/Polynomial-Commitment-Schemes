theory Test 
  imports Polynomial_Commitment_Schemes
  keywords
  "lift_to_algebraic" :: thy_decl
and  "local_test" :: thy_decl
begin

ML \<open>
signature ALGEBRAIC_ALGORITHM =
sig 

val rcodomain_transf : (typ -> typ) -> typ -> typ

val adjoin : typ -> typ -> (typ -> typ)

val lift_to_algebraicT : typ -> typ -> typ -> typ

val strip_spmfT : typ -> typ

val return_spmf : term -> term

val extract_type_params : typ -> string list

val rapply : term list -> term -> term 

val rabs : term list -> term -> term 

(* TODO delete the next two in the interface *)
val create_names_prod_cases :  Name.context -> typ -> term list * Name.context;

val extract_vec_pair_list: typ -> term list -> term

val constrain_pairs: Name.context -> typ -> typ -> term

val build_ret_term : Name.context -> typ -> term

val abs_typ_over_term : Name.context -> typ -> term -> term

val enforce_alg: Name.context -> typ -> term -> term

val build_alg_fun : Name.context -> typ -> typ -> term * Name.context

end;

structure Algebraic_Algorithm : ALGEBRAIC_ALGORITHM = 
struct

fun rcodomain_transf f (Type ("fun", [T, U])) = (Type ("fun", [T, f U]))
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
      (T1_res@T2_res, nctxt'') (*TODO Is this okay?*)
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

fun constrain_pairs nctxt T resT = resT 
  |> create_names_prod_cases nctxt 
  |> fst 
  |> extract_vec_pair_list T
  (*TODO here comes the assert*)

fun create_assert nctxt grpT resT = 
  let 
    val vlist = constrain_pairs nctxt grpT resT
    val assert_term = @{term True} (* TODO create assert term belongs here *)
  in 
    \<^Const>\<open>SPMF.assert_spmf for assert_term\<close>
  end

(* TODO create a constrain list pairs function. Accordingly create a type lifting that lifts 'g lists
to a pair ('g list, int list list) 
This function should also assert that the lists match in size *)

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
    val restT = t |> Term.fastype_of (* |> Term.dest_funT |> snd TODO ggf check for fun?*)
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

fun supply_prams nctxt t = 
  let  
    val T = Term.fastype_of t
    val (prams,nctxt') = extract_params nctxt T
  in 
    (rapply prams t, nctxt')
  end

fun build_assert_fun nctxt grpT retT t = 
  let 
    val unitT = @{typ unit}
    val assert_term = create_assert nctxt grpT retT
    val t' = Term.absdummy unitT t
  in
   \<^Const>\<open>bind_spmf unitT retT for assert_term t'\<close>
  end

fun build_body_fun nctxt grpT T = 
  build_ret_term nctxt T |> build_assert_fun nctxt grpT T |> abs_typ_over_term nctxt T

fun enforce_alg nctxt grpT t = 
  let 
    val (spmf,nctxt') = supply_prams nctxt t
    val retT = Term.fastype_of spmf |> strip_spmfT
    val body_term = build_body_fun nctxt' grpT retT
  in 
     \<^Const>\<open>bind_spmf retT retT for spmf body_term\<close>
  end

fun build_alg_fun nctxt grpT T = 
  let
    (* create params to abstract over*)
    val (prams,nctxt') = extract_params nctxt T
    (* instantiate the adversary*)
    val (advN, nctxt'') = Name.variant "\<A>" nctxt'
    val adv = Term.Free(advN,T)
    (* create the fun term to enforce the agm for the adversary *)
    val fun_term = enforce_alg nctxt grpT adv
  in 
    (rabs (rev (adv::prams)) fun_term, nctxt'')
  end

(* TODO write function that takes the free vars list and filters it for group#int_list#xs and 
  turns it into an Isar level (group*int list) list \<rightarrow> write function that takes the free vars 
  list, applies the previous described function, and applies create_assert to it.

  Then write a function that takes the free var list and creates prod and abstracts

  Finally put everything together. First create returns spmf, then apply the prod function, then spmf binding. 
  Once that works, extend with assert.
*)

end;
\<close>

ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>lift_to_algebraic\<close> "print term test"
    (Parse.typ -- (Parse.typ -- (Parse.typ -- (\<^keyword>\<open>=>\<close> |--Parse.binding))) >> 
      (fn (g,(v,(alg,b))) => fn lthy => Local_Theory.raw_theory (fn thy =>
      let
        val ctxt = Proof_Context.init_global thy;
        val gT = Syntax.read_typ ctxt g;
        val vT = Syntax.read_typ ctxt v;
        val algT = Syntax.read_typ ctxt alg;
        val agmT = Algebraic_Algorithm.lift_to_algebraicT gT vT algT;
        val tps = Algebraic_Algorithm.extract_type_params agmT;
        val thy' = Sign.add_type_abbrev ctxt (b, tps, agmT) thy
      in thy' end) lthy));
\<close>


context cyclic_group
begin 

fun constrain :: "'a \<Rightarrow> (int list) \<Rightarrow> bool"
  where "constrain g c_vec = (g = fold (\<lambda>c g. g \<otimes> \<^bold>g [^] c) c_vec \<^bold>g)"

fun constrain_list :: "('a \<times> int list) list \<Rightarrow> bool"
  where "constrain_list xs = list_all (\<lambda>(g, c_vec). constrain g c_vec) xs"

type_synonym ('g','b', 'a')alg = "'g' \<Rightarrow> 'b' \<Rightarrow> 'a' \<Rightarrow> ('g' * int*nat) spmf"

lift_to_algebraic 'g "int list"  "('g,'b,'a)cyclic_group.alg" => agm_adv

fun create_assert:: "'x * 'y list \<Rightarrow> bool spmf"
  where "create_assert (x,y) = return_spmf True"


declare [[ML_print_depth = 1000]]
ML \<open>
  val agmT = @{typ "('a,'b,'g)agm_adv"}

  val grpT = @{typ 'a}

  val (paramsT, resT) = Term.strip_type agmT

 val boolT = @{typ bool}

 (* val truet = @{term True}
  
  val testt = @{term "return_spmf True"}

  (* return_spmf*)
  val testt' = \<^Const>\<open>return_pmf  \<^Type>\<open>option boolT\<close> for \<^Const>\<open>Some boolT for truet\<close>\<close>*)

  val striped_resT = Algebraic_Algorithm.strip_spmfT resT

  val ret_True = Algebraic_Algorithm.return_spmf @{term True}

  val testgame =  \<^Const>\<open>bind_spmf boolT boolT for ret_True\<close>

  val testgame' = @{term "do {return_spmf True}"}

  val testtt = Algebraic_Algorithm.build_ret_term Name.context striped_resT

  val testttt = Algebraic_Algorithm.abs_typ_over_term Name.context striped_resT testtt 

  val test_term = @{term 
    "\<lambda>(A::('a,'b,'g)agm_adv) g b a. do { 
      ((g',c),i,j) \<leftarrow> A g b a;
      _::unit \<leftarrow> assert_spmf(True);
      return_spmf ((g',c),i,j) 
    }"}

 (* val adv_term = Term.Free("A", agmT)

  val test_monad = Algebraic_Algorithm.enforce_alg Name.context adv_term*)

  val test_monad' = Algebraic_Algorithm.build_alg_fun Name.context grpT agmT |> fst
(*
 bind_spmf type is not dependent on further statments in the monad, but the monads outcome.
bind_spmf type is reswspmf \<Rightarrow> (fun resw/ospmf \<Rightarrow> monad res) \<Rightarrow> monad_res 

In terms:
bind_spmf $ reswspmf $ (fun resw/ospmf \<Rightarrow> monad res)

Product_Type.prod.case_prod typ is:
(fun newtype \<Rightarrow> function typ) \<Rightarrow> new_type x codomain of fun type \<Rightarrow> domain of fun type


Strategy:
 bind_spmf is just aplly and gives one implicit var for the complete type 
  \<rightarrow> nothing todo
  the core is the function that takes the type without spmf and returns the end result type
  \<rightarrow> here two phases 
    1. define var decomposition with abs 
      \<longrightarrow> how to order the names i.e. 
          create the right names that are used in the body?
    2. define actual content with the vars. 
*)
\<close>


ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>local_test\<close> "test local definition"
    (Parse.binding >> (fn b => fn lthy =>
      let
        val agmT = @{typ "('a,'b,'g)agm_adv"}
        val grpT = @{typ "'a"}
        val agm_term = Algebraic_Algorithm.build_alg_fun Name.context grpT agmT |> fst;
        val (def, lthy') = Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), agm_term)) lthy;
      in lthy' end));
\<close>

declare [[show_types]]
local_test test_adv
thm test_adv_def 

definition test 
  where "test \<equiv> \<lambda>(A::('a,'b,'g)agm_adv) g b a. do { 
      ((g',c),i,j) \<leftarrow> A g b a;
      _::unit \<leftarrow>assert_spmf(True);
      return_spmf ((g',c),i,j) 
    }" 

lemma "test_adv \<equiv> test"
  unfolding test_def test_adv_def
  by argo

end


context abstract_polynomial_commitment_scheme
begin 

declare [[ML_print_depth = 1000]]
ML \<open>
 (*
   val test2 = @{term "\<lambda>(\<A>::('ck, 'commit, 'state, 'argument, 'evaluation, 'witness) 
  knowledge_soundness_adversary) (E::('r, 'commit, 'trapdoor) extractor). do {
  let (\<A>1,\<A>2) = \<A>;
  (ck,vk) \<leftarrow> key_gen;
  (c,\<sigma>) \<leftarrow> \<A>1 ck;  
  (p,d) \<leftarrow> E c;             
  (i, w) \<leftarrow> \<A>2 \<sigma>;                   
  let (p_i,_) = w;
  let (p_i',_) = eval ck d p i;         
  return_spmf (verify_eval vk c i w \<and> p_i \<noteq> p_i')       
  }"}
*)

  val test3 =  @{term eval_bind_game}
  val test4 =  Term.strip_comb (Thm.prop_of @{thm knowledge_soundness_game_def});

  (*val test3 = Term.strip_abs test2;*)

  (*writeln (Syntax.string_of_term  \<^context> test2);*)
  (*writeln (@{make_string} test2)*)
\<close>
(*TODO find out how c is represented (Var, Abs, Bound, Free, and how to change that)*) 

end


end
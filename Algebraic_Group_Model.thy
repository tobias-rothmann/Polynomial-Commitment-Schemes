theory Algebraic_Group_Model 
  imports CryptHOL.CryptHOL Restrictive_Comp
  keywords
  "lift_to_algebraicT" :: thy_decl
and "agm_interpretation" :: thy_decl
begin

text \<open>This theory extends CryptHOL for the Algebraic Group Model according to 
Fuchsbauer, Kiltz, and Loss: The Algebraic Group Model and its Applications
https://eprint.iacr.org/2017/620.pdf

Adversaries in CryptHOL are modelled as uninitialized parameters (arbitrary functions), thus we 
cannot ensure that the adversary algorithm itself is algebraic. Instead we enforce the algebraic 
rules on the outputs of the adversary, counting rule breaking as losing the game. Hence, every 
adversary with non-negligible advantage has to be an algebraic algorithm.

We formalize this relaxed notion of an algebraic algorithm as a sub case of Restrictive_Comp, i.e. 
we define the AGM in terms of a RCM.

We provide group specific records groupS and groupC for Select and constrain. Furthermore,  
we define some automation and sanity check functions in Isabelle/ML\<close>

context cyclic_group
begin

text \<open>group elements are the single important type we want to select.\<close>
definition groupS :: "('a,'a) Select"
  where "groupS \<equiv> \<lparr>select = (\<lambda>x. [x])\<rparr>"

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
    \<and> g = fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^esub> seen_vec!i [^]\<^bsub>G\<^esub> (c_vec!i)) [0..<length seen_vec] \<one>\<^bsub>G\<^esub>)"

definition groupC :: "('a, ('a \<times> int list)) Constrain"
  where "groupC \<equiv> \<lparr>constrain = (\<lambda>ip op. constrain_grp ip op)\<rparr>"

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

locale Algebraic_Algorithm = G : cyclic_group G 
  for G :: "('a, 'b) cyclic_group_scheme" (structure)
  + 
  fixes sel :: "('x,'a) Select"
  and con :: "('a,'y) Constrain"

sublocale Algebraic_Algorithm \<subseteq> Restrictive_Comp sel con .

locale algebraic_algorithm_examples = cyclic_group
begin

text \<open>To obtain an algebraic algorithm one needs to simply instantiate the restrictive_comp locale 
with the record composition that one needs and apply the non-algebraic algorithm to the obtained 
restrictive_comp.restrict.\<close>

text\<open>The trivial example of only one group element as in and output.\<close>
text \<open>For simplicity let the adversary be id\<close>

definition \<A>_id :: "'a \<Rightarrow> ('a \<times> int list) spmf" 
  where "\<A>_id = (\<lambda>x. return_spmf (x, [1::int]))"

interpretation Algebraic_Algorithm G "groupS" "groupC" 
  by (unfold_locales) 

lemma 
  assumes "g \<in> carrier G"
  shows "restrict \<A>_id g
    = \<A>_id g"
  unfolding \<A>_id_def Restrictive_Comp.restrict_def 
  unfolding groupS_def groupC_def constrain_grp_def
  by (simp add: assms)
  
text \<open>Now the same for a list of input elements and and output elements\<close>

definition \<A>_list_fst :: "'a list \<Rightarrow> ('a \<times> int list) list spmf" 
  where "\<A>_list_fst = (\<lambda>x. return_spmf (map (\<lambda>_. (x!0, [1::int,0,0])) x))"

interpretation list_id: Restrictive_Comp "(listS groupS)" "listC groupC" .

lemma 
  assumes "g1 \<in> carrier G \<and> g2 \<in> carrier G \<and> g3 \<in> carrier G"
  shows "list_id.restrict \<A>_list_fst [g1,g2,g3]
    = \<A>_list_fst [g1,g2,g3]"
  unfolding \<A>_list_fst_def Restrictive_Comp.restrict_def
  unfolding listS_def groupS_def listC_def groupC_def 
    unfolding constrain_grp_def
  by (simp add: assms)

text \<open>We define some useful ML functions for the AGM.

wellformed is a sanity check that checks, given a group G and a function type, that the function 
type returns a creation vector (int list) paired with every group value in the output.  

lift_to_algebraicT operates on the type level, lifting standard model function types into their 
corresponding type as an algebraic algorithm. I.e. extend the outputs that are group elements 
with a vector.

agm_interpretation automates the instance resolution: given a group and a function type, it 
automatically lifts the function type via lift_to_algebraicT and interprets AlgebraicAlgorithm
with a composed Select record, mirroring the functions (decurried) input, and Constrain record, 
mirroring the functions output.
\<close>

text \<open>This takes any algorithm/function type and lifts it to the algebraic algorithm equivalent type.
For examples take a look at the end of this file.\<close>
ML \<open>
  local 
    (*apply function f to the codaomain of a function*)
    fun rcodomain_transf f (Type ("fun", [T, U])) = (Type ("fun", [T, rcodomain_transf f U]))
      | rcodomain_transf f T = f T;
    
    (*adjoin vec to t as a product type if the Type = t*)
    fun adjoin t vec = fn T => if T = t then Type ("Product_Type.prod", [T, vec]) else T
    
    (*decurry a function*)
    fun decurry (Type ("fun", [T1, Type ("fun", [T2, T3])])) = 
        decurry (Type ("fun", [Type ("Product_Type.prod", [T1, T2]), T3]))
      | decurry T = T
    
    fun extract_type_params t = Term.add_tfree_namesT t []
    
    fun lift_to_algebraicT grpT vec = (rcodomain_transf (Term.map_atyps (adjoin grpT vec))) o decurry

  in 
  val _ = 
    Outer_Syntax.local_theory \<^command_keyword>\<open>lift_to_algebraicT\<close> "lift to algebraic type"
      (Parse.typ -- (Parse.term -- (\<^keyword>\<open>=>\<close> |--Parse.binding)) >> 
        (fn (alg,(grp,b)) => fn lthy => Local_Theory.raw_theory (fn thy =>
        let
          val algT = Syntax.read_typ lthy alg;
          val grp_desc = Syntax.read_term lthy grp;
          val grpT = Term.fastype_of grp_desc |> Term.dest_Type_args |> hd;
          val agmT = lift_to_algebraicT grpT @{typ "int list"} algT;
          val tps = extract_type_params agmT;
          val thy' = Sign.add_type_abbrev lthy (b, tps, agmT) thy
        in thy' end) lthy));
  end;
\<close>

ML \<open>
  local
    fun rcodomain_transf f (Type ("fun", [T, U])) = (Type ("fun", [T, rcodomain_transf f U]))
      | rcodomain_transf f T = f T;

    fun adjoin t vec = fn T => if T = t then Type ("Product_Type.prod", [T, vec]) else T;

    fun decurry (Type ("fun", [T1, Type ("fun", [T2, T3])])) =
        decurry (Type ("fun", [Type ("Product_Type.prod", [T1, T2]), T3]))
      | decurry T = T;

    fun lift_to_algebraicT grpT vec =
      (rcodomain_transf (Term.map_atyps (adjoin grpT vec))) o decurry;

    fun const_exists ctxt name =
      let
        val thy = Proof_Context.theory_of ctxt;
      in
        can (fn n => Sign.const_type thy (Proof_Context.intern_const ctxt n)) name
      end;

    fun mk_select ctxt grpT grp_s T =
      if T = grpT then "cyclic_group.groupS"
      else
        (case T of
          Type ("Product_Type.prod", [A, B]) =>
            "prodS (" ^ mk_select ctxt grpT grp_s A ^ ") (" ^ mk_select ctxt grpT grp_s B ^ ")"
        | Type (tycon, args) =>
            let
              val ctor = Long_Name.base_name tycon ^ "S";
            in
              if const_exists ctxt ctor then
                fold (fn arg => fn acc => acc ^ " (" ^ mk_select ctxt grpT grp_s arg ^ ")") args ctor
              else "noSelect"
            end
        | _ => "noSelect");

    fun mk_constrain ctxt grpT vecT grp_s T =
      (case T of
        Type ("Product_Type.prod", [A, B]) =>
          if A = grpT andalso B = vecT then "(cyclic_group.groupC " ^ grp_s ^ ")"
          else "prodC (" ^ mk_constrain ctxt grpT vecT grp_s A ^ ") (" ^ mk_constrain ctxt grpT vecT grp_s B ^ ")"
      | Type (tycon, args) =>
          let
            val ctor = Long_Name.base_name tycon ^ "C";
          in
            if const_exists ctxt ctor then
              fold (fn arg => fn acc => acc ^ " (" ^ mk_constrain ctxt grpT vecT grp_s arg ^ ")") args ctor
            else "noConstrain"
          end
      | _ => "noConstrain");

    fun mk_unfold_locales_method_range () : Method.text_range =
      let
        val src = Token.make_src ("unfold_locales", Position.none) [];
      in
        (Method.Source src, Position.no_range)
      end;

    fun strip_markup s =
      let
        val X = #"\005";
        fun go [] _ acc = String.implode (rev acc)
          | go (c :: cs) in_tag acc =
              if in_tag then
                if c = X then go cs false acc else go cs true acc
              else if c = X then go cs true acc
              else go cs false (c :: acc);
      in
        go (String.explode s) false []
      end;

    fun safe_term_source ctxt t =
      strip_markup (Syntax.string_of_term ctxt t);

    fun mk_alg_expr (b: binding) (g: string) (sel: string) (con: string) : Expression.expression =
      let
        val prefix = (Binding.name_of b, true);
        val inst = Expression.Positional [SOME g, SOME sel, SOME con];
        val expr = [(("Algebraic_Algorithm", Position.none), (prefix, (inst, [])))];
      in
        (expr, [])
      end;
  in
    val _ =
      Outer_Syntax.command \<^command_keyword>\<open>agm_interpretation\<close>
        "interpret Algebraic_Algorithm and discharge obligations via unfold_locales"
        (Parse.binding --| \<^keyword>\<open>:\<close> -- Parse.term -- Parse.typ >>
          (fn ((b, g), alg_ty) =>
            let
              val m = mk_unfold_locales_method_range ();
              fun interp lthy =
                let
                  val algT = Syntax.read_typ lthy alg_ty;
                  val grp_desc = Syntax.read_term lthy g;
                  val grp_s =
                    (case try (fn () => safe_term_source lthy grp_desc) () of
                      SOME s => s
                    | NONE => strip_markup g);
                  val grpT = Term.fastype_of grp_desc |> Term.dest_Type_args |> hd;
                  val vecT = @{typ "int list"};
                  val agmT = lift_to_algebraicT grpT vecT algT;
                  val (inps, resT) = Term.strip_type agmT;
                  val inpT =
                    (case inps of
                      [] => error "agm_interpretation: expected function type"
                    | T :: Ts =>
                        fold (fn U => fn acc => Type ("Product_Type.prod", [acc, U])) Ts T);
                  val outT =
                    let
                      val thy = Proof_Context.theory_of lthy;
                      val out_ix = ("out", 0);
                      val out_tv = (out_ix, @{sort type});
                      val spmf_pat =
                        Term.map_atyps (K (TVar out_tv)) @{typ "'a spmf"};
                    in
                      (case try (fn () => Sign.typ_match thy (spmf_pat, resT) Vartab.empty) () of
                        SOME tyenv =>
                          (case Vartab.lookup tyenv out_ix of
                            SOME (_, T) => T
                          | NONE =>
                              error
                                ("agm_interpretation: internal error (failed to recover spmf type argument)"))
                      | NONE =>
                          error
                            ("agm_interpretation: expected lifted type with codomain _ spmf, got: " ^
                             Syntax.string_of_typ lthy resT ^ " in " ^ Syntax.string_of_typ lthy agmT))
                    end;
                  val sel_s = mk_select lthy grpT grp_s inpT;
                  val con_s = mk_constrain lthy grpT vecT grp_s outT;
                  val expr = mk_alg_expr b grp_s sel_s con_s;
                in
                  Interpretation.isar_interpretation_cmd expr lthy
                end;
            in
              Toplevel.local_theory_to_proof NONE NONE interp
              #> Toplevel.proofs (Proof.apply_end m)
              #> Toplevel.proof Proof.local_done_proof
            end))
  end;
\<close>

subsection \<open>Examples for the ML functions\<close>

text \<open>We define a standard model adversary with group G of type 'a\<close>
type_synonym ('a')adv = "'a' list \<Rightarrow> 'a' \<Rightarrow> nat \<Rightarrow> ('a' * int * nat) spmf"

text \<open>We lift the type into the AGM (its algebraic algorithm pendant):\<close>
lift_to_algebraicT "('a) adv"  "G" => algebraic_adv


text \<open>We interpret restrict for the created algebraic_adv\<close>
interpretation manualAGM: Algebraic_Algorithm G "prodS (prodS (listS groupS) groupS) noSelect" 
  "prodC groupC (prodC noConstrain noConstrain)"
  by (unfold_locales)

text \<open>We skip the last step and automatically interpret the right version restrict version 
for adv.\<close>
agm_interpretation autoAGM : G "('a)adv" ..

lemma "manualAGM.restrict = autoAGM.restrict"
  unfolding manualAGM.restrict_def autoAGM.restrict_def
  by simp
  

end

end
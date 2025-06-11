theory Test 
  imports Main
  keywords
  "lift_to_algebraic" :: thy_decl
begin 

ML \<open>
signature ALGEBRAIC_ALGORITHM =
sig 

val rcodomain_transf : (typ -> typ) -> typ -> typ

val adjoin : typ -> typ -> (typ -> typ)

val lift_to_algebraic : typ -> typ -> typ -> typ

val extract_type_params : typ -> string list

end;

structure Algebraic_Algorithm : ALGEBRAIC_ALGORITHM = 
struct

fun rcodomain_transf f (Type ("fun", [T, U])) = (Type ("fun", [T, f U]))
  | rcodomain_transf f T = f T;

fun adjoin t vec = fn T => if T = t then Type ("Product_Type.prod", [T, vec]) else T

fun lift_to_algebraic grpT vec = (rcodomain_transf o Term.map_atyps) (adjoin grpT vec)

fun extract_type_params t = Term.add_tfree_namesT t []

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
        val agmT = Algebraic_Algorithm.lift_to_algebraic gT vT algT;
        val tps = Algebraic_Algorithm.extract_type_params agmT;
        val thy' = Sign.add_type_abbrev ctxt (b, tps, agmT) thy
      in thy' end) lthy));
\<close>

locale semigroup =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes assoc: "f (f x y) z = f x (f y z)"
begin

lemma left_assoc: "f x (f y z) = f (f x y) z"
  using assoc by simp

type_synonym ('g','b', 'a')alg = "'g' \<Rightarrow> 'b' \<Rightarrow> 'a' \<Rightarrow> ('g' * int)"

lift_to_algebraic 'g "int list"  "'g \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> ('g * int * ('g * bool) * nat)" => agm_adv

ML \<open>

  (* val testT = @{typ 'a}
  val tps = Algebraic_Algorithm.extract_type_params testT;
  val advT = @{typ "'g \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> ('g * int)"}
  val alg = Algebraic_Algorithm.lift_to_algebraic @{typ 'g} @{typ "int list"} advT;*)

  val t = @{typ "('a,'b,'g)agm_adv"}
\<close>

(* Test Ground *)

type_synonym pair = "(int * int)"

ML \<open>

fun type_constructor_name_option my_typ =
  (case my_typ of
    Type (name, _) => SOME name  (* If it's a type constructor application, extract its name *)
  | TFree (_, _) => NONE         (* It's a fixed type variable like 'a' *)
  | TVar (_, _) => NONE);

val t = @{typ pair}

val ts = type_constructor_name_option t

val ct = @{typ "'a \<Rightarrow> bool \<Rightarrow> 'a * 'b"}

fun f _ = @{typ int};

val t' = Term.map_atyps f ct;
\<close>

end

end
theory Test 
  imports Main
  keywords
  "global_test" :: thy_decl
begin 

ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>global_test\<close> "print term test"
    (Parse.binding -- (\<^keyword>\<open>=\<close> |-- Parse.typ) >> (fn (b,s) => Toplevel.theory (fn thy =>
      let
        val ctxt = Proof_Context.init_global thy;
        val t = Syntax.read_typ ctxt s;
        fun f _ = @{typ "int * int"};
        val t' = Term.map_atyps f t;
        val thy' = Sign.add_type_abbrev ctxt (b, [], t') thy
      in thy' end)));
\<close>

global_test agm = 'a

end 
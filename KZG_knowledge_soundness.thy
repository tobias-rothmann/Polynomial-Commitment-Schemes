theory KZG_knowledge_soundness

imports KZG_eval_bind Algebraic_Group_Model

begin

locale KZG_PCS_knowledge_sound = KZG_PCS_binding
begin 


lift_to_agm "('a ck, 'a commit, 'state) knowledge_soundness_adversary1"  "G\<^sub>p"  => AGM_knowledge_soundness_adversary1
AGMLifting  "('a ck, 'a commit, 'state) knowledge_soundness_adversary1" "G\<^sub>p" => lift_\<A>1
thm lift_\<A>1_def

lift_to_agm "('state, 'e mod_ring, 'e evaluation, 'a witness) knowledge_soundness_adversary2"  "G\<^sub>p"  => AGM_knowledge_soundness_adversary2
AGMLifting  "('state, 'e mod_ring, 'e evaluation, 'a witness) knowledge_soundness_adversary2" "G\<^sub>p" => lift_\<A>2
thm lift_\<A>2_def

text \<open>print obtained adversary types\<close>
ML \<open>
  val agm_adv1 = @{typ "('state, 'a) AGM_knowledge_soundness_adversary1"}
  val agm_adv2 = @{typ "('a, 'e, 'state) AGM_knowledge_soundness_adversary2"}
\<close>

text \<open>The extractor is an algorithm that plays against the adversary. It is granted access to the 
adversaries messages and state (which we neglect in this case as we do not need it because the 
calculation vector is enough to create sensible values) and has to come up with a polynomial such 
that the adversary cannot create valid opening points that are not part of the polynomial.\<close>
type_synonym ('a', 'e') extractor = 
  "('a' commit \<times> int list) \<Rightarrow> 
    ('e' mod_ring poly \<times> unit) spmf"

text \<open>the knowledge soundness game in the agm\<close>
definition AGM_knowledge_soundness_game :: "(('state, 'a) AGM_knowledge_soundness_adversary1 
  \<times> ('a, 'e, 'state) AGM_knowledge_soundness_adversary2) 
  \<Rightarrow> ('a, 'e) extractor \<Rightarrow> bool spmf"
  where "AGM_knowledge_soundness_game \<A> E = TRY do {
  let (\<A>1,\<A>2) = \<A>;
  let \<A>1_AGM = lift_\<A>1 \<A>1;
  (ck,vk) \<leftarrow> key_gen;
  ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
  (p,td) \<leftarrow> E (c,cvec);
  (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
  let (p_i',w') = Eval ck td p i;         
  return_spmf (verify_eval vk c i (p_i,w) \<and> p_i \<noteq> p_i' \<and> valid_eval (p_i,w))       
  } ELSE return_spmf False"

text \<open>reduction to eval bind game\<close>
definition knowledge_soundness_reduction
  :: "('a, 'e) extractor \<Rightarrow> ('state, 'a) AGM_knowledge_soundness_adversary1  
  \<Rightarrow> ('a, 'e, 'state) AGM_knowledge_soundness_adversary2
  \<Rightarrow> ('a ck, 'a commit, 'e argument, 'e evaluation, 'a witness)  eval_bind_adversary"                     
where
  "knowledge_soundness_reduction \<E> \<A>1 \<A>2 ck = do {
  let \<A>1_AGM = lift_\<A>1 \<A>1;
  let \<A>2_AGM = lift_\<A>2 \<A>2;
  ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
  (p,td) \<leftarrow> \<E> (c,cvec);
  (i, p_i, w, wvec) \<leftarrow> \<A>2 \<sigma>;
  let (p_i',w') = Eval ck td p i;
  return_spmf (c, i, p_i, w, p_i', w')}"

text \<open>Extractor definition\<close>
fun E :: "('a, 'e) extractor" where 
  "E (c,cvec) = return_spmf (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec),())"

subsection \<open>helping definitions\<close>

text \<open>The knowledge soundness reduction adversary extended for asserts that 
are present in the evaluation binding game. We use this definition to show equivalence to 
the evaluation binding game. Later on we can then easily over-estimate the probability from 
this extended version to the normal reduction.\<close> (* TODO properly integrate AGM2*)
definition knowledge_soundness_reduction_ext
  :: "('a, 'e) extractor \<Rightarrow> ('state, 'a) AGM_knowledge_soundness_adversary1  
  \<Rightarrow> ('a, 'e, 'state) AGM_knowledge_soundness_adversary2
  \<Rightarrow> ('a ck, 'a commit, 'e argument, 'e evaluation, 'a witness)  eval_bind_adversary"                     
where
  "knowledge_soundness_reduction_ext \<E> \<A>1 \<A>2 ck = do {
  let \<A>1_AGM = lift_\<A>1 \<A>1;
  let \<A>2_AGM = lift_\<A>2 \<A>2;
  ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
  (p,td) \<leftarrow> \<E> (c,cvec);
  (i, p_i, w, wvec) \<leftarrow> \<A>2 \<sigma>;
  _ :: unit \<leftarrow> assert_spmf (valid_eval (p_i, w));
  let (p_i',w') = Eval ck td p i;
  return_spmf (c, i, p_i, w, p_i', w')}"

subsection \<open>helping lemmas\<close>

text \<open>CryptHOL extenstions\<close>
lemma assert_commute: "bind_spmf X (\<lambda>x. bind_spmf (assert_spmf Y) (\<lambda>_. Z x)) 
  = bind_spmf (assert_spmf Y) (\<lambda>_. bind_spmf X (\<lambda>x. Z x))"
  by (rule bind_commute_spmf)

thm assert_commute[symmetric]

lemma assert_collapse: "bind_spmf (assert_spmf X) (\<lambda>_. bind_spmf (assert_spmf Y) (\<lambda>_. Z)) = 
   bind_spmf (assert_spmf (X \<and> Y)) (\<lambda>_. Z)"
  by (smt (verit) assert_spmf_simps(1,2) return_None_bind_spmf return_bind_spmf)

lemma assert_cong: " X = Y \<Longrightarrow> rel_spmf (=) (assert_spmf X)  (assert_spmf Y)"
  by simp

text \<open>proof related helping lemmas\<close> (* TODO delete or add \<and> w \<noteq> w'*)

lemma ks_imp_eval_bind_asserts:
      " let ck = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
           vk = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
           (p_i',w') = Eval ck td (Poly (map of_int_mod_ring cvec)) i 
       in
          length ck = length (cvec::int list)
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
          \<and> verify_eval vk c i (p_i,w)
          \<and> p_i \<noteq> p_i'
          \<and> valid_eval (p_i,w) 
        \<longleftrightarrow>
          length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
          \<and> p_i \<noteq> p_i'
          
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w')
          \<and> verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w')"
proof -
  define ck where ck_def: "ck = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]"
  define vk where vk_def: "vk = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]"
  define p_i'  where p_i'_def: "p_i' = fst (Eval ck td (Poly (map of_int_mod_ring cvec)) i)" 
  define w'  where w'_def: "w' = snd (Eval ck td (Poly (map of_int_mod_ring cvec)) i)" 

  (* TODO add or remove \<and> w \<noteq> w'*)
  have " length ck = length (cvec::int list)
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
          \<and> verify_eval vk c i (p_i,w)
          \<and> p_i \<noteq> p_i'
          \<and> valid_eval (p_i,w) 
        \<longleftrightarrow>
          length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
          \<and> p_i \<noteq> p_i'
          
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w')
          \<and> verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w')"
  (is "?lhs \<longleftrightarrow> ?rhs")
  proof 
    assume asm: "?lhs"
    show "?rhs"
    proof(intro conjI)
      from asm show valid_eval_adv: "valid_eval (p_i, w)" by force
      from asm show "verify_eval vk c i (p_i, w)" by force
  
      show valid_eval_gen: "valid_eval (p_i', w')"
      proof -
        have "g_pow_PK_Prod ck (\<psi>_of (Poly (map of_int_mod_ring cvec)) i) 
        = \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (poly (\<psi>_of (Poly (map of_int_mod_ring cvec)) i) \<alpha>)"
          unfolding ck_def
        proof (rule g_pow_PK_Prod_correct)
          show "degree (\<psi>_of (Poly (map of_int_mod_ring cvec)) i) \<le> max_deg"
          proof (rule  le_trans[OF degree_q_le_\<phi>])
            have "length (map of_int_mod_ring cvec) = max_deg +1"
              using asm unfolding ck_def by force
            moreover have "length (coeffs (Poly (map of_int_mod_ring cvec))) \<le> length (map of_int_mod_ring cvec)"
              by (metis coeffs_Poly length_map length_strip_while_le)
            ultimately show "degree (Poly (map of_int_mod_ring cvec)) \<le> max_deg"
              using degree_eq_length_coeffs[of "Poly (map of_int_mod_ring cvec)"]
              by (metis le_diff_conv)
          qed
        qed
        then show ?thesis 
          unfolding valid_eval_def
          by (simp add: Eval_def p_i'_def w'_def)
      qed
  
  
      show verify_eval_gen: "verify_eval vk c i (p_i', w')"
      proof -
        let ?cvec = "(map of_int_mod_ring cvec::'e mod_ring list)"
  
        have length_cvec: "length ?cvec = max_deg +1"
          using asm unfolding ck_def by force
        moreover have "length (coeffs (Poly ?cvec)) \<le> length ?cvec"
          by (metis coeffs_Poly length_strip_while_le)
        ultimately have deg_poly_calc_vec_le_max_deg: "degree (Poly ?cvec) \<le> max_deg"
          using degree_eq_length_coeffs[of "Poly ?cvec"]
          by (metis coeffs_Poly le_diff_conv length_strip_while_le)
        
        have 1: "(g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1])
          (\<psi>_of (Poly ?cvec) i))
          = (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (\<psi>_of (Poly ?cvec) i) \<alpha>)"
        proof(rule  g_pow_PK_Prod_correct)
          show "degree (\<psi>_of (Poly ?cvec) i) \<le> max_deg"
            by (rule le_trans[OF degree_q_le_\<phi>])(fact deg_poly_calc_vec_le_max_deg)
        qed
  
        have 2: "map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1] ! 1 = \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha>"
          by (metis (no_types, lifting) One_nat_def add.commute d_pos diff_zero le_add_same_cancel1 le_zero_eq length_upt nth_map nth_upt plus_1_eq_Suc power_one_right zero_compare_simps(1))
        
        have 3: "(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (Poly ?cvec) \<alpha>) = c"
        proof -
          have "(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (Poly ?cvec) \<alpha>) 
               = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (Poly ?cvec)"
            by (rule g_pow_PK_Prod_correct[symmetric])(fact deg_poly_calc_vec_le_max_deg)
          also have g_pow_to_fold: "\<dots> = fold (\<lambda>i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^i)) ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff (Poly ?cvec) i)) 
            [0..<Suc (degree (Poly ?cvec))] \<one>\<^bsub>G\<^sub>p\<^esub>"
            by (rule g_pow_PK_Prod_to_fold)(fact deg_poly_calc_vec_le_max_deg)
          also have "\<dots> 
          =fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^i)) ^\<^bsub>G\<^sub>p\<^esub> (?cvec!i)) [0..<max_deg+1] \<one>\<^bsub>G\<^sub>p\<^esub>"
          proof -
            have "fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! i) [0..<max_deg + 1] \<one>
                = fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! i) 
                    ([0..<Suc (degree (Poly ?cvec))] @ [Suc (degree (Poly ?cvec))..<max_deg + 1]) 
                    \<one>" 
            proof -
              have "Suc (degree (Poly ?cvec)) \<le> max_deg +1"
                by (simp add: deg_poly_calc_vec_le_max_deg)
              then show ?thesis
                by (metis (lifting) nat_le_iff_add upt_add_eq_append zero_order(1))
            qed
            also have "\<dots> = fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! i) 
                              [Suc (degree (Poly ?cvec))..<max_deg + 1]
                              (fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! i) 
                               [0..<Suc (degree (Poly ?cvec))] \<one>)"
              by fastforce
            also have "\<dots> = fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff (Poly ?cvec) i) 
                              [0..<Suc (degree (Poly ?cvec))] 
                              \<one>"
            proof -
              have "fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! i) [0..<Suc (degree (Poly ?cvec))] \<one> 
                  = fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff (Poly ?cvec) i) [0..<Suc (degree (Poly ?cvec))] \<one>" 
              proof (rule List.fold_cong) 
                show " \<And>x. x \<in> set [0..<Suc (degree (Poly ?cvec))] \<Longrightarrow>
                         (\<lambda>acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x) =
                         (\<lambda>acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff (Poly ?cvec) x)"
                proof 
                  fix x::nat
                  fix acc::'a
                  assume asm: "x \<in> set [0..<Suc (degree (Poly ?cvec))]"
                  then have "?cvec ! x = poly.coeff (Poly ?cvec) x"
                    by (metis \<open>length ?cvec = max_deg + 1\<close> atLeastLessThan_iff coeff_Poly deg_poly_calc_vec_le_max_deg dual_order.trans less_Suc_eq_le nth_default_nth semiring_norm(174) set_upt)
                  then show "acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x = acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> poly.coeff (Poly ?cvec) x "
                    by presburger
                qed
              qed simp+
              moreover have "\<forall>init \<in> carrier G\<^sub>p. 
                      fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! i) 
                        [Suc (degree (Poly ?cvec))..<max_deg + 1] 
                        init 
                      = init"
              proof 
                fix init ::'a
                assume init_in_carrier: "init \<in> carrier G\<^sub>p"
                have "fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! i) 
                        [Suc (degree (Poly ?cvec))..<max_deg + 1]    
                        init = fold (\<lambda>i acc. acc \<otimes> \<one>) 
                        [Suc (degree (Poly ?cvec))..<max_deg + 1] 
                        init"
                proof (rule List.fold_cong)
                  show " \<And>x. x \<in> set [Suc (degree (Poly ?cvec))..<max_deg + 1] \<Longrightarrow>
                          (\<lambda>acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x) = (\<lambda>acc. acc \<otimes> \<one>)"
                  proof 
                    fix x::nat
                    fix acc ::'a
                    assume asm: "x \<in> set [Suc (degree (Poly ?cvec))..<max_deg + 1]"
                    show "acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x = acc  \<otimes> \<one>"
                    proof -
                      have " ?cvec ! x = 0" using asm length_cvec
                        by (smt (verit) add.commute coeff_Poly_eq in_set_conv_nth le_degree length_upt less_diff_conv not_less_eq_eq nth_default_eq_dflt_iff nth_upt order.refl trans_le_add2)
                      then have "(\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x = \<one>" by simp
                      then show ?thesis by argo 
                    qed
                  qed
                qed simp+
                also have "\<dots> = init" 
                proof (induction max_deg)
                  case 0
                  then show ?case by fastforce
                next
                  case (Suc max_deg)
                  have "fold (\<lambda>i acc. acc \<otimes> \<one>) [Suc (degree (Poly ?cvec))..<Suc max_deg + 1] init
                  = fold (\<lambda>i acc. acc \<otimes> \<one>) ([Suc (degree (Poly ?cvec))..<max_deg + 1] @ [Suc max_deg]) init"
                    by (simp add: init_in_carrier)
                  also have "\<dots> = fold (\<lambda>i acc. acc \<otimes> \<one>) [Suc max_deg] (fold (\<lambda>i acc. acc \<otimes> \<one>) [Suc (degree (Poly ?cvec))..<max_deg + 1] init)"
                    by force
                  also have "\<dots> = fold (\<lambda>i acc. acc \<otimes> \<one>) [Suc max_deg] init" using Suc.IH by argo
                  also have "\<dots> = init \<otimes> \<one>" by force
                  also have "\<dots> = init" by (simp add: init_in_carrier)
                  finally show ?case .
                qed
                finally show "fold (\<lambda>i acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ i) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! i) 
                        [Suc (degree (Poly ?cvec))..<max_deg + 1] 
                        init 
                     = init" .
              qed
              ultimately show ?thesis
                by (metis (no_types, lifting) G\<^sub>p.generator_closed G\<^sub>p.int_pow_closed \<open>\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> poly (Poly ?cvec) \<alpha> = g_pow_PK_Prod (map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1]) (Poly ?cvec)\<close> g_pow_to_fold)
            qed
            finally show ?thesis by presburger
          qed
          also have "\<dots> 
          =fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])!i ^\<^bsub>G\<^sub>p\<^esub> (?cvec!i)) [0..<max_deg+1] \<one>\<^bsub>G\<^sub>p\<^esub>"
          proof(rule List.fold_cong)
            show "\<one> = \<one>" by simp
            show "[0..<max_deg + 1] = [0..<max_deg + 1]" by simp
            show "\<And>x. x \<in> set [0..<max_deg + 1] \<Longrightarrow>
             (\<lambda>acc. acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x) =
             (\<lambda>acc. acc \<otimes> map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1] ! x ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x)"
            proof 
              fix x::nat 
              fix acc :: 'a
              assume asm: "x \<in> set [0..<max_deg + 1]"
              show " acc \<otimes> (\<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ x) ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x 
                   = acc \<otimes> map (\<lambda>t. \<^bold>g ^\<^bsub>G\<^sub>p\<^esub> \<alpha> ^ t) [0..<max_deg + 1] ! x ^\<^bsub>G\<^sub>p\<^esub> ?cvec ! x"
                using PK_i[symmetric] asm
                by (metis Suc_eq_plus1 atLeastLessThan_iff less_Suc_eq_le set_upt)
            qed
          qed
          also have "\<dots> 
          =fold (\<lambda> i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> (map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1])!i ^\<^bsub>G\<^sub>p\<^esub> (of_int_mod_ring (cvec!i))) [0..<max_deg+1] \<one>\<^bsub>G\<^sub>p\<^esub>"
          proof(rule List.fold_cong)
            fix x
            assume "x \<in> set [0..<max_deg + 1]"
            then have "x < length cvec" 
              using asm unfolding ck_def 
              by fastforce
            then show "(\<lambda>acc. acc \<otimes> map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1] ! x ^ map of_int_mod_ring cvec ! x) =
           (\<lambda>acc. acc \<otimes> map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1] ! x ^ of_int_mod_ring (cvec ! x))"
              by force
          qed simp+
          also have "\<dots> = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>"
          proof -
            have length_eq_max_deg: "length (map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1]) = max_deg +1"
              by force
            have mod_ring_trnsf_eq_plain: "\<And>g x. g \<in> carrier G\<^sub>p \<Longrightarrow>  g [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (of_int_mod_ring x::'e mod_ring)) = g [^]\<^bsub>G\<^sub>p\<^esub> x"
            proof -
              fix g x
              assume g_in_carrier: "g \<in> carrier G\<^sub>p"
              have mod_red: "to_int_mod_ring (of_int_mod_ring x::'e mod_ring) = x mod p"
                unfolding of_int_mod_ring_def to_int_mod_ring_def 
                by (metis CARD_q of_int_mod_ring.rep_eq of_int_mod_ring_def to_int_mod_ring.rep_eq to_int_mod_ring_def)
              then show  "g [^]\<^bsub>G\<^sub>p\<^esub> (to_int_mod_ring (of_int_mod_ring x::'e mod_ring)) = g [^]\<^bsub>G\<^sub>p\<^esub> x"
                using carrier_pow_mod_order_G\<^sub>p g_in_carrier mod_red by metis
            qed
            show ?thesis 
            proof(rule List.fold_cong)
              fix x 
              assume "x \<in> set [0..<max_deg + 1]"
              then show "(\<lambda>acc. acc \<otimes> map (\<lambda>t. \<^bold>g ^ \<alpha> ^ t) [0..<max_deg + 1] ! x ^ of_int_mod_ring (cvec ! x)) = (\<lambda>acc. acc \<otimes> ck ! x [^] cvec ! x)"
                unfolding ck_def length_eq_max_deg using mod_ring_trnsf_eq_plain 
                by (metis (no_types, lifting) G\<^sub>p.generator_closed G\<^sub>p.int_pow_closed atLeastLessThan_iff length_upt nth_map set_upt verit_minus_simplify(2))
            qed (simp add: ck_def)+
          qed
          also have "\<dots> = c" 
            using asm unfolding ck_def by fast
          finally show ?thesis . 
        qed
        show ?thesis
          unfolding verify_eval_def Eval_def Let_def split_def g_pow_PK_Prod_correct 
          using eq_on_e[of "(Poly ?cvec)" i \<alpha>]
          by (metis "1" "2" 3 Eval_def ck_def vk_def p_i'_def w'_def eq_on_e fst_conv snd_conv)
      qed
    qed (force simp add: asm)+
  next
    assume asm: "?rhs"
    show "?lhs" 
    proof(intro conjI)
      from asm show "valid_eval (p_i, w)" by force
      from asm show "verify_eval vk c i (p_i, w)" by force
    qed (simp add: asm)+
  qed
  then show ?thesis 
    unfolding ck_def vk_def p_i'_def w'_def Let_def split_def by fast
qed

lemma knowledge_soundness_game_alt_def: 
  "AGM_knowledge_soundness_game (\<A>1,\<A>2) E = 
  eval_bind_game (knowledge_soundness_reduction_ext E \<A>1 \<A>2)"
proof -
  note [simp] = Let_def split_def

  have "AGM_knowledge_soundness_game (\<A>1,\<A>2) E = 
    TRY do {
      let \<A>1_AGM = lift_\<A>1 \<A>1;
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;         
      return_spmf (verify_eval vk c i (p_i,w) \<and> p_i \<noteq> p_i' \<and> valid_eval (p_i,w))       
    } ELSE return_spmf False"
       by (simp add: AGM_knowledge_soundness_game_def)
    also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      _ :: unit \<leftarrow> assert_spmf (G\<^sub>p.constrain_list (ck @ []) [(c, cvec)]);
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;         
      return_spmf (verify_eval vk c i (p_i,w) \<and> p_i \<noteq> p_i' \<and> valid_eval (p_i,w))       
    } ELSE return_spmf False"
      unfolding lift_\<A>1_def by simp
    also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;         
      return_spmf (verify_eval vk c i (p_i,w) \<and> p_i \<noteq> p_i' \<and> valid_eval (p_i,w))       
    } ELSE return_spmf False" 
      by simp
    also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
      return_spmf (verify_eval vk c i (p_i,w) \<and> p_i \<noteq> p_i' \<and> valid_eval (p_i,w))       
    } ELSE return_spmf False" 
      by (rule try_spmf_cong)(simp add: assert_commute)+
    also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      TRY do {
        ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
        TRY do {
          (p,td) \<leftarrow> E (c,cvec);
          TRY do {
            (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
            TRY do {
              let (p_i',w') = Eval ck td p i;
              _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
                    \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
              TRY do {
                return_spmf (verify_eval vk c i (p_i,w) \<and> p_i \<noteq> p_i' \<and> valid_eval (p_i,w)) 
              } ELSE return_spmf False    
            } ELSE return_spmf False    
          } ELSE return_spmf False    
        } ELSE return_spmf False    
      } ELSE return_spmf False    
    } ELSE return_spmf False" 
      unfolding Let_def split_def
      by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
   also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      TRY do {
        ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
        TRY do {
          (p,td) \<leftarrow> E (c,cvec);
          TRY do {
            (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
            TRY do {
              let (p_i',w') = Eval ck td p i;
              _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
                    \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
              _ :: unit \<leftarrow> assert_spmf (verify_eval vk c i (p_i,w) \<and> p_i \<noteq> p_i' \<and> valid_eval (p_i,w));
              return_spmf True   
            } ELSE return_spmf False    
          } ELSE return_spmf False    
        } ELSE return_spmf False    
      } ELSE return_spmf False    
    } ELSE return_spmf False" 
     by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
      _ :: unit \<leftarrow> assert_spmf (verify_eval vk c i (p_i,w) \<and> p_i \<noteq> p_i' \<and> valid_eval (p_i,w));
      return_spmf True
    } ELSE return_spmf False" 
    unfolding Let_def split_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
          \<and> verify_eval vk c i (p_i,w) 
          \<and> p_i \<noteq> p_i' 
          \<and> valid_eval (p_i,w));
      return_spmf True
    } ELSE return_spmf False" 
    by (simp add: assert_collapse)
  also have "\<dots> = TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
      let (\<alpha>::'e mod_ring) = of_int_mod_ring (int x);
      let ck = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let vk = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      let (p,td) = (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec),());
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
          \<and> verify_eval vk c i (p_i,w) 
          \<and> p_i \<noteq> p_i' 
          \<and> valid_eval (p_i,w));
      return_spmf True
    } ELSE return_spmf False" 
    unfolding key_gen_def Setup_def by auto
(* TODO add or remove \<and> w \<noteq> w'*)
   also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
      let (\<alpha>::'e mod_ring) = of_int_mod_ring (int x);
      let ck = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let vk = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      let (p,td) = (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec),());
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
          \<and> p_i \<noteq> p_i'
          
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w')
          \<and> verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w'));
      return_spmf True
    } ELSE return_spmf False" 
     apply(unfold spmf_rel_eq[symmetric])
     apply (rule rel_spmf_try_spmf)
      apply(unfold Let_def split_def)
      apply(rule rel_spmf_bindI[of "(=)"] | force)+
       apply(rule assert_cong)
       apply(insert ks_imp_eval_bind_asserts)
       apply(unfold Let_def split_def)
       apply simp+
     done
   also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
          \<and> p_i \<noteq> p_i'
          
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w')
          \<and> verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w'));
      return_spmf True
    } ELSE return_spmf False" 
     unfolding key_gen_def Setup_def by force
  also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf ( 
           p_i \<noteq> p_i'
          
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w')
          \<and> verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w'));
      return_spmf True
    } ELSE return_spmf False" 
    by (simp add: assert_collapse)
  also have "\<dots> = 
    TRY do {
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf ( 
           p_i \<noteq> p_i'
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w')
          \<and> verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w'));
      return_spmf True
    } ELSE return_spmf False" 
    apply (rule try_spmf_cong)
     apply simp
     apply(subst assert_commute) 
     apply blast+
    done
  also have "\<dots> = 
    TRY do {
      (ck,vk) \<leftarrow> key_gen;
      let \<A>1_AGM = lift_\<A>1 \<A>1;
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf ( 
           p_i \<noteq> p_i'
          
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w')
          \<and> verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w'));
      return_spmf True
    } ELSE return_spmf False" 
    unfolding lift_\<A>1_def by fastforce
  also have "\<dots> = 
    TRY do {
      (ck,vk) \<leftarrow> key_gen;
      let \<A>1_AGM = lift_\<A>1 \<A>1;
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf ( 
          valid_eval (p_i,w)
          \<and> p_i \<noteq> p_i'
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w')
          \<and> verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w'));
      return_spmf True
    } ELSE return_spmf False" 
    apply(unfold spmf_rel_eq[symmetric])
    apply (rule rel_spmf_try_spmf)
     apply(unfold Let_def split_def)
     apply(rule rel_spmf_bindI[of "(=)"] | force)+
      apply(rule assert_cong)
      apply force+
    done  
  also have "\<dots> = 
    TRY do {
      (ck,vk) \<leftarrow> key_gen;
      let \<A>1_AGM = lift_\<A>1 \<A>1;
      let \<A>2_AGM = lift_\<A>2 \<A>2;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, p_i, (w, wvec)) \<leftarrow> \<A>2 \<sigma>;
      _ :: unit \<leftarrow> assert_spmf ( valid_eval (p_i,w));
      let (p_i',w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf ( 
          p_i \<noteq> p_i'
          \<and> valid_eval (p_i,w)
          \<and> valid_eval (p_i', w'));
      _ :: unit \<leftarrow> assert_spmf(
          verify_eval vk c i (p_i, w) 
          \<and> verify_eval vk c i (p_i', w'));
      return_spmf True
    } ELSE return_spmf False" 
    by (simp add: assert_collapse)
  also have "\<dots> = 
    TRY do {
      (ck,vk) \<leftarrow> key_gen;
      (c, i, v, w, v', w') \<leftarrow> knowledge_soundness_reduction_ext E \<A>1 \<A>2 ck;
      _ :: unit \<leftarrow> assert_spmf ( 
          v \<noteq> v'
          \<and> valid_eval (v,w)
          \<and> valid_eval (v', w'));
      _ :: unit \<leftarrow> assert_spmf(
          verify_eval vk c i (v, w) 
          \<and> verify_eval vk c i (v', w'));
      return_spmf True
    } ELSE return_spmf False"
    unfolding knowledge_soundness_reduction_ext_def by force
  also have "\<dots> = 
    TRY do {
      (ck,vk) \<leftarrow> key_gen;
      TRY do {
        (c, i, v, w, v', w') \<leftarrow> knowledge_soundness_reduction_ext E \<A>1 \<A>2 ck;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf ( 
              v \<noteq> v'
              \<and> valid_eval (v,w)
              \<and> valid_eval (v', w'));
          TRY do {
            _ :: unit \<leftarrow> assert_spmf(
                verify_eval vk c i (v, w) 
                \<and> verify_eval vk c i (v', w'));
            return_spmf True
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding Let_def split_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = 
    TRY do {
      (ck,vk) \<leftarrow> key_gen;
      TRY do {
        (c, i, v, w, v', w') \<leftarrow> knowledge_soundness_reduction_ext E \<A>1 \<A>2 ck;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf ( 
              v \<noteq> v'
              \<and> valid_eval (v,w)
              \<and> valid_eval (v', w'));
          TRY do {
            return_spmf (verify_eval vk c i (v, w) \<and> verify_eval vk c i (v', w'))
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
   also have "\<dots> = 
    TRY do {
      (ck,vk) \<leftarrow> key_gen;
      (c, i, v, w, v', w') \<leftarrow> knowledge_soundness_reduction_ext E \<A>1 \<A>2 ck;
      _ :: unit \<leftarrow> assert_spmf ( 
          v \<noteq> v'
          \<and> valid_eval (v,w)
          \<and> valid_eval (v', w'));
      return_spmf( verify_eval vk c i (v, w) \<and> verify_eval vk c i (v', w'))
    } ELSE return_spmf False"
    unfolding Let_def split_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots> = eval_bind_game (knowledge_soundness_reduction_ext E \<A>1 \<A>2)"
    unfolding eval_bind_game_def by presburger
  finally show ?thesis .
qed 


text \<open>We overestimate the probability of winning the evaluation binding game with the extended adversary 
by winning it with the normal adversary.\<close>
lemma overestimate_reductions: "spmf (eval_bind_game (knowledge_soundness_reduction_ext E \<A> \<A>')) True 
  \<le> spmf (eval_bind_game (knowledge_soundness_reduction E \<A> \<A>')) True"
proof -
   note [simp] = Let_def split_def

   text \<open>We extend the evaluation binding game with the extended reduction adversary to a complete 
   game.\<close>
   have w_assert_ext: "eval_bind_game (knowledge_soundness_reduction_ext E \<A> \<A>') = 
    TRY do {
      (ck, vk) \<leftarrow> key_gen;
      let \<A>1_AGM = lift_\<A>1 \<A>;
      let \<A>2_AGM = lift_\<A>2 \<A>';
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, v, w, wvec) \<leftarrow> \<A>' \<sigma>;
      _ :: unit \<leftarrow> assert_spmf (valid_eval (v, w));
      let (v',w') = Eval ck td p i;     
      _ :: unit \<leftarrow> assert_spmf (v \<noteq> v' \<and> valid_eval (v, w) \<and> valid_eval (v', w'));                     
      let b = verify_eval vk c i (v,w);
      let b' = verify_eval vk c i (v',w');
      return_spmf (b \<and> b')} ELSE return_spmf False"
     unfolding eval_bind_game_def knowledge_soundness_reduction_ext_def 
     by (simp add: split_def Let_def)

   text \<open>We extend the evaluation binding game with the normal reduction adversary to a complete 
   game.\<close>
   have wo_assert_ext: "eval_bind_game (knowledge_soundness_reduction E \<A> \<A>') = 
    TRY do {
      (ck, vk) \<leftarrow> key_gen;
      let \<A>1_AGM = lift_\<A>1 \<A>;
      let \<A>2_AGM = lift_\<A>2 \<A>';
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1_AGM ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, v, w, wvec) \<leftarrow> \<A>' \<sigma>;
      let (v',w') = Eval ck td p i;     
      _ :: unit \<leftarrow> assert_spmf (v \<noteq> v' \<and> valid_eval (v, w) \<and> valid_eval (v', w'));                     
      let b = verify_eval vk c i (v,w);
      let b' = verify_eval vk c i (v',w');
      return_spmf (b \<and> b')} ELSE return_spmf False"
     unfolding eval_bind_game_def knowledge_soundness_reduction_def 
     by (simp add: split_def Let_def)

  text \<open>We show the thesis in ennreal, which implies the plain thesis\<close>
  have "ennreal (spmf (eval_bind_game (knowledge_soundness_reduction_ext E \<A> \<A>')) True) 
    \<le> ennreal (spmf (eval_bind_game (knowledge_soundness_reduction E \<A> \<A>')) True)"
    unfolding w_assert_ext wo_assert_ext
    apply (simp add: spmf_try_spmf ennreal_spmf_bind)
    apply (rule nn_integral_mono)+
    apply (simp add: assert_spmf_def)
    apply (simp add: measure_spmf.emeasure_eq_measure)
    done
  then show ?thesis by simp
qed
  
text \<open>Proof Step 6:

Finally we put everything together:
we conclude that for every efficient adversary in the AGM the advantage of winning the 
knowledge soundness game is less equal to breaking the t-SDH assumption.\<close>
(* TODO advantage in the AGM *)
theorem knowledge_soundness: 
  "spmf (AGM_knowledge_soundness_game (\<A>,\<A>') E) True
  \<le> t_SDH_G\<^sub>p.advantage (eval_bind_reduction (knowledge_soundness_reduction E \<A> \<A>'))"
  using evaluation_binding[of "knowledge_soundness_reduction E \<A> \<A>'"]
    overestimate_reductions[of \<A> \<A>']
  unfolding eval_bind_advantage_def  knowledge_soundness_game_alt_def
  by linarith

end

end
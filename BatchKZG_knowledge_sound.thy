theory BatchKZG_knowledge_sound

imports BatchKZG_eval_bind Algebraic_Group_Model
begin


text \<open>In this theory we prove knowledge soundness for the KZG, concretely the knowledge soundness 
as defined in the abstract polynomial commitment scheme. The proof is a reduction to the 
evaluation binding game which has been reduced to the t-Bilinear strong Diffie-Hellmann problem in the 
KZG_eval_bind theory.\<close>

hide_const restrict

locale BatchEvalKZG_PCS_knowledge_sound = BatchEvalKZG_PCS_eval_bind
begin 

text \<open>the AGM adversary types that are useful in defining reductions (i.e. the reduction to the 
evaluation binding game)\<close>
lift_to_algebraicT "('a ck, 'a commit, 'state) knowledge_soundness_adversary1"  "G\<^sub>p" 
  => AGM_knowledge_soundness_adversary1
lift_to_algebraicT "('state, 'a ck, 'e mod_ring, 'e evaluation, 'a witness) knowledge_soundness_adversary2" 
  "G\<^sub>p"  => AGM_knowledge_soundness_adversary2

text \<open>We adapt the knowledge soundness adversary in round 2 to the batch version. 
Concretely, we aks the adversary to give a single point $i \in I$ at which the evaluation polynomial 
$r$ is disticnt from the extractor polynomial\<close>
type_synonym ('e', 'state', 'a') knowledge_soundness_adversary2_AGM 
  = "('a' ck \<times> 'state') \<Rightarrow> ('e' mod_ring \<times> 'e' argument set \<times> ('e' batch_evaluation \<times> ('a' witness \<times> int list))) spmf"

text \<open>The extractor is an algorithm that plays against the adversary. It is granted access to the 
adversaries messages and state (which we neglect in this case as we do not need it because the 
calculation vector is enough to create sensible values) and has to come up with a polynomial such 
that the adversary cannot create valid opening points that are not part of the polynomial.\<close>
type_synonym ('a', 'e') extractor = 
  "('a' commit \<times> int list) \<Rightarrow> 
    ('e' mod_ring poly \<times> unit) spmf"

text \<open>restrict for AGM adversaries 1 & 2\<close>

interpretation AGM1: Algebraic_Algorithm G\<^sub>p "listS G\<^sub>p.groupS" "prodC G\<^sub>p.groupC noConstrain" 
  by (unfold_locales)

text \<open>"'ck' \<Rightarrow> 'state' \<Rightarrow> ('argument' \<times> ('evaluation' \<times> 'witness')) spmf"\<close>
interpretation AGM2: Algebraic_Algorithm G\<^sub>p "prodS (listS G\<^sub>p.groupS) noSelect" 
  "prodC noConstrain (prodC noConstrain (prodC noConstrain G\<^sub>p.groupC))"
  by (unfold_locales)

definition knowledge_soundness_game_AGM :: "('state, 'a) AGM_knowledge_soundness_adversary1  
  \<Rightarrow> ('e, 'state, 'a) knowledge_soundness_adversary2_AGM \<Rightarrow> ('a, 'e) extractor \<Rightarrow> bool spmf"
  where "knowledge_soundness_game_AGM \<A>1 \<A>2 \<E> = TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> AGM1.restrict \<A>1 ck;
      (p,td) \<leftarrow> \<E> (c,cvec);
      (i, I, (r, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w') = Eval ck td p i;        
      return_spmf (verify_eval_batch vk c I (r,w) \<and> poly r i \<noteq> p_i 
        \<and> valid_argument_batch I \<and> valid_eval_batch (r,w) \<and> i \<in> I)       
    } ELSE return_spmf False"

definition ks_to_eval_bind_reduction :: "('state, 'a) AGM_knowledge_soundness_adversary1  
  \<Rightarrow> ('e, 'state, 'a) knowledge_soundness_adversary2_AGM \<Rightarrow> ('a, 'e) extractor 
  \<Rightarrow> ('a, 'e)  adversary" where 
  "ks_to_eval_bind_reduction \<A>1 \<A>2 \<E> ck = do {
    ((c,cvec),\<sigma>) \<leftarrow> AGM1.restrict \<A>1 ck;
      (p,td) \<leftarrow> \<E> (c,cvec);
      (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w') = Eval ck td p i;    
      return_spmf (c,i, p_i, w', I, w, r_x)
  }"

text \<open>Extractor definition\<close>
fun E :: "('a, 'e) extractor" where 
  "E (c,cvec) = return_spmf (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec),())"

lemma reduction_map_imp: "
       let ck = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
           vk = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
           (p_i,w_i) = Eval ck td (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec)) i 
       in
        length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> verify_eval_batch vk c I (r_x,w) \<and> poly r_x i \<noteq> p_i 
        \<and> valid_argument_batch I \<and> valid_eval_batch (r_x,w) \<and> i \<in> I
  \<longrightarrow> 
        length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> i \<in> I \<and> p_i \<noteq> poly r_x i 
        \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w) 
        \<and> verify_eval vk c i (p_i, w_i)
        \<and> verify_eval_batch vk c I (r_x,w)"
proof -
    define ck where ck_def: "ck = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]"
  define vk where vk_def: "vk = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]"
  define p_i  where p_i_def: "p_i = fst (Eval ck td (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec)) i )" 
  define w_i  where w_i_def: "w_i = snd (Eval ck td (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec)) i )" 

  have "length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> verify_eval_batch vk c I (r_x,w) \<and> poly r_x i \<noteq> p_i 
        \<and> valid_argument_batch I \<and> valid_eval_batch (r_x,w) \<and> i \<in> I 
        \<longrightarrow>
          length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> i \<in> I \<and> p_i \<noteq> poly r_x i 
        \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w) 
        \<and> verify_eval vk c i (p_i, w_i)
        \<and> verify_eval_batch vk c I (r_x,w)"
  (is "?lhs \<longrightarrow> ?rhs")
  proof 
    assume asm: "?lhs"
    show "?rhs"
    proof(intro conjI)
      from asm show "length ck = length cvec" by blast
      from asm show "c = fold (\<lambda>(i::nat) acc::'a. acc \<otimes> ck ! i [^] cvec ! i) [0..<length ck] \<one>" by blast
      from asm show "i \<in> I" by blast
      from asm show " p_i \<noteq> poly r_x i" by blast
      from asm show "valid_argument_batch I" by blast
      from asm show "valid_eval_batch (r_x, w)" by blast
      from asm show "verify_eval_batch vk c I (r_x, w)" by blast
      show "valid_eval (p_i, w_i)" 
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
          by (simp add: Eval_def p_i_def w_i_def)
      qed
      show "verify_eval vk c i (p_i, w_i)" 
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
          by (metis "1" "2" 3 Eval_def ck_def vk_def p_i_def w_i_def eq_on_e fst_conv snd_conv)
      qed
    qed
  qed
  then show ?thesis 
    unfolding ck_def vk_def p_i_def w_i_def Let_def split_def
    by blast
qed


theorem ks_game_to_eval_bind_game: "spmf (knowledge_soundness_game_AGM \<A>1 \<A>2 E) True 
  \<le> spmf (bind_game (ks_to_eval_bind_reduction \<A>1 \<A>2 E)) True"
  (is "?lhs \<le> ?rhs")
proof -
  note [simp] = Let_def split_def

  have "spmf (knowledge_soundness_game_AGM \<A>1 \<A>2 E) True = spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
          \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
      (p,td) \<leftarrow> E (c,cvec);
      (i, I, (r, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w') = Eval ck td p i;        
      return_spmf (verify_eval_batch vk c I (r,w) \<and> poly r i \<noteq> p_i 
        \<and> valid_argument_batch I \<and> valid_eval_batch (r,w) \<and> i \<in> I)       
    } ELSE return_spmf False) True"
    unfolding knowledge_soundness_game_AGM_def AGM1.restrict_def listS_def G\<^sub>p.groupS_def noSelect_def 
        Restrictive_Comp.restrict_def prodC_def G\<^sub>p.groupC_def G\<^sub>p.constrain_grp_def 
        noConstrain_def
    by force
  also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      TRY do {
        ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
          TRY do {
          _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
              \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
            TRY do {
            (p,td) \<leftarrow> E (c,cvec);
              TRY do {
              (i, I, (r, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
              let (p_i,w') = Eval ck td p i;        
                TRY do {
                return_spmf (verify_eval_batch vk c I (r,w) \<and> poly r i \<noteq> p_i 
                  \<and> valid_argument_batch I \<and> valid_eval_batch (r,w) \<and> i \<in> I)    
              } ELSE return_spmf False   
            } ELSE return_spmf False
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False) True"
    unfolding Let_def split_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      TRY do {
        ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
          TRY do {
          _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
              \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
            TRY do {
            (p,td) \<leftarrow> E (c,cvec);
              TRY do {
              (i, I, (r, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
              let (p_i,w') = Eval ck td p i;   
                TRY do {
                _ :: unit \<leftarrow> assert_spmf (verify_eval_batch vk c I (r,w) \<and> poly r i \<noteq> p_i 
                  \<and> valid_argument_batch I \<and> valid_eval_batch (r,w) \<and> i \<in> I);     
                return_spmf True
              } ELSE return_spmf False
            } ELSE return_spmf False
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False) True" 
      by (rule spmf_eqI')(auto simp add:  try_bind_assert_spmf try_spmf_return_spmf1 del: Let_def split_def intro!: try_spmf_cong bind_spmf_cong)
      also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
       \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
      (p,td) \<leftarrow> E (c,cvec);
       (i, I, (r, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
       let (p_i,w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (verify_eval_batch vk c I (r,w) \<and> poly r i \<noteq> p_i 
        \<and> valid_argument_batch I \<and> valid_eval_batch (r,w) \<and> i \<in> I);     
      return_spmf True
      } ELSE return_spmf False) True"
        unfolding Let_def split_def
        by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
    also have "\<dots>= spmf(TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, I, (r, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
       \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one>);
      _ :: unit \<leftarrow> assert_spmf (verify_eval_batch vk c I (r,w) \<and> poly r i \<noteq> p_i 
        \<and> valid_argument_batch I \<and> valid_eval_batch (r,w) \<and> i \<in> I);     
      return_spmf True
      } ELSE return_spmf False) True"
      apply (rule spmf_eqI')
      apply (rule try_spmf_cong)
       apply (rule unpack_bind_spmf'; simp)+
       apply (subst assert_commute)
       apply simp+
      done
    also have "\<dots>= spmf (TRY do {
      x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
      let (\<alpha>::'e mod_ring) = of_int_mod_ring (int x);
      let ck = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let vk = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      let (p,td) = (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec),());
      (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w') = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> verify_eval_batch vk c I (r_x,w) \<and> poly r_x i \<noteq> p_i 
        \<and> valid_argument_batch I \<and> valid_eval_batch (r_x,w) \<and> i \<in> I);     
      return_spmf True
      } ELSE return_spmf False) True"
      by (simp add: key_gen_def Setup_def assert_collapse)
    also have "\<dots>\<le> spmf (TRY do {
      x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
      let (\<alpha>::'e mod_ring) = of_int_mod_ring (int x);
      let ck = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      let vk = map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1];
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      let (p,td) = (Poly (map (of_int_mod_ring::int \<Rightarrow>'e mod_ring) cvec),());
      (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w_i) = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> i \<in> I \<and> p_i \<noteq> poly r_x i 
        \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w) 
        \<and> verify_eval vk c i (p_i, w_i)
        \<and> verify_eval_batch vk c I (r_x,w));     
      return_spmf True
      } ELSE return_spmf False) True"
      unfolding E.simps key_gen_def Setup_def
      apply (rule try_spmf_le)
      apply (unfold Let_def split_def)
      apply (rule bind_spmf_le)+
      apply (rule assert_imp)
      apply (insert reduction_map_imp)
      apply(unfold Let_def split_def)
      apply (intro impI)
      apply simp
      apply force
      done
    also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w_i) = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> i \<in> I \<and> p_i \<noteq> poly r_x i 
        \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w) 
        \<and> verify_eval vk c i (p_i, w_i)
        \<and> verify_eval_batch vk c I (r_x,w));     
      return_spmf True
      } ELSE return_spmf False) True"
      by (simp add: key_gen_def Setup_def assert_collapse)
    also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w_i) = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> i \<in> I \<and> p_i \<noteq> poly r_x i 
        \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w));
      _::unit \<leftarrow> assert_spmf (verify_eval vk c i (p_i, w_i)
        \<and> verify_eval_batch vk c I (r_x,w));     
      return_spmf True
      } ELSE return_spmf False) True"
      by (simp add: assert_collapse)
    also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
        TRY do {
        ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
          TRY do {
          (p,td) \<leftarrow> E (c,cvec);
            TRY do{
            (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
              TRY do{
              let (p_i,w_i) = Eval ck td p i;
              _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> i \<in> I \<and> p_i \<noteq> poly r_x i 
                \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w));
                TRY do {
                _::unit \<leftarrow> assert_spmf (verify_eval vk c i (p_i, w_i)
                  \<and> verify_eval_batch vk c I (r_x,w));     
                return_spmf True
                } ELSE return_spmf False
              } ELSE return_spmf False
            } ELSE return_spmf False
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False) True"
      unfolding Let_def split_def
      by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
    also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
        TRY do {
        ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
          TRY do {
          (p,td) \<leftarrow> E (c,cvec);
            TRY do{
            (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
              TRY do{
              let (p_i,w_i) = Eval ck td p i;
              _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
                \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
                \<and> i \<in> I \<and> p_i \<noteq> poly r_x i 
                \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w));
                TRY do {
                return_spmf (verify_eval vk c i (p_i, w_i)
                  \<and> verify_eval_batch vk c I (r_x,w))
                } ELSE return_spmf False
              } ELSE return_spmf False
            } ELSE return_spmf False
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False) True"
      by (rule spmf_eqI')(auto simp add:  try_bind_assert_spmf try_spmf_return_spmf1 del: Let_def split_def intro!: try_spmf_cong bind_spmf_cong)
    also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w_i) = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> 
        \<and> i \<in> I \<and> p_i \<noteq> poly r_x i 
        \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w));
      return_spmf (verify_eval vk c i (p_i, w_i)
        \<and> verify_eval_batch vk c I (r_x,w))
      } ELSE return_spmf False) True"
    unfolding Let_def split_def
    by (fold try_bind_spmf_lossless2[OF lossless_return_spmf])simp
  also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      (p,td) \<leftarrow> E (c,cvec);
      (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w_i) = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> );
      _ :: unit \<leftarrow> assert_spmf (i \<in> I \<and> p_i \<noteq> poly r_x i 
        \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w));
      return_spmf (verify_eval vk c i (p_i, w_i)
        \<and> verify_eval_batch vk c I (r_x,w))
      } ELSE return_spmf False) True"
    by (simp add: assert_collapse)
    also have "\<dots>= spmf (TRY do {
      (ck,vk) \<leftarrow> key_gen;
      ((c,cvec),\<sigma>) \<leftarrow> \<A>1 ck;
      _ :: unit \<leftarrow> assert_spmf (length ck = length cvec 
        \<and> c = fold (\<lambda> i acc. acc \<otimes> ck!i [^] (cvec!i)) [0..<length ck] \<one> );
      (p,td) \<leftarrow> E (c,cvec);
      (i, I, (r_x, (w, wvec))) \<leftarrow> AGM2.restrict \<A>2 (ck,\<sigma>);
      let (p_i,w_i) = Eval ck td p i;
      _ :: unit \<leftarrow> assert_spmf (i \<in> I \<and> p_i \<noteq> poly r_x i 
        \<and> valid_argument_batch I \<and> valid_eval (p_i, w_i) \<and> valid_eval_batch (r_x, w));
      return_spmf (verify_eval vk c i (p_i, w_i)
        \<and> verify_eval_batch vk c I (r_x,w))
      } ELSE return_spmf False) True"
      apply (rule spmf_eqI')
      apply (unfold Let_def split_def)
      apply (simp split: prod.split)
      apply (rule unpack_try_spmf)
      apply (rule unpack_bind_spmf'; rule ext)+
      apply (subst assert_commute)
      apply (subst assert_commute)
      apply blast
      done
  also have "\<dots> \<le> spmf (bind_game (ks_to_eval_bind_reduction \<A>1 \<A>2 E)) True"
    unfolding bind_game_def ks_to_eval_bind_reduction_def
    unfolding knowledge_soundness_game_AGM_def AGM1.restrict_def listS_def G\<^sub>p.groupS_def noSelect_def 
        Restrictive_Comp.restrict_def prodC_def G\<^sub>p.groupC_def G\<^sub>p.constrain_grp_def 
        noConstrain_def split_def Let_def
    by force
  finally show ?thesis .
qed

text \<open>Finally we put everything together:
we conclude that for every efficient adversary in the AGM the advantage of winning the 
knowledge soundness game is less equal to breaking the t-BSDH assumption.\<close>
theorem knowledge_soundness: 
  "spmf (knowledge_soundness_game_AGM \<A>1 \<A>2 E) True 
  \<le> t_BSDH.advantage (reduction (ks_to_eval_bind_reduction \<A>1 \<A>2 E))"
  using  ks_game_to_eval_bind_game
  using evaluation_binding[of "ks_to_eval_bind_reduction \<A>1 \<A>2 E"]
  unfolding bind_advantage_def
  using landau_o.R_trans by blast

end

end
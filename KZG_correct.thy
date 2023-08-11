theory KZG_correct

imports KZG_Def

begin

locale KZG_correct = KZG_Def
begin

subsection \<open>
Verifying that a correct Setup with a correct commit yields a correct verification\<close>

definition Poly_Commit_game:: "nat \<Rightarrow>'e polynomial \<Rightarrow> bool spmf"
  where "Poly_Commit_game t \<phi> = 
    do{
    (\<alpha>,PK) \<leftarrow> Setup t;
    C::'a commit \<leftarrow> Commit PK \<phi>;
    VerifyPoly PK C \<phi>
    }"

lemma lossless_Setup: "lossless_spmf (Setup t)"
  unfolding Setup_def 
  by (metis (no_types, lifting) G\<^sub>p.order_gt_0 lossless_bind_spmf lossless_return_spmf lossless_sample_uniform)

theorem Poly_Commit_correct:  
  assumes t_ge_2: "t\<ge>2"
  and deg_\<phi>_let: "degree (of_qr \<phi>) \<le> t"
shows "spmf (Poly_Commit_game t \<phi>) True = 1"
proof -
  note [simp] = Let_def split_def
  have weight_Setup: "weight_spmf (Setup t) = 1" using lossless_spmf_def lossless_Setup by fast
  have "(Poly_Commit_game t \<phi>) = 
   do{
    (\<alpha>,PK) \<leftarrow> Setup t;
    return_spmf True
    }"
  unfolding Poly_Commit_game_def Commit_def VerifyPoly_def by force
  also have "\<dots> = scale_spmf (weight_spmf (Setup t)) (return_spmf True)"
    by (simp add:split_def)(rule bind_spmf_const)
  also have "\<dots> = return_spmf True" using weight_Setup by force
  finally show ?thesis by fastforce
qed

definition Eval_Commit_game:: "nat \<Rightarrow>'e polynomial \<Rightarrow> 'e eval_position  \<Rightarrow> bool spmf"
  where "Eval_Commit_game t \<phi> i = 
    do{
    (\<alpha>,PK) \<leftarrow> Setup t;
    C::'a commit \<leftarrow> Commit PK \<phi>;
    (i, \<phi>_of_i, w_i) \<leftarrow> CreateWitness PK \<phi> i;
    VerifyEval PK C i \<phi>_of_i w_i
    }"

theorem Eval_Commit_correct:  
  assumes t_ge_2: "t\<ge>2"
  and deg_\<phi>_let: "degree (of_qr \<phi>) \<le> t"
shows "spmf (Eval_Commit_game t \<phi> i) = 1"
  sorry

end

end
theory BatchKZG_poly_bind

imports BatchKZG_Def KZG_poly_bind

begin

locale BatchEvalKZG_PCS_poly_bind = BatchEvalKZG + KZG_CS_binding
begin

text \<open>We inherit polynomial binding for the batched KZG directly from the standard KZG.\<close>
theorem "bKZG.poly_bind_advantage \<A> \<le> t_DL_G\<^sub>p.advantage (bind_reduction \<A>)"
  using polynomial_binding by blast

end

end
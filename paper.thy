(*<*)
theory paper
  imports "Regular-Sets.Regexp_Method"
begin
(*>*)

text\<open>Testing: @{thm Regular_Set.Arden}\<close>

lemma "S O (S O S^* O R^* \<union> R^* ) \<subseteq> S O S^* O R^*"
  by regexp

section \<open>Usage of functional data structures\<close>(*Todo?*)

lemma
  assumes "\<And>A B. R A B \<Longrightarrow> [] \<in> A \<longleftrightarrow> [] \<in> B"
  assumes "\<And>A B x. R A B \<Longrightarrow> R (Deriv x A) (Deriv x B)"
  assumes "R A B"
  shows "A = B"
  using assms(1) assms(2) assms(3) language_coinduct by blast

(*<*)
end
(*>*)
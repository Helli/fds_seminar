(*<*)
theory paper
  imports "Regular-Sets.Regexp_Method"
  "HOL-Library.Char_ord"
  "HOL-Eisbach.Eisbach"
begin
(*>*)

text\<open>Testing: @{thm Regular_Set.Arden}\<close>
thm Regular_Set.Arden

section\<open>Polymorphic method for standard-@{type rexp}\<close>

definition check_eqv :: "'a :: order rexp \<Rightarrow> 'a rexp \<Rightarrow> bool" where
"check_eqv r s =
  (let nr = NDerivative.norm r; ns = NDerivative.norm s; as = Equivalence_Checking.add_atoms nr (Equivalence_Checking.add_atoms ns [])
   in case Equivalence_Checking.closure as (nr, ns) of
     Some([],_) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma soundness: 
assumes "check_eqv r s" shows "lang r = lang s"
proof -
  let ?nr = "NDerivative.norm r" let ?ns = "NDerivative.norm s"
  let ?as = "Equivalence_Checking.add_atoms ?nr (Equivalence_Checking.add_atoms ?ns [])"
  obtain R where 1: "Equivalence_Checking.closure ?as (?nr,?ns) = Some([],R)"
    using assms by (auto simp: check_eqv_def Let_def split:option.splits list.splits)
  then have "lang (NDerivative.norm r) = lang (NDerivative.norm s)"
    by (rule Equivalence_Checking.closure_sound) (auto simp: set_add_atoms dest!: subsetD[OF atoms_norm])
  thus "lang r = lang s" by simp
qed

text\<open>Test:\<close>
lemma "check_eqv (Plus One (Times (Atom (0::nat)) (Star(Atom 0)))) (Star(Atom 0))"
  by eval

method rexp = rule soundness, eval

lemma
  assumes "\<And>A B. R A B \<Longrightarrow> [] \<in> A \<longleftrightarrow> [] \<in> B"
  assumes "\<And>A B x. R A B \<Longrightarrow> R (Deriv x A) (Deriv x B)"
  assumes "R A B"
  shows "A = B"
  using assms(1) assms(2) assms(3) language_coinduct by blast

value "NDerivative.norm (Atom (CHR ''a''))"

paragraph \<open>Minimal example for a strictly partial order\<close>
datatype part_ord = A | B

instantiation part_ord :: order
begin

definition "a \<le> b \<longleftrightarrow> a = b" for a b :: part_ord
definition "a < b \<longleftrightarrow> False" for a b :: part_ord

instance
  by standard (simp_all add: less_eq_part_ord_def less_part_ord_def)
end

abbreviation "AB \<equiv> Times (Atom A) (Atom B)"
abbreviation "A_or_B \<equiv> Plus (Atom A) (Atom B)"

text\<open>Trying to get a nontermination:\<close>
lemma "lang (Times (Star (Plus (Atom B) AB)) A_or_B) = lang (Times (Star (Plus AB (Atom B))) A_or_B)"
  apply rexp
  done

abbreviation "a \<equiv> CHR ''a''"
abbreviation "b \<equiv> CHR ''b''"

value "NDerivative.norm (Plus (Atom B) (Atom A))"

section \<open>Usage of functional data structures\<close>(*Todo?*)

(*<*)
end
(*>*)
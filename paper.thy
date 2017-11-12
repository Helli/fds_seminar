(*<*)
theory paper
  imports "Regular-Sets.Regexp_Method"
  "HOL-Library.Char_ord"
  "HOL-Eisbach.Eisbach"
begin
(*>*)

declare[[names_short]]

section\<open>Overview\<close>

text\<open>Consider the following lemma, which is proven by word-length induction:
@{thm [names_short] language_coinduct}
Thus, we can obtain an equivalence proof by establishing such a relation \<open>\<sim>\<close> (called \<open>bisimulation\<close>).\<close>

text\<open>Remember that relations are just sets of pairs. Our method will incrementally add language
  pairs (represented by increasingly complex regular expressions), maintaining the relation's
  bisimulation property. Once the examined regexes are added, equivalence for them is shown.\<close>

section\<open>Nullability\<close>

thm nullable_iff
text \<open>@{thm nullable.simps}\<close>
text \<open>If \<open>R\<close> is a bisimulation, for every pair \<open>(A,B)\<close>, \<open>A\<close> and \<open>B\<close> agree on nullability: @{thm
  language_coinduct[of R "lang r1" "lang l2", folded nullable_iff]}.
@{thm is_bisimulation_def}\<close>

section\<open>ACI-normalization\<close>

text\<open>@{const NDerivative.nTimes} and @{const NDerivative.nPlus} are part of @{const
  NDerivative.norm}, working on already @{const NDerivative.norm}ed subterms.\<close>

text\<open>We only need \<open>\<subseteq>\<close> in the lemma @{thm atoms_nTimes}. Without the extra simplification in @{const
  NDerivative.nTimes}, we could prove \<open>=\<close>.\<close>

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

paragraph \<open>Small example for a strictly partial order\<close>
datatype part_ord = A | B | C

instantiation part_ord :: order
begin

definition "a \<le> b \<longleftrightarrow> a = b" for a b :: part_ord
definition "a < b \<longleftrightarrow> False" for a b :: part_ord

instance
  by standard (simp_all add: less_eq_part_ord_def less_part_ord_def)
end

abbreviation "AB \<equiv> Times (Atom A) (Atom B)"
abbreviation "A_or_B \<equiv> Plus (Atom A) (Atom B)"
abbreviation "B_or_A \<equiv> Plus (Atom B) (Atom A)"
abbreviation "r \<equiv> Plus AB (Plus (Star B_or_A) (Star A_or_B))"
abbreviation "s \<equiv> Plus (Plus (Star AB) (Star A_or_B)) B_or_A"

text\<open>Trying to get a nontermination / false negative:\<close>
lemma "lang (Times (Star (Plus (Atom B) AB)) A_or_B) = lang (Times (Star (Plus AB (Atom B))) A_or_B)"
  apply rexp
  done

lemma size_nPlus: "size (NDerivative.nPlus R1 R2) \<le> size R1 + size R2 + 1"
  apply (induction rule: NDerivative.nPlus.induct)
                      apply auto
  done

lemma size_nTimes: "size (NDerivative.nTimes R1 R2) \<le> size R1 + size R2 + 1"
  apply (induction rule: NDerivative.nTimes.induct) apply auto
  done

lemma size_norm: "size (NDerivative.norm R) \<le> size R"
proof (induction R, simp_all)
  fix R1 :: "'a rexp" and R2 :: "'a rexp"
  assume "size (NDerivative.norm R1) \<le> size R1" "size (NDerivative.norm R2) \<le> size R2"
  then have "1 + (size (NDerivative.norm R1) + size (NDerivative.norm R2)) \<le> Suc (size R1 + size R2)"
    using add_le_mono by presburger
  then show
    "size (NDerivative.nPlus (NDerivative.norm R1) (NDerivative.norm R2)) \<le> Suc (size R1 + size R2)"
    "size (NDerivative.nTimes (NDerivative.norm R1) (NDerivative.norm R2)) \<le> Suc (size R1 + size R2)"
    using size_nPlus size_nTimes by (metis (no_types)
        Orderings.order_class.dual_order.trans semiring_normalization_rules(24))+
qed

lemma "finite b1 \<Longrightarrow> finite {R . atoms R \<subseteq> b1 \<and> size R \<le> b2}"
  oops

lemma "finite {(NDerivative.norm ^^ k) R | k . True}"
proof -
  have "atoms ((NDerivative.norm ^^ k) R) \<subseteq> atoms R" for k
    apply (induction k)
     apply simp
    using atoms_norm by auto
  moreover have "size ((NDerivative.norm ^^ k) R) \<le> size R" for k
    apply (induction k)
    apply auto
    using le_trans size_norm by blast
  ultimately
  show ?thesis oops

value "(NDerivative.norm ^^ 1) r"
value "(NDerivative.norm ^^ 2) r"
value "(NDerivative.norm ^^ 3) r"
value "(NDerivative.norm ^^ 4) r"
value "(NDerivative.norm ^^ 5) r"

value "(NDerivative.norm ^^ 1) s"
value "(NDerivative.norm ^^ 2) s"
value "(NDerivative.norm ^^ 3) s"
value "(NDerivative.norm ^^ 4) s"
value "(NDerivative.norm ^^ 5) s"

value "let
    nr = NDerivative.norm r;
    ns = NDerivative.norm s;
    as = Equivalence_Checking.add_atoms nr (Equivalence_Checking.add_atoms ns [])
  in Equivalence_Checking.closure as (nr, ns)"

lemma "lang r = lang s"
  apply rexp
  done

lemma "lang (Star (Atom A)) \<noteq> lang (Star (Atom B))"
  oops

section \<open>Usage of functional data structures\<close>(*Todo?*)

text\<open>The test @{term "p \<in> set ps'"} could be sped up maybe...\<close>

text\<open>For now, the implementation uses lists.\<close>

section \<open>Usage in Relation Algebras\<close>

text \<open>Maybe relevant if relations are represented by some functional data structure?\<close>

text \<open>The "reflection"-technique is kinda cool.\<close>



(*<*)
end
(*>*)
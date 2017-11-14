(*<*)
theory paper
  imports "Regular-Sets.Regexp_Method"
  "HOL-Library.Char_ord"
  "HOL-Eisbach.Eisbach"
begin

alias nTimes = NDerivative.nTimes
alias nPlus = NDerivative.nPlus
alias norm = NDerivative.norm
alias add_atoms = Equivalence_Checking.add_atoms
alias closure = Equivalence_Checking.closure
(*>*)

text\<open>The problem of equivalence between regular expressions is decidable. The simplest proof of this
is also the only algorithm most textbooks teach: Convert both expressions into automata,
 determinize and minimize the result and check for equality (disregarding state identifiers). However, while
 this approach's correctness is obvious for CS graduates, verifying it is tedious, mostly because
 the formalization of automata theory requires a lot of notational overhead. Nipkow's paper @{cite
 "Krauss-Nipkow-JAR"} follows an alternative approach due to Brzozowski@{cite Brzozowski}. The
 development results in a ready-to-use proof method@{cite "Regular-Sets-AFP"} in Isabelle/HOL.
\<close>

section\<open>Proof pearls\<close>
text\<open>Not so often, experts publish articles so polished and clear, that they are called \<^emph>\<open>Proof
 pearl\<close>.
The proof should be purposeful, and shorter than expected. The author references the work of Braibant and
 Pous@{cite Braibant2010}, whose verified equivalence checker is more efficient, but very complex in the derivation.
 The paper's strength is that it comletely? ignores standard textbook-methods and finds inspiration
 instead in the Brzozowski's paper@{cite "Brzozowski"}, which fits perfectly into the world of
 interactive theorem proving due to its simplicity.
\<close>

subsection\<open>Simplicity\<close>
text\<open>Simplicity is of utmost importance for Isabelle: Not only are small, elegant proofs faster to
 re-run themselves (AFP is run several times a day to test conformance to the Isabelle development version),
  also the prover process does not need to load a huge chunk of code whenever it encounters a usage
 of the proof method: As we see later, we can shift the entire computation to the @{method eval}
 method, which probably resides in fast memory anyways during a lengthy build process.
\<close>

declare[[names_short]]

section\<open>Introduction\<close>

text\<open>The purpose of the article@{cite "Krauss-Nipkow-JAR"} is to provide a new proof method for
  Isabelle/HOL. Users should not have to prove equivalence relations of regular expressions
  themselves, but use a simple automatic command, saving time and work load. Ideally, this command should
 verify every correct equivalence, i.e. be complete (we don' worry about \<^bold>\<open>in\<close>equalities). However, as Nipkow
 writes, completeness "merely lets you sleep better". The reason is that proof methods are usually
 used interactively, and for small goals, meaning that a user can just \<^emph>\<open>try\<close> whether it solves the
 goal. He still argues why this works in most cases, but does not verify it.

\<close>

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

text\<open>Regular expressions \<open>r1\<close> and \<open>r2\<close> are \<^emph>\<open>ACI-equivalent\<close>@{cite "Krauss-Nipkow-JAR"} /
 \<^emph>\<open>similar\<close>@{cite Brzozowski}, if one can be transformed into the other using only the follwing
  rules:\<close>
lemma
  "lang (Plus (Plus A B) C) = lang (Plus A (Plus B C))" --\<open>\<^bold>\<open>A\<close>ssociativity\<close>
  "lang (Plus A B) = lang (Plus B A)"                   --\<open>\<^bold>\<open>C\<close>ommutativity\<close>
  "lang (Plus A A) = lang A"                            --\<open>\<^bold>\<open>I\<close>dempotence\<close>
  by auto

text\<open>@{const nTimes} and @{const nPlus} are part of @{const
  norm}, working on already @{const norm}ed subterms.\<close>

text\<open>We only need \<open>\<subseteq>\<close> in the lemma @{thm atoms_nTimes}. Without the extra simplification in @{const
  nTimes}, we could prove \<open>=\<close>.\<close>

section\<open>Main loop\<close>

subsection\<open>Usage of @{const while_option}\<close>

text\<open>For purposes of the Logic (HOL being a logic of total functions) @{const while_option} always
 has a value associated with it: If no number of iterations falsifies the while-condition, this is
 @{const None}. However, the code generator is set up to only use the unfolding equation @{thm
 while_option_unfold}, meaning it works just like an imperative \<^emph>\<open>while\<close> would.

A specialisation for computing the transitive closure (which is exactly what we want) is already
  available in @{theory While_Combinator} as @{const rtrancl_while}, which operates 
\<close>

section\<open>Polymorphic method for standard-@{type rexp}\<close>

text\<open>This following lemma and definition are copied from @{theory Equivalence_Checking}, with @{typ
  nat} replaced by @{typ "'a::order"}.\<close>
definition check_eqv :: "'a :: order rexp \<Rightarrow> 'a rexp \<Rightarrow> bool" where
"check_eqv r s =
  (let nr = norm r; ns = norm s; as = add_atoms nr
 (add_atoms ns [])
   in case closure as (nr, ns) of
     Some([],_) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma soundness: 
assumes "check_eqv r s" shows "lang r = lang s"
proof -
  let ?nr = "norm r" let ?ns = "norm s"
  let ?as = "add_atoms ?nr (add_atoms ?ns [])"
  obtain R where 1: "closure ?as (?nr,?ns) = Some([],R)"
    using assms by (auto simp: check_eqv_def Let_def split:option.splits list.splits)
  then have "lang (norm r) = lang (norm s)"
    by (rule closure_sound) (auto simp: set_add_atoms dest!: subsetD[OF atoms_norm])
  thus "lang r = lang s" by simp
qed

method rexp = rule soundness, eval

section\<open>Testing the limits\<close>

text\<open>B\<close>

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

lemma size_nPlus: "size (nPlus R1 R2) \<le> size R1 + size R2 + 1"
  apply (induction rule: nPlus.induct)
                      apply auto
  done

lemma size_nTimes: "size (nTimes R1 R2) \<le> size R1 + size R2 + 1"
  apply (induction rule: nTimes.induct)
                      apply auto
  done

lemma size_norm: "size (norm R) \<le> size R"
proof (induction R, simp_all)
  fix R1 :: "'a rexp" and R2 :: "'a rexp"
  assume "size (norm R1) \<le> size R1" "size (norm R2) \<le> size R2"
  then have "1 + (size (norm R1) + size (norm R2)) \<le> Suc (size R1 + size R2)"
    using add_le_mono by presburger
  then show
    "size (nPlus (norm R1) (norm R2)) \<le> Suc (size R1 + size R2)"
    "size (nTimes (norm R1) (norm R2)) \<le> Suc (size R1 + size R2)"
    using size_nPlus size_nTimes by (metis (no_types)
        Orderings.order_class.dual_order.trans semiring_normalization_rules(24))+
qed

lemma "finite b1 \<Longrightarrow> finite {R . atoms R \<subseteq> b1 \<and> size R \<le> b2}"
  oops

lemma "finite {(norm ^^ k) R | k . True}"
proof -
  have "atoms ((norm ^^ k) R) \<subseteq> atoms R" for k
    apply (induction k)
     apply simp
    using atoms_norm by auto
  moreover have "size ((norm ^^ k) R) \<le> size R" for k
    apply (induction k)
    apply auto
    using le_trans size_norm by blast
  ultimately
  show ?thesis oops

value "(norm ^^ 1) r"
value "(norm ^^ 2) r"
value "(norm ^^ 3) r"
value "(norm ^^ 4) r"
value "(norm ^^ 5) r"

value "(norm ^^ 1) s"
value "(norm ^^ 2) s"
value "(norm ^^ 3) s"
value "(norm ^^ 4) s"
value "(norm ^^ 5) s"

value "let
    nr = norm r;
    ns = norm s;
    as = add_atoms nr (add_atoms ns [])
  in closure as (nr, ns)"

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
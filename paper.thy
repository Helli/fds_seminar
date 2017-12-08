(*<*)
theory paper
  imports 
  (*"Regular-Sets.Equivalence_Checking2"*)
  "Regular-Sets.Regexp_Method"
  "HOL-Library.Char_ord"
  "HOL-Eisbach.Eisbach"
begin

alias nTimes = NDerivative.nTimes
alias nPlus = NDerivative.nPlus
alias norm = NDerivative.norm
alias add_atoms = Equivalence_Checking.add_atoms
alias closure = Equivalence_Checking.closure
alias nullable = Regular_Exp.nullable

declare[[names_short]]
(*>*)

section\<open>Introduction\<close>
text\<open>Two regular expressions (RE for short) are \<^emph>\<open>equivalent\<close>, if and only if they represent the
 same formal language, i.e.

  @{prop "lang r1 = lang r2"}

A well-known result from theoretical CS is that the problem of RE equivalence is decidable, meaning
that solving goals of the above form can be reduced to a mere computation. Thus, structured proofs
 often do not add understanding; they should be replaced by a simple proof method invocation,
 increasing readability and maintainability.

To prove decidability, most textbooks give this algorithm: Convert both REs into automata,
 determinise and minimise the result and check for equality (disregarding state identifiers).
 However, while correctness of this approach is obvious for CS graduates, verifying it is tedious,
 mostly because the formalization of all the needed automata theory requires a lot of work. Nipkow
 and Krauss @{cite "Krauss-Nipkow-JAR"} follow an alternative approach first described by Brzozowski
 @{cite Brzozowski}. The development results in a ready-to-use proof method @{cite
 "Regular-Sets-AFP"} in Isabelle/HOL, replacing the need for manual derivation of RE equivalences.

  This paper explains this approach, and how it is implemented as of AFP2017 (@{url
 "https://www.isa-afp.org"}). It hopes to give insight why such a succinct development (compared to
 other verified RE equivalent checkers) is beautiful and desirable for interactive proving.
\<close>

section\<open>About the reference article\<close>

text\<open>The purpose of the article @{cite "Krauss-Nipkow-JAR"} is to provide a new proof method for
  Isabelle/HOL. Users should not have to prove equivalence relations of REs
  themselves, but use a simple automatic command, saving time and work load. Ideally, this command should
 verify every correct equivalence, i.e. be complete. However, as the authors write, completeness
 "merely lets you sleep better".They still argue why completeness holds (following a proof by
 Brzozowski @{cite "Brzozowski"}), but do not verify it. The reason is that proof methods are usually
 used interactively, and for small goals, meaning that a user can just \<^emph>\<open>try\<close> whether it solves the
 goal.

\<close>

subsection\<open>What \<^emph>\<open>is\<close> in the article\<close>
text\<open>
\<^item> a proof method for RE equivalences, i.e. goals of the form
  \<open>lang r1 = lang r2\<close>; ...
\<^item> ...using the rule @{prop \<open>lang r1 \<subseteq> lang r2 \<longleftrightarrow> lang (Plus r1 r2) = lang r2\<close>}, also
  for \<open>lang r1 \<subseteq> lang r2\<close> (or \<open>lang r1 \<supseteq> lang r2\<close>)
\<close>
subsection\<open>What \<^emph>\<open>is not\<close> in the article\<close>
text\<open>
\<^item> verified termination proofs for any of the above
\<^item> a proof method for RE \<^emph>\<open>in\<close>equalities, i.e. goals of the form \<open>lang r1 \<noteq> lang r2\<close>
\<close>

section\<open>Languages and REs\<close>

subsection\<open>Notation\<close>

text\<open>
In Isabelle, list syntax is used for word operations:
\<close>
type_synonym 'a lang = "'a list set"  \<comment>\<open>Languages are sets of lists.\<close>
text\<open>@{term_type lang} is defined as usual.

For REs, we have the identifiers

@{const Zero} for the RE with @{thm Regular_Exp.lang.simps(1)} and

@{const One} for the RE with @{thm Regular_Exp.lang.simps(2)}

...referencing their properties in the corresponding Kleene algebra.
Special syntax is completely avoided: All connectives are represented
 with standard constructors:
  \<^descr>@{term_type Atom}
  \<^descr>@{term_type Plus}
  \<^descr>@{term_type Times}
  \<^descr>@{term_type Star}
\<close>

subsection\<open>Derivatives\<close>
text\<open>Remember the standard definition of a \<^emph>\<open>language derivative\<close> with respect to an atom \<open>x\<close>:

@{thm Deriv_def[no_vars]}

As the derivative of a regular language is regular again, we know that a RE
 describing it exists.

In his 1964 article \<^emph>\<open>Derivatives of Regular Expressions\<close> @{cite "Brzozowski"}, Brzozowski gives
 rules to construct it from a RE describing the original language:
\<close>
fun deriv :: "'a \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "deriv _ Zero = Zero"
| "deriv _ One = Zero"
| "deriv a (Atom b) = (if a = b then One else Zero)"
| "deriv a (Plus r s) = Plus (deriv a r) (deriv a s)"
| "deriv a (Times r s) =
    (let r's = Times (deriv a r) s
     in if nullable r then Plus r's (deriv a s) else r's)"
| "deriv a (Star r) = Times (deriv a r) (Star r)"

text\<open>...where @{const nullable}, defined as \<open>nullable r \<longleftrightarrow> [] \<in> lang r\<close>, is computable as well
  (omitted here).\<close>

lemma lang_deriv: "lang (deriv a r) = Deriv a (lang r)"
by (induction r) (auto simp: Let_def nullable_iff)

section\<open>Bisimulations\<close>

subsection\<open>Language Coinduction\<close>
text\<open>Consider the following lemma, which is proven by word induction (i.e. list induction):
\<close>
lemma language_coinduct:
assumes "\<And>K L. R K L \<Longrightarrow> ([] \<in> K \<longleftrightarrow> [] \<in> L)"
assumes "\<And>K L x. R K L \<Longrightarrow> R (Deriv x K) (Deriv x L)"
assumes "R K\<^sub>0 L\<^sub>0"
shows "K\<^sub>0 = L\<^sub>0"
proof (rule set_eqI)
  fix w
  show "w \<in> K\<^sub>0 \<longleftrightarrow> w \<in> L\<^sub>0" using assms
    apply (induction w arbitrary: K\<^sub>0 L\<^sub>0)
     apply (auto simp: Deriv_def)
     apply blast+
    done
qed
text\<open>Thus, we can obtain an equivalence proof by establishing such a relation \<open>R\<close> (called
 \<^emph>\<open>bisimulation\<close>).
\<close>
subsection\<open>Computable variant\<close>
text\<open>The following is the same for @{typ "'a rexp"} instead of languages themselves. Note that we
 also switch to set-bounded quantification (property 1 below), to make this computable for finite \<open>as\<close> (we later set
 \<open>as = atoms r1 \<union> atoms r2\<close>).
\<close>
definition is_bisimulation ::  "'a::order list \<Rightarrow> ('a rexp \<times> 'a rexp) set \<Rightarrow> bool"
where
  "is_bisimulation as R \<longleftrightarrow>
    (\<forall>(r,s)\<in> R.
(*1*) atoms r \<union> atoms s \<subseteq> set as \<and>
(*2*) (nullable r \<longleftrightarrow> nullable s) \<and>
(*3*) (\<forall>a\<in>set as. (nderiv a r, nderiv a s) \<in> R))"
text\<open>@{const nderiv} is a variant of @{const deriv}, explained later.\<close>
lemma bisim_lang_eq:
assumes "is_bisimulation as ps"
assumes "(r, s) \<in> ps"
shows "lang r = lang s"
proof -
  \<comment>\<open>This can easily be reduced to the above result.\<close>
(*<*)
  define ps' where "ps' = insert (Zero, Zero) ps"
  from \<open>is_bisimulation as ps\<close> have bisim': "is_bisimulation as ps'"
    by (auto simp: ps'_def is_bisimulation_def)
  let ?R = "\<lambda>K L. (\<exists>(r,s)\<in>ps'. K = lang r \<and> L = lang s)"
  show ?thesis
  proof (rule language_coinduct[where R="?R"])
    from \<open>(r, s) \<in> ps\<close> 
    have "(r, s) \<in> ps'" by (auto simp: ps'_def)
    thus "?R (lang r) (lang s)" by auto
  next
    fix K L assume "?R K L"
    then obtain r s where rs: "(r, s) \<in> ps'"
      and KL: "K = lang r" "L = lang s" by auto
    with bisim' have "nullable r \<longleftrightarrow> nullable s"
      by (auto simp: is_bisimulation_def)
    thus "[] \<in> K \<longleftrightarrow> [] \<in> L" by (auto simp: nullable_iff KL)
    fix a
    show "?R (Deriv a K) (Deriv a L)"
    proof cases
      assume "a \<in> set as"
      with rs bisim'
      have "(nderiv a r, nderiv a s) \<in> ps'"
        by (auto simp: is_bisimulation_def)
      thus ?thesis by (force simp: KL lang_nderiv)
    next
      assume "a \<notin> set as"
      with bisim' rs
      have "a \<notin> atoms r" "a \<notin> atoms s" by (auto simp: is_bisimulation_def)
      then have "nderiv a r = Zero" "nderiv a s = Zero"
        by (auto intro: deriv_no_occurrence)
      then have "Deriv a K = lang Zero" 
        "Deriv a L = lang Zero" 
        unfolding KL lang_nderiv[symmetric] by auto
      thus ?thesis by (auto simp: ps'_def)
    qed
  qed
qed
(*>*)

text\<open>At this point, we already have a certificate checker: Given \<open>as\<close> and \<open>ps\<close>, it iterates over
 all RE-pairs in \<open>ps\<close> and test whether they satisfy property 1,2 and 3 (3 needs another iteration
 over \<open>as\<close>).
Isabelle's proof method @{method eval} performs this without further setup:\<close>

abbreviation "a \<equiv> Atom CHR ''a''"

lemma "is_bisimulation [CHR ''a''] {
        (Zero, Zero),
        (One, One),
        (a, a),
        (Times a a, Times a a),
        (Times a (Times a a), Times (Times a a) a)
        }"
  by eval

text\<open>Afterwards, if \<open>(r,s)\<in>ps\<close>, the desired RE equivalence is shown via rule @{thm[source]bisim_lang_eq}.\<close>

text\<open>
Such a certificate \<open>(as, ps)\<close> could be obtained from untrusted computations, and checked by
 @{method eval}.
However, it turns out that constructing the (already verified) bisimulation is just as
 simple, removing the need to check it separately.\<close>

section\<open>Main loop\<close>

text\<open>
We present a simple work set algorithm which iteratively
  \<^item>identifies RE pairs missing for property 3 (these are the work set)
  \<^item>adds one of them to the relation, checking that it satisfies property 1 and 2

Initially, we put \<open>(r,s)\<close> in the work set, to ensure that it will be in the constructed relation.

We can then prove that the
 work set becoming empty already guarantees the premises of @{thm[source] bisim_lang_eq}.
\<close>

text\<open>\<open>succs\<close> computes the list of derivated RE pairs for all atoms:\<close>

fun succs where "succs as (r, s) = map (\<lambda>a. (nderiv a r, nderiv a s)) as"

text\<open>In each step, a pair is taken from the work set, added to the relation, and its derivatives are
 in turn added to the work set if they are not yet accounted for:
\<close>

fun step where "step as (ws, ps) =
  (let ps' = hd ws # ps;
    new = [p\<leftarrow>succs as (hd ws) . p \<notin> set ps' \<union> set ws]
  in (new @ tl ws, ps'))"

subsection\<open>Usage of @{const while_option}\<close>

text\<open>For purposes of the Logic (HOL being a logic of total functions) @{const while_option} always
 has a value associated with it: If no number of iterations falsifies the while-condition, this is
 @{const None}. However, the generated executable code only uses the unfolding equation @{thm
 while_option_unfold[no_vars]}, meaning it works just like an imperative \<^emph>\<open>while\<close> would.
\<close>

text\<open>The while-condition is the following:\<close>

fun test where "test (ws,_) \<longleftrightarrow> (case ws of [] \<Rightarrow> False | (p, q)#vs \<Rightarrow> nullable p \<longleftrightarrow> nullable q)"
text\<open>The loop terminates
  \<^item> if the worklist is empty (a suitable \<^emph>\<open>bisimulation\<close> was found) or
  \<^item> if two derivs do not agree on nullability (a counterexample was found)\<close>

text\<open>@{theory_text \<open>definition "closure as = while_option test (step as)"\<close>}\<close>

text\<open>The following is the same as @{const is_bisimulation}, but with the work list elements not yet
 processed:\<close>

definition pre_bisim :: "'a::order list \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp \<Rightarrow> ('a rexp \<times> 'a rexp) list \<times> ('a rexp \<times> 'a rexp) set \<Rightarrow> bool"
where
"pre_bisim as r s = (\<lambda>(ws,R).
 (r,s) \<in> R \<and> set ws \<subseteq> R \<and>
 (\<forall>(r,s)\<in> R. atoms r \<union> atoms s \<subseteq> set as) \<and>
 (\<forall>(r,s)\<in> R - set ws. (nullable r \<longleftrightarrow> nullable s) \<and>
   (\<forall>a\<in>set as. (nderiv a r, nderiv a s) \<in> R)))"

text\<open>@{const pre_bisim} is a suitable invariant:
  \<^item> if @{const pre_bisim} holds initially, it also holds after a @{const step}
  \<^item> the negated @{const test} together with the premise that the result  matches the pattern
 \<open>Some([], _)\<close> (i.e. terminated with an empty work set) implies @{const is_bisimulation}, yielding
 the desired equivalence via rule @{thm[source] bisim_lang_eq}

This proof is in a formal form available as @{thm[source] closure_sound}.
\<close>

subsection\<open>Remarks\<close>
text\<open>
Note that this is just the computation of the transitive closure of \<open>R\<close> w.r.t @{const
 nderiv}, i.e. the smallest set \<open>R' \<supseteq> R\<close> s.t. \<open>\<And>r1 r2 r3. (r1,r2) \<in> R' \<Longrightarrow> (r2,r3) \<in> R' \<Longrightarrow> (r1,r3) \<in> R'\<close>.
 Thus, it can be expressed using the library's @{const rtrancl_while}, which 
 is how it is done as of AFP 2017 @{cite "Regular-Sets-AFP"}.

Also note that there are more efficient ways to compute the transitive closure @{cite
 "Transitive-Closure-AFP"} @{cite "Roy_Floyd_Warshall-AFP"}, but for the small goals that arise in
 interactive proofs, this is not needed.
\<close>

subsection\<open>Termination via ACI-normalization\<close>

text\<open>REs \<open>r1\<close> and \<open>r2\<close> are \<^emph>\<open>ACI-equivalent\<close> @{cite "Krauss-Nipkow-JAR"} /
 \<^emph>\<open>similar\<close> @{cite Brzozowski}, if one can be transformed into the other using only the following
  rules:\<close>
lemma
(*<*)  "lang (Plus (Plus a b) c) = lang (Plus a (Plus b c))"(*>*)
  "lang (Times (Times a b) c) = lang (Times a (Times b c))" --\<open>\<^bold>\<open>A\<close>ssociativity\<close>
  "lang (Plus a b) = lang (Plus b a)"                       --\<open>\<^bold>\<open>C\<close>ommutativity\<close>
  "lang (Plus a a) = lang a"                                --\<open>\<^bold>\<open>I\<close>dempotence\<close>
  by (auto simp: conc_assoc)

text\<open>In the following, we will call a RE \<^emph>\<open>normed\<close> if
  \<^item> nested concatenation are parenthesised to the right
  \<^item> nested choices are also parenthesised to the right and also sorted:
    Atoms first, then @{const Star}-terms, then concatenations
    (This order is arbitrary, but fixed).

The goal is that @{const nderiv} maintains this property, meaning that ACI-equivalent terms can be
identified.
\<close>
text
\<open>The first step of the equivalence checker must bring the input expressions into a normal form,
 such that ACI-equilavent terms map to the same normal form. It also performs other minor
 simplifications. The authors indicate the rough procedure for such a transformation, but omit
 implementation details. These are not relevant anyways: As long as @{thm lang_norm[no_vars]} is
 fulfilled (a simple structural induction proves it), errors at this step would not 
  lead to wrong results, but instead falsify completeness of the method

  However, verifying completeness is not necessary for an Isabelle proof method: In the case that
 the method hangs (very unlikely, a termination proof exists!), a user could always just provide a
 structured proof in Isar.
\<close>

text\<open>
@{const norm} operates bottom up, deferring Plus-terms and Times-terms to auxiliary functions
  which associate their subterms in a fixed manner.

The rules are obviously designed to fulfill @{thm lang_nderiv[no_vars]} just like @{const deriv} does,
 which is shown by structural induction. This part is needed in the soundness proof.

 @{const nderiv} operating on @{const norm}ed terms outputs @{const norm}ed terms again. This fact is
 not needed for partial correctness, and therefore not verified.

It is, however, crucial for the termination argument:
In the while-step, the filter \<open>p \<notin> set ps' \<union> set ws\<close> must throw out at least ACI-equivalent terms
 (\<open>p\<close> is @{const norm}ed at that point).
 Brzozowski showed @{cite "Brzozowski"} that this is enough for the work set to become empty
 eventually.

  We will later also need this property:

  @{thm atoms_norm[no_vars]}
\<close>

section\<open>A proof method for standard-@{type rexp}s\<close>
text\<open>The authors choose to provide the equivalence checker only specialised to @{typ "nat rexp"},
 however, it also works for an arbitrary \<open>'a::order rexp\<close>:
\<close>

subsection\<open>@{const Equivalence_Checking.check_eqv} for arbitrary (but ordered) atoms\<close>
text\<open>The following definition and lemma are copied from @{theory Equivalence_Checking}, with @{typ
  nat} replaced by \<open>'a::order\<close>.\<close>
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

subsection\<open>Defining the proof method\<close>

text\<open>First, we need to refine subset-goals to an equivalence check:\<close>
lemma subset_eq_to_eq: "lang r \<subseteq> lang s \<longleftrightarrow> lang (Plus r s) = lang s"
  by auto

text\<open>Using @{doc eisbach} @{cite "Matichuk:2016:EPM:2904234.2904264"}, one could now define:\<close>
method rexp = (unfold subset_eq_to_eq)?, (rule soundness, eval)+
text\<open>An informal description: If necessary, unfold @{thm[source]
 subset_eq_to_eq} to obtain an equality goal, then apply the soundness rule (backwards refinement),
 then iterate the closure-check loop (by @{method eval}) until it has the form \<open>Some([],_)\<close>,
 which solves the goal. Repeat this if more subgoals are present.

Examples:
\<close>

abbreviation "AB \<equiv> Times (Atom (CHR ''a'')) (Atom (CHR ''b''))"
abbreviation "A_or_B \<equiv> Plus (Atom (CHR ''a'')) (Atom (CHR ''b''))"
abbreviation "B_or_A \<equiv> Plus (Atom (CHR ''b'')) (Atom (CHR ''a''))"

lemma
  "lang (Times (Star (Plus One AB)) A_or_B) = lang (Times (Star (Plus AB One)) A_or_B)"
  "lang (Times (Star (Plus Zero AB)) B_or_A) \<supseteq> lang (Times (Star (Plus AB One)) A_or_B)"
  "lang (Times (Star (Plus One AB)) A_or_B) \<subseteq> lang (Times (Star (Plus AB One)) A_or_B)"
  by rexp

abbreviation "r \<equiv> Plus AB (Plus (Star B_or_A) (Star A_or_B))"
abbreviation "s \<equiv> Plus (Plus (Star AB) (Star A_or_B)) B_or_A"

lemma "lang r = lang s"
  by rexp

lemma "lang (Star (Atom (CHR ''a''))) \<noteq> lang (Star (Atom (CHR ''b'')))"
  oops \<comment>\<open>correct, but not part of the method\<close>

section\<open>Draft: Testing the limits of termination\<close>

(*replace by comments about Not and Inter (extended REs)?*)

text\<open>Note that Brzozoswki's proof of termination requires the property that ACI-equivalent REs can
 be identified, i.e. mapped to one representative. Nipkow and Krauss argue why their @{const
 nderiv}-function maintains such an ACI-normal form, but they need the assumption that the atoms of
 the REs conform to some total order.

This is presently not reflected by the code @{cite "Regular-Sets-AFP"}: @{const closure} has the
 type

\<open>'a::order list \<Rightarrow> ... \<Rightarrow> ...\<close>

The reason is convenience for the user: When only requiring @{class order}, there is no need to
 provide an instance proof for @{class linorder} before being able to use the proof method: For
 its partial correctness, the total order is not needed.
\<close>
text\<open>The rest of this section will be reworked if I manage to construct a counterexample for
 termination. It can be ignored for now.
\<close>

paragraph \<open>Small example for a non-total order\<close>

text\<open>Via \<^bold>\<open>associativity\<close> and \<^bold>\<open>commutativity\<close>, only finitely many equivalent REs can arise (proof:
 both rules do not increase the term size). Thus, the counterexample needs to be crafted so that norm
 fails to recognize \<^bold>\<open>idempotence\<close>, producing bigger and bigger REs. The only @{const norm}-step which
 increases the RE is @{term "nderiv c (Times r s)"}, so target that.
\<close>

datatype part_ord = A | B | C

text\<open>For finite types, one could always find a total order, but let's assume we do not.\<close>

instantiation part_ord :: order
begin

definition "a \<le> b \<longleftrightarrow> a = b" for a b :: part_ord
definition "a < b \<longleftrightarrow> False" for a b :: part_ord

instance
  by standard (simp_all add: less_eq_part_ord_def less_part_ord_def)
end
(*<*)
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
    nr = norm (Times a (Times a a));
    ns = norm (Times (Times a a) a);
    as = add_atoms nr (add_atoms ns [])
  in closure as (nr, ns)"
(*>*)
(*
text\<open>We illustate the nontermination using the Isar proof language:\<close>
notepad
begin
  have \<open>nderiv s = \<close> by simp
  have \<open>... = \<close> by simp
  have \<open>... = \<close> by simp
  have \<open>... = \<close> by simp
end
*)

section\<open>Conclusion\<close>

subsection\<open>Achievements\<close>
text\<open>As mentioned above, the method simplifies interactive proof development in Isabelle/HOL.
However, it also is an advancement of theoretical CS, as Brzozowski's simple algorithm was seldom
 considered before. Due to Nipkow's and Krauss' development, it might get more attention.
\<close>

text\<open>Simplicity is desirable for an Isabelle proof method: Not only is a small, elegant
 verification faster to 
 re-run itself (AFP is run several times a day to test conformance to the Isabelle development
 version), the prover process also does not need to load a huge chunk of code whenever it encounters
 a usage of the proof method: As we have seen, we can shift the entire computation to the @{method eval}
 method, which probably resides in fast memory anyways during a lengthy build process.
\<close>

subsection\<open>Proof pearls\<close>
text\<open>Not so often, experts publish articles so polished and clear, that they are called \<^emph>\<open>Proof
 pearl\<close>.
The proof should be purposeful, and unexpected in its elegance and shortness. The authors compare
 their technique to the work of
 Braibant and 
 Pous @{cite Braibant2010}, whose verified equivalence checker is more efficient, but very complex in
 the derivation. 
 The paper's strength is that it mostly ignores standard textbook methods and finds inspiration
 instead in Brzozowski's paper @{cite "Brzozowski"}, which fits perfectly into the world of
 interactive theorem proving due to its simplicity.
\<close>

subsection\<open>Historical Remarks\<close>

text\<open>
Brzozoswki's RE derivatives are seldom-mentioned, which is surprising, considering they are such a
 natural counterpart to the (more often used) language derivatives.
  A quick search suggest that it took until 1998 until the simple algorithm above was formulated
 without automata theory.

Nipkow and Krauss mention as inspiration the \<^emph>\<open>Interactive Theorem Proving\<close> conference 2010,
 when Braibant and 
 Pous @{cite "Braibant2010"} presented their tactic for the theorem prover coq. While their acquired
 algorithm is quite efficient and can handle arbitrary Kleene algebras, they need long and complex
 proofs for the verification (about 19000 lines compared to about 950 in the AFP entry's relevant
 theories).
\<close>

(*<*)
end
(*>*)
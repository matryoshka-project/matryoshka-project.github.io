(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

theory Language
imports "~~/src/HOL/Library/BNF_Corec"
begin

declare rel_fun_def[simp]

text \<open>Type \oo for \<oo> and \dd for \<dd>\<close>

codatatype 'a language = Lang (\<oo>: bool) (\<dd>: "'a \<Rightarrow> 'a language")

primcorec Zero where
  "Zero = Lang False (\<lambda>_. Zero)"
primcorec One where
  "One = Lang True (\<lambda>_. Zero)"
primcorec Atom where
  "Atom a = Lang False (\<lambda>b. if a = b then One else Zero)"

primrec mem where
  "mem [] L = \<oo> L"
| "mem (a # w) L = mem w (\<dd> L a)"

text \<open>
  Fill the blanks (or rather undefineds) with sensible definitions,
  such that the commented proofs work for the mem properties.

  Prove the subset of the Kleene algebra axioms given below.
  You might need some auxiliary lemmas.
\<close>


definition Plus :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "Plus r s = undefined"

lemma Plus_sel[simp]:
  "\<oo> (Plus r s) = undefined"
  "\<dd> (Plus r s) a = undefined"
(*by (subst Plus.code; simp)+*)
  oops

lemma mem_Plus[simp]: "mem w (Plus r s) = (mem w r \<or> mem w s)"
(*by (induct w arbitrary: r s) auto*)
  oops

definition Times :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "Times r s = undefined"

lemma Times_sel[simp]:
  "\<oo> (Times r s) = undefined"
  "\<dd> (Times r s) a = undefined"
(*by (subst Times.code; simp)+*)
  oops

lemma mem_Times[simp]: "mem w (Times r s) = (\<exists>v u. w = v @ u \<and> mem v r \<and> mem u s)"
(*by (induct w arbitrary: r s)
    (auto 5 3 simp: Cons_eq_append_conv intro: exI[of _ "[]"] exI[of _ "_ # _"])*)
  oops

definition Star :: "'a language \<Rightarrow> 'a language" where
  "Star r = undefined"

lemma Star_sel[simp]:
  "\<oo> (Star r) = undefined"
  "\<dd> (Star r) a = undefined"
(*by (subst Star.code; simp)+*)
  oops

lemma mem_Star[simp]: "mem w (Star r) =
  (w = [] \<or> (\<exists>v u. w = v @ u \<and> mem v r \<and> mem u (Star r)))"
(*by (induct w arbitrary: r)
    (auto 5 3 simp: Cons_eq_append_conv intro: exI[of _ "[]"] exI[of _ "_ # _"])*)
  oops

lemma Plus_assoc[ac_simps]: "Plus (Plus r s) t = Plus r (Plus s t)"
  sorry

lemma Plus_comm[ac_simps]: "Plus r s = Plus s r"
  sorry

lemma Plus_ac[ac_simps]: "Plus r (Plus s t) = Plus s (Plus r t)"
  sorry

lemma Plus_idem[ac_simps]: "Plus r r = r"
  sorry

lemma Plus_ac_idem[ac_simps]: "Plus r (Plus r t) = Plus r t"
  sorry

lemma Times_PlusL[simp]: "Times (Plus r s) t = Plus (Times r t) (Times s t)"
  sorry

lemma Times_PlusR[simp]: "Times r (Plus s t) = Plus (Times r s) (Times r t)"
  sorry

lemma Times_assoc[simp]: "Times (Times r s) t = Times r (Times s t)"
  sorry

lemma Star_unfoldL: "Star r = Plus One (Times r (Star r))"
  sorry

end
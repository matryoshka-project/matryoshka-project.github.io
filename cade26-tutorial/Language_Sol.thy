(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

theory Language_Sol
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

corec (friend) Plus :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "Plus r s = Lang (\<oo> r \<or> \<oo> s) (\<lambda>a. Plus (\<dd> r a) (\<dd> s a))"

lemma Plus_sel[simp]:
  "\<oo> (Plus r s) = (\<oo> r \<or> \<oo> s)"
  "\<dd> (Plus r s) a = Plus (\<dd> r a) (\<dd> s a)"
  by (subst Plus.code; simp)+

lemma mem_Plus[simp]: "mem w (Plus r s) = (mem w r \<or> mem w s)"
  by (induct w arbitrary: r s) auto

corec (friend) Times :: "'a language \<Rightarrow> 'a language \<Rightarrow> 'a language" where
  "Times r s = Lang (\<oo> r \<and> \<oo> s)
     (\<lambda>a. if \<oo> r then Plus (Times (\<dd> r a) s) (\<dd> s a) else Times (\<dd> r a) s)"

lemma Times_sel[simp]:
  "\<oo> (Times r s) = (\<oo> r \<and> \<oo> s)"
  "\<dd> (Times r s) a = (if \<oo> r then Plus (Times (\<dd> r a) s) (\<dd> s a) else Times (\<dd> r a) s)"
  by (subst Times.code; simp)+

lemma mem_Times[simp]: "mem w (Times r s) = (\<exists>v u. w = v @ u \<and> mem v r \<and> mem u s)"
  by (induct w arbitrary: r s)
    (auto 5 3 simp: Cons_eq_append_conv intro: exI[of _ "[]"] exI[of _ "_ # _"])

corec (friend) Star :: "'a language \<Rightarrow> 'a language" where
  "Star r = Lang True (\<lambda>a. Times (\<dd> r a) (Star r))"

lemma Star_sel[simp]:
  "\<oo> (Star r) = True"
  "\<dd> (Star r) a = Times (\<dd> r a) (Star r)"
  by (subst Star.code; simp)+

lemma mem_Star[simp]: "mem w (Star r) =
  (w = [] \<or> (\<exists>v u. w = v @ u \<and> mem v r \<and> mem u (Star r)))"
  by (induct w arbitrary: r)
    (auto 5 3 simp: Cons_eq_append_conv intro: exI[of _ "[]"] exI[of _ "_ # _"])

lemma Plus_assoc[ac_simps]: "Plus (Plus r s) t = Plus r (Plus s t)"
  by (coinduction arbitrary: r s t) auto

lemma Plus_comm[ac_simps]: "Plus r s = Plus s r"
  by (coinduction arbitrary: r s) auto

lemma Plus_ac[ac_simps]: "Plus r (Plus s t) = Plus s (Plus r t)"
  by (metis Plus_assoc Plus_comm)

lemma Plus_idem[ac_simps]: "Plus r r = r"
  by (coinduction arbitrary: r) auto

lemma Plus_ac_idem[ac_simps]: "Plus r (Plus r t) = Plus r t"
  by (metis Plus_assoc Plus_idem)

lemma Plus_Zero[simp]: "Plus Zero r = r"
  by (coinduction arbitrary: r) auto

lemma Times_PlusL[simp]: "Times (Plus r s) t = Plus (Times r t) (Times s t)"
  by (coinduction arbitrary: r s rule: language.coinduct_upto)
    (auto intro: language.cong_base language.cong_refl language.cong_Plus simp: ac_simps)

lemma Times_PlusR[simp]: "Times r (Plus s t) = Plus (Times r s) (Times r t)"
  by (coinduction arbitrary: r s rule: language.coinduct_upto)
    (fastforce intro: language.cong_base language.cong_refl language.cong_Plus simp: ac_simps)

lemma Times_assoc[simp]: "Times (Times r s) t = Times r (Times s t)"
  by (coinduction arbitrary: r s t rule: language.coinduct_upto)
    (fastforce intro: language.cong_base language.cong_refl language.cong_Plus simp: ac_simps)

lemma Times_Zero[simp]: "Times Zero r = Zero"
  by (coinduction arbitrary: r) auto

lemma Star_Zero: "Star Zero = One"
  by (coinduction rule: language.coinduct_upto) (auto intro: language.cong_refl)

lemma Star_One: "Star One = One"
  by (coinduction rule: language.coinduct_upto) (auto intro: language.cong_refl)

lemma Star_unfoldL: "Star r = Plus One (Times r (Star r))"
  by (coinduction rule: language.coinduct_upto) (auto intro: language.cong_refl simp: ac_simps)

end
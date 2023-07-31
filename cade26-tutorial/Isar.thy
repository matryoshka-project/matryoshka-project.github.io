(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

section \<open>Isar examples\<close>

theory Isar
  imports Main
begin

text \<open>Cantor's theorem\<close>

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume a: "surj f"
  from a have b: "\<forall>A. \<exists>a. A = f a"
    by (simp add: surj_def)
  from b have c: "\<exists>a. {x. x \<notin> f x} = f a"
    by blast
  from c show False
    by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set" assumes s: "surj f"
  shows False
proof -
  have "\<exists>a. {x. x \<notin> f x} = f a"
    using s by (auto simp: surj_def)
  then show False
    by blast
qed

text \<open>Case distinction\<close>

lemma R
proof cases
  assume P
  show R
    sorry
next
  assume "\<not> P"
  show R
    sorry
qed

lemma
  assumes "P \<or> Q"
  shows R
  using assms
proof
  assume P
  show R
    sorry
next
  assume Q
  show R
    sorry
qed

text \<open>Contradiction\<close>

lemma "\<not> P"
proof
  assume P
  show False
    sorry
qed

lemma P
proof (rule ccontr)
  assume "\<not> P"
  show False
    sorry
qed

text \<open>Equivalence\<close>

lemma "P \<longleftrightarrow> Q"
proof
  assume P
  show Q
    sorry
next
  assume Q
  show P
    sorry
qed

text \<open>Quantifiers\<close>

lemma "\<forall>x. P x"
proof
  fix x
  show "P x"
    sorry
qed

lemma "\<exists>x. P x"
proof
  show "P witness"
    sorry
qed

end

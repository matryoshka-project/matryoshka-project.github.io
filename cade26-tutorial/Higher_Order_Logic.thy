(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

theory Higher_Order_Logic
  imports Main
begin

typ bool
typ nat
typ "'a set"
typ "nat set"

typedecl varname

typedef nznat = "UNIV - {0::nat}"
  by auto

term Abs_nznat
term Rep_nznat

print_theorems


(* A simple comment *)

text \<open>This is also a comment but it generates nice \LaTeX-text!\<close>

text \<open>Note that variables and constants (eg True, &) are displayed differently. \<close>

term "True"
term "False"
term "true"
term "True & False"
term "True & false"

value "True & False"
value "True & P"

(* To display types in jedit: press ctrl (Mac: cmd) and hover over text.
   To view the definition of a constant: press ctrl (Mac: cmd) and click on the text.
*)

text \<open>Warning: "+" and numbers are overloaded:\<close>

term "n + n = 0"
term "(n::nat) + n = 0"

(*Try this:

term "True + False"

Terms must be type correct!*)

text \<open>Type inference:\<close>

term "f (g x) y"
term "h (\<lambda>x. f(g x))"
term "\<lambda>x. x + x"

text \<open>Introducing new (higher-order) constants:\<close>

consts unknown :: int

lemma "unknown = 0"
  nitpick [show_consts]
  oops

lemma "unknown \<noteq> 0"
  nitpick [show_consts]
  oops

definition square :: "int \<Rightarrow> int" where
  "square n = n * n"

print_theorems
thm square_def


text \<open>Metalogic vs. object logic\<close>

lemma "\<And>x. A x \<Longrightarrow> B x"
  oops

lemma "\<forall>x. A x \<longrightarrow> B x"
  oops

lemma "\<exists>x. \<not> A x \<and> B x"
  oops

end

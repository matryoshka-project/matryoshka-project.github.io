(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

section \<open>Programming examples\<close>

theory Induction
  imports Main
begin

(* disable list syntax and functions from Isabelle's standard library *)
no_type_notation list ("[_]" [0] 999)
no_notation
  Nil ("[]") and
  Cons (infixr "#" 65) and
  append (infixr "@" 65)
hide_const (open) rev append Nil Cons map concat set
hide_type (open) list



datatype (set: 'a) list
  = Nil               ("[]")
  | Cons 'a "'a list" (infixr "#" 65)
  for map: map

translations (* syntax for list enumerations *)
  "[x, xs]" == "x # [xs]"
  "[x]"     == "x # []"

primrec append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@" 65)
where
  append_Nil:  "[] @ ys = ys"
| append_Cons: "(x # xs) @ ys = x # (xs @ ys)"

export_code append in Haskell
value "[1,2,3] @ [4,5,6] :: int list"


lemma append_Nil2: "xs @ [] = xs"
apply(induction xs)
 apply simp
apply simp
done
(*
proof(induction xs)
  case Nil
  then show ?case by(fact append_Nil)
next
  case (Cons x xs)
  then show ?case using [[simp_trace_new mode=full]] by simp
thm Cons.IH
(*  have "(x # xs) @ [] = x # (xs @ [])" by(fact append_Cons)
  also have "x # (xs @ []) = x # xs" using Cons.IH by simp
  finally show "(x # xs) @ [] = x # xs" by this *)
qed
*)



primrec rev :: "'a list \<Rightarrow> 'a list" where
  "rev [] = []"
| "rev (x # xs) = rev xs @ [x]"

export_code rev in SML

lemma append_assoc: "(xs @ ys) @ zs = xs @ (ys @ zs)"
by(induction xs)(simp_all)

lemma rev_append: "rev (xs @ ys) = rev ys @ rev xs"
by(induction xs)(simp_all add: append_Nil2 append_assoc)

lemma rev_rev: "rev (rev xs) = xs"
by(induction xs)(simp_all add: rev_append)


primrec qrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  qrev_Nil:  "qrev []       ys = ys"
| qrev_Cons: "qrev (x # xs) ys = qrev xs (x # ys)"

thm list.induct

lemma qrev_aux: "qrev xs zs @ ys = qrev xs (zs @ ys)"
apply(induction xs arbitrary: zs)
 apply simp
apply simp
done

lemma rev_qrev': "rev xs @ ys = qrev xs ys"
apply(induction xs arbitrary: ys)
 apply simp
apply(simp add: qrev_aux)
done

lemma rev_qrev: "rev xs = qrev xs []"
apply(simp add: rev_qrev'[symmetric] append_Nil2)
done

declare rev_qrev [code]

export_code rev in Haskell

thm rev_def



text \<open>
Termination proofs

Task: Define a function merge that merges two lists:

  merge [a,b,c] [1,2,3,4] = [a,1,b,2,c,3,4]
\<close>

function merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge [] ys = ys"
| "merge (x # xs) ys = x # merge ys xs"
by pat_completeness auto
termination by size_change
(* apply(relation "measure (\<lambda>(xs, ys). size xs + size ys)")
apply auto
done *)

value "merge [1,2,3] [4,5,6,7] :: int list"

lemma size_merge: "size (merge xs ys) = size xs + size ys"
apply(induction xs ys rule: merge.induct)
apply simp_all
done

text \<open>Rose trees\<close>

datatype 'a rtree = Node 'a "'a rtree list"

thm rtree.induct

primrec rmirror :: "'a rtree \<Rightarrow> 'a rtree"
where "rmirror (Node x ts) = Node x (rev (map rmirror ts))"

lemma map_append [simp]: "map f (xs @ ys) = map f xs @ map f ys"
by(induction xs) simp_all

lemma map_rev: "map f (rev xs) = rev (map f xs)"
by(induction xs) simp_all

lemma rmirror_rmirror: "rmirror (rmirror t) = t"
proof(induction t)
  case (Node x ts)
  thm Node.IH
(*  have *: "map (rmirror \<circ> rmirror) ts = map id ts"
thm list.map_cong
    apply(rule list.map_cong)
     apply simp
    apply(simp)
    apply(rule Node.IH)
    apply assumption
    done
thm list.map_comp
  show ?case
    apply(simp)
    apply(simp add: map_rev list.map_comp rev_rev * list.map_id)
    done
*)  show ?case
thm list.map_ident
    by(simp add: map_rev list.map_comp rev_rev Node.IH list.map_ident cong: list.map_cong) 
qed

end

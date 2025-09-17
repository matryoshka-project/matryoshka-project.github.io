(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

section \<open>Exercises on Programming\<close>

(* The exercises are at the end of this file. 
  The start just defines some list and tree functions that were covered in the tutorial.
*)

theory Programming
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

subsection \<open>Lists\<close>

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
proof(induction xs)
  case Nil
  show ?case by(fact append_Nil)
next
  case (Cons x xs)
  have "(x # xs) @ [] = x # (xs @ [])" by(simp only: append_Cons)
  also have "x # (xs @ []) = x # xs" by(simp only: Cons.IH)
  finally show ?case by this
qed

lemma append_assoc: "(xs @ ys) @ zs = xs @ ys @ zs"
by(induction xs) simp_all

lemma set_append [simp]: "set (xs @ ys) = set xs \<union> set ys"
by(induction xs) simp_all


fun rev :: "'a list \<Rightarrow> 'a list" where
  rev_Nil:  "rev [] = []"
| rev_Cons: "rev (x # xs) = rev xs @ [x]"

export_code rev in SML

lemma rev_append: "rev (xs @ ys) = rev ys @ rev xs"
by(induction xs)(simp_all add: append_Nil2 append_assoc)

lemma rev_rev: "rev (rev xs) = xs"
by(induction xs)(simp_all add: rev_append)

lemma set_rev [simp]: "set (rev xs) = set xs"
by(induction xs) simp_all

lemma map_append [simp]: "map f (xs @ ys) = map f xs @ map f ys"
by(induction xs) simp_all

lemma map_rev: "map f (rev xs) = rev (map f xs)"
by(induction xs) simp_all


subsection \<open>Rose trees\<close>

datatype 'a rtree = Node 'a "'a rtree list"

primrec rmirror :: "'a rtree \<Rightarrow> 'a rtree"
where "rmirror (Node x ts) = Node x (rev (map rmirror ts))"

lemma rmirror_rmirror: "rmirror (rmirror t) = t"
proof(induction t)
  case (Node x ts)
  have *: "map (rmirror \<circ> rmirror) ts = map id ts"
    apply(rule list.map_cong)
     apply(rule refl)
    apply(simp)
    apply(rule Node.IH)
    apply assumption
    done
  show ?case
    apply(simp)
    apply(simp add: map_rev list.map_comp rev_rev * list.map_id)
    done
qed

lemma "rmirror (rmirror t) = t" (* the previous lemma proven in one line *)
by(induction t)(simp add: map_rev list.map_comp rev_rev list.map_id[unfolded id_def] cong: list.map_cong)

section \<open>Exercises\<close>

subsection \<open>List concatenation\<close>
(* Define a function concat :: "'a list list \<Rightarrow> 'a list" that concatenates a list of lists. *)

primrec concat :: "'a list list \<Rightarrow> 'a list" where
  "concat [] = ..."
| "concat (xs # xss) = ..."

(* How does concat behave w.r.t. append and rev? Find appropriate right-hand sides
  for the lemmas and prove them. *)

lemma concat_append: "concat (xss @ yss) = ..."

lemma rev_concat: "rev (concat xss) = ..."


subsection \<open>Rose trees\<close>

(* Define a function preorder :: "'a rtree \<Rightarrow> 'a list" that traverses an
  arbitrarily branching tree in preorder and returns the list of nodes it visits. Also define a
  function postorder that does the same for a postorder traversal. *)

primrec preorder :: "'a rtree \<Rightarrow> 'a list" where 

primrec postorder :: "'a rtree \<Rightarrow> 'a list" where

(* Now prove by induction that the preorder traversal of a mirrored tree
  is the reverse of its postorder traversal. *)

lemma preorder_rmirror: "preorder (rmirror t) = ..."


end
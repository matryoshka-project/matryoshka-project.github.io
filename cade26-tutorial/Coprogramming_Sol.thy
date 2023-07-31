(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

section \<open>Exercises on Coprogramming\<close>

(* The exercises are at the end of this file. 
  The start just defines some list and tree functions that were covered in the tutorial.
*)

theory Coprogramming_Sol
  imports "~~/src/HOL/Library/BNF_Corec"
begin

subsection \<open>Lazy lists\<close>

codatatype 'a llist = lnull: LNil | LCons (lhd: 'a) (ltl: "'a llist")
  for map: lmap
  where "ltl LNil = LNil"

lemma LCons_lazy: "x = y \<Longrightarrow> LCons x xs = LCons y xs" by simp
setup {* Code_Simp.map_ss (Simplifier.add_cong @{thm LCons_lazy}) *}

subsection \<open>Trees\<close>

codatatype 'a tree = is_Leaf: Leaf | Node (left: "'a tree") (val: 'a) (right: "'a tree")
  for map: tmap
  where
    "left Leaf = Leaf" 
  | "right Leaf = Leaf"

lemma Node_lazy: "x = y \<Longrightarrow> Node l x r = Node l y r" by simp (* Lazy symbolic evaluation with value [simp] (odd style with ease) *)
setup {* Code_Simp.map_ss (Simplifier.add_cong @{thm Node_lazy}) *}

lemma tmap_sel [simp]:
  "left (tmap f t) = tmap f (left t)"
  "right (tmap f t) = tmap f (right t)"
  "\<not> is_Leaf t \<Longrightarrow> val (tmap f t) = f (val t)"
by(cases t; simp; fail)+

primcorec chop :: "'a tree \<Rightarrow> 'a tree"
where
  "is_Leaf t \<or> is_Leaf (left t) \<and> is_Leaf (right t) \<Longrightarrow> is_Leaf (chop t)"
| "val (chop t) = (if is_Leaf (left t) then val (right t) else val (left t))"
| "left (chop t) = (if is_Leaf (left t) then left (right t) else right t)"
| "right (chop t) = (if is_Leaf (left t) then right (right t) else chop (left t))"

lemma chop_match [simp]:
  "chop Leaf = Leaf"
  "chop (Node l x r) = (if is_Leaf l then r else Node r (val l) (chop l))"
by(rule tree.expand; simp; fail)+

subsection \<open>From lists to trees and back\<close>

primcorec tree_of :: "'a llist \<Rightarrow> 'a tree"
where
  "lnull xs \<Longrightarrow> is_Leaf (tree_of xs)"
| "left (tree_of xs) = Leaf"
| "val (tree_of xs) = lhd xs"
| "right (tree_of xs) = tree_of (ltl xs)"

lemma tree_of_match [simp]:
  "tree_of LNil = Leaf"
  "tree_of (LCons x xs) = Node Leaf x (tree_of xs)"
by(rule tree.expand; simp; fail)+

primcorec llist_of :: "'a tree \<Rightarrow> 'a llist"
where
  "is_Leaf t \<Longrightarrow> lnull (llist_of t)"
| "lhd (llist_of t) = val t"
| "ltl (llist_of t) = llist_of (chop t)"

lemma llist_of_match [simp]:
  "llist_of Leaf = LNil"
  "llist_of (Node l x r) = LCons x (llist_of (chop (Node l x r)))"
by(rule llist.expand; simp; fail)+

lemma chop_tree_of: "chop (tree_of xs) = tree_of (ltl xs)"
apply(cases xs)
apply simp_all
done

lemma llist_of_tree_of: "llist_of (tree_of xs) = xs"
apply(coinduction arbitrary: xs)
apply(simp_all add: chop_tree_of)
done


section \<open>Exercises\<close>

subsection \<open>Another conversion to trees\<close>

(* Define a function tree_of' :: "'a llist \<Rightarrow> 'a tree" that converts a lazy
 list [x,y,z,...] into a tree that leans to the left, i.e., 

           x
         /   \
        y    Leaf
      /   \
     z    Leaf
    ...
*)

primcorec tree_of' :: "'a llist \<Rightarrow> 'a tree" where
  "lnull xs \<Longrightarrow> is_Leaf (tree_of' xs)"
| "val (tree_of' xs) = lhd xs"
| "left (tree_of' xs) = tree_of' (ltl xs)"
| "right (tree_of' xs) = Leaf"

(* Prove that tree_of' is a right-inverse of llist_of.
  Hint: You might need a lemma about chop and tree_of'. 
  You can use value with finite lazy lists to see what chop does to tree_of'.
 *)

lemma chop_tree_of': "chop (tree_of' xs) = (if lnull xs then Leaf else tree_of (ltl xs))"
apply(coinduction arbitrary: xs rule: tree.coinduct_strong)
apply auto
done

lemma llist_of_tree_of' [simp]: "llist_of (tree_of' xs) = xs"
apply(rule llist.expand)
apply(simp_all add: chop_tree_of' llist_of_tree_of)
done

subsection \<open>Ascending numbers\<close>

(* Define a function lup :: int llist that is the list of all
 non-negative integers in ascending order. 

Hint: Use corecursion up-to.
*)
friend_of_corec lmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"
by(rule llist.expand; simp split: llist.split) transfer_prover

corec lup :: "int llist" where "lup = LCons 0 (lmap (op + 1) lup)"


subsection \<open>A tree of all non-negative numbers\<close>

(* Define a tree tnum :: int tree with no Leafs such that llist_of is the
  ascending list of numbers (use int as element type). Prove the lemma.

Hint: You will need to prove lemmas about how the friends interact with your functions.
 *)
friend_of_corec tmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where "tmap f t = (case t of Leaf \<Rightarrow> Leaf | Node l x r \<Rightarrow> Node (tmap f l) (f x) (tmap f r))"
by(rule tree.expand; simp split: tree.splits)  transfer_prover

corec tnum :: "int tree"
where "tnum = Node (tmap (\<lambda>x. x * 2 + 1) tnum) 0 (tmap (\<lambda>x. x * 2 + 2) tnum)"

lemma tnum_sel [simp]:
  "is_Leaf tnum = False"
  "val tnum = 0"
  "left tnum = tmap (\<lambda>x. x * 2 + 1) tnum"
  "right tnum = tmap (\<lambda>x. x * 2 + 2) tnum"
by(subst tnum.code; simp; fail)+

lemma chop_tmap: "chop (tmap f t) = tmap f (chop t)"
apply(coinduction arbitrary: t rule: tree.coinduct_strong)
apply(auto simp add: tree.map_sel)
done

lemma chop_tnum: "chop tnum = tmap (op + 1) tnum"
proof(coinduction rule: tnum.coinduct)
  case Eq_int_tree
  have "?is_Leaf" by simp
  moreover have "?Node"
  proof(intro strip conjI)
    let ?R = "\<lambda>t t'. t = chop tnum \<and> t' = tmap (op + 1) tnum"
    show "tree.congclp ?R (left (chop tnum)) (left (tmap (op + 1) tnum))"
      by(simp add: tree.map_comp o_def algebra_simps tmap.friend.cong_refl)
    show "val (chop tnum) = val (tmap (op + 1) tnum)" by simp
    have "right (tmap (op + 1) tnum) = tmap (\<lambda>x. x * 2 + 1) (tmap (op + 1) tnum)"
      by(simp add: tree.map_comp o_def)
    then show "tree.congclp ?R (right (chop tnum)) (right (tmap (op + 1) tnum))"
      by(simp add: chop_tmap tmap.friend.cong_tmap[OF refl] tmap.friend.cong_base)
  qed
  ultimately show ?case by simp
qed

lemma llist_of_tmap: "llist_of (tmap f t) = lmap f (llist_of t)"
apply(coinduction arbitrary: t)
apply(auto simp add: llist.map_sel chop_tmap)
done

lemma llist_of_tnum: "llist_of tnum = lup"
apply(rule lup.unique)
apply(rule llist.expand)
apply(simp_all add: chop_tnum llist_of_tmap)
done

end
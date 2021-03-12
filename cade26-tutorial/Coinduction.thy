(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

section \<open>Coprogramming examples\<close>

theory Coinduction imports
  "~~/src/HOL/Library/BNF_Corec"
  "~~/src/HOL/Library/Code_Test"
begin

section \<open>Extended naturals\<close>

codatatype enat = is_zero: Zero | eSuc (epred: enat)

text \<open>Lazy evaluation for enat with @{method code_simp}.\<close>
lemma eSuc_lazy: "eSuc n = eSuc n" by simp
setup {* Code_Simp.map_ss (Simplifier.add_cong @{thm eSuc_lazy}) *}

primcorec infty :: enat ("\<infinity>") where
  "\<infinity> = eSuc \<infinity>"

thm infty.sel infty.disc

primcorec eplus :: "enat \<Rightarrow> enat \<Rightarrow> enat" (infixl "\<oplus>" 65)
where 
  "m \<oplus> n = (if is_zero m then n else eSuc (epred m \<oplus> n))"


thm eplus.simps

thm enat.coinduct

lemma eplus_infty [simp]: "\<infinity> \<oplus> n = \<infinity>"
apply(coinduction)
apply auto
done
(* proof(coinduction)
  case Eq_enat
  have "is_zero (\<infinity> \<oplus> n) = is_zero \<infinity>" using [[simp_trace_new]] by simp
  moreover have "\<not> is_zero (\<infinity> \<oplus> n) \<longrightarrow> \<not> is_zero \<infinity> \<longrightarrow> epred (\<infinity> \<oplus> n) = \<infinity> \<oplus> n \<and> epred \<infinity> = \<infinity>"
  proof(intro impI conjI)
    have "epred (\<infinity> \<oplus> n) = (if is_zero \<infinity> then epred n else epred \<infinity> \<oplus> n)" by(simp)
    also have "is_zero \<infinity> = False" by simp
    also have "(if False then epred n else epred \<infinity> \<oplus> n) = epred \<infinity> \<oplus> n" by simp
    also have "epred \<infinity> = \<infinity>" by simp
    finally show "epred (\<infinity> \<oplus> n) = \<infinity> \<oplus> n" .
    show "epred \<infinity> = \<infinity>" by simp
  qed
  ultimately show ?case ..
qed *)

thm enat.coinduct_strong enat.coinduct
lemma eplus_infty2 [simp]: "n \<oplus> \<infinity> = \<infinity>"
proof(coinduction arbitrary: n rule: enat.coinduct_strong)
  case Eq_enat
  have "is_zero (n \<oplus> \<infinity>) = is_zero \<infinity>" by simp
  then show ?case
    apply auto
    done
qed

section \<open>Streams / infinite sequences\<close>

codatatype 'a stream = SCons (shd: 'a) (stl: "'a stream") (infixr "##" 65)
  for map: smap

declare stream.map_sel [simp]

text \<open>Lazy evaluation for streams with @{method code_simp}.\<close>
lemma SCons_lazy: "x = y \<Longrightarrow> x ## xs = y ## xs" by simp
setup {* Code_Simp.map_ss (Simplifier.add_cong @{thm SCons_lazy}) *}

fun stake :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a list" where
  "stake 0       _         = []"
| "stake (Suc n) (x ## xs) = x # stake n xs"

primcorec zeros :: "nat stream" 
where "zeros = 0 ## zeros"

primcorec smerge :: "'a stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream"
where
  "shd (smerge xs ys) = shd xs"
| "stl (smerge xs ys) = smerge ys (stl xs)"

primcorec up :: "nat \<Rightarrow> nat stream"
where "up n = n ## up (n + 1)"

value [simp] "stake 10 (up 12)"

value [GHC] "stake 5 (smerge (up 1) (up 5))"

section \<open>Trees\<close>

codatatype 'a tree = is_Leaf: Leaf | Node (left: "'a tree") (val: 'a) (right: "'a tree")
  for map: tmap
  where
    "left Leaf = Leaf" 
  | "right Leaf = Leaf"

lemma Node_lazy: "x = y \<Longrightarrow> Node l x r = Node l y r" by simp (* Lazy symbolic evaluation with value [simp] *)
setup {* Code_Simp.map_ss (Simplifier.add_cong @{thm Node_lazy}) *}

primcorec mirror :: "'a tree \<Rightarrow> 'a tree"
where
  "is_Leaf t \<Longrightarrow> is_Leaf (mirror t)"
| "left (mirror t) = mirror (right t)"
| "val (mirror t) = val t"
| "right (mirror t) = mirror (left t)"

thm mirror.sel

lemma mirror_match [simp]:
  "mirror Leaf = Leaf"
  "mirror (Node l x r) = Node (mirror r) x (mirror l)"
by(rule tree.expand; simp; fail)+

lemma mirror_mirror [simp]: "mirror (mirror t) = t"
proof(coinduction arbitrary: t)
print_cases
  case Eq_tree
  have "?is_Leaf" by simp
  moreover have "?Node" by simp
  ultimately show ?case by simp
qed

lemma mirror_sel [simp]:
  "left (mirror t) = mirror (right t)"
  "right (mirror t) = mirror (left t)"
  "val (mirror t) = val t"
by(cases t; simp; fail)+

lemma tmap_sel [simp]:
  "left (tmap f t) = tmap f (left t)"
  "right (tmap f t) = tmap f (right t)"
  "\<not> is_Leaf t \<Longrightarrow> val (tmap f t) = f (val t)"
by(cases t; simp; fail)+

datatype dir = L | R

fun subtree :: "dir list \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
where
  "subtree [] t = t"
| "subtree (L # p) t = subtree p (left t)"
| "subtree (R # p) t = subtree p (right t)"

primrec swap :: "dir \<Rightarrow> dir"
where "swap L = R" | "swap R = L"

lemma subtree_append: "subtree (p @ p') t = subtree p' (subtree p t)"
apply(coinduction arbitrary: p p' t)
apply auto
oops

lemma subtree_append: "subtree (p @ p') t = subtree p' (subtree p t)"
apply(induction p t rule: subtree.induct)
apply auto
done

lemma subtree_mirror: "subtree p (mirror t) = mirror (subtree (map swap p) t)"
proof(induction p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons dir p)
  then show ?case by(cases dir) auto
qed


codatatype 'a llist = lnull: LNil | LCons (lhd: 'a) (ltl: "'a llist")
  for map: lmap
  where "ltl LNil = LNil"

lemma LCons_lazy: "x = y \<Longrightarrow> LCons x xs = LCons y xs" by simp
setup {* Code_Simp.map_ss (Simplifier.add_cong @{thm LCons_lazy}) *}

fun ltake :: "nat \<Rightarrow> 'a llist \<Rightarrow> 'a list"
where 
  "ltake 0 xs = []"
| "ltake (Suc n) LNil = []"
| "ltake (Suc n) (LCons x xs) = x # ltake n xs"

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

primcorec chop :: "'a tree \<Rightarrow> 'a tree" (* tree chopping *)
where
  "is_Leaf t \<or> is_Leaf (left t) \<and> is_Leaf (right t) \<Longrightarrow> is_Leaf (chop t)"
| "val (chop t) = (if is_Leaf (left t) then val (right t) else val (left t))"
| "left (chop t) = (if is_Leaf (left t) then left (right t) else right t)"
| "right (chop t) = (if is_Leaf (left t) then right (right t) else chop (left t))"

lemma chop_match [simp]:
  "chop Leaf = Leaf"
  "chop (Node l x r) = (if is_Leaf l then r else Node r (val l) (chop l))"
by(rule tree.expand; simp; fail)+

primcorec llist_of :: "'a tree \<Rightarrow> 'a llist"
where
  "is_Leaf t \<Longrightarrow> lnull (llist_of t)"
(* | "\<not> is_Leaf t \<Longrightarrow> \<not> lnull (llist_of t)" *)
| "lhd (llist_of t) = val t"
| "ltl (llist_of t) = llist_of (chop t)"

lemma llist_of_match [simp]:
  "llist_of Leaf = LNil"
  "llist_of (Node l x r) = LCons x (llist_of (chop (Node l x r)))"
by(rule llist.expand; simp; fail)+

value "ltake 10 (llist_of (Node 
    (Node (Node Leaf 2 Leaf) (1 :: int) (Node Leaf 3 Leaf)) 
    0
    (Node (Node Leaf 5 Leaf) 4 (Node Leaf 6 Leaf))))"

lemma chop_tree_of: "\<not> lnull xs \<Longrightarrow> chop (tree_of xs) = tree_of (ltl xs)"
apply(coinduction arbitrary: xs rule: tree.coinduct_strong)
apply auto
done

lemma llist_of_tree_of: "llist_of (tree_of xs) = xs"
apply(coinduction arbitrary: xs)
apply( auto simp add: )
apply(rule arg_cong[where f=llist_of])
subgoal for xs apply(coinduction arbitrary: xs rule: tree.coinduct_strong) apply auto done
done

end

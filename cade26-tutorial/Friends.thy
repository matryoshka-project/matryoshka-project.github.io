(* Certified Functional (Co)programming with Isabelle/HOL *)
(* Jasmin Christian Blanchette, Andreas Lochbihler, Andrei Popescu, Dmitriy Traytel *)

theory Friends
  imports
    Complex_Main
    "~~/src/HOL/Library/BNF_Corec"
    "~~/src/HOL/Library/Code_Test"
    "~~/src/HOL/Library/Code_Target_Nat"
begin

section \<open>Streams\<close>

codatatype 'a stream = SCons (shd: 'a) (stl: "'a stream") (infixr "##" 65)
  for map: smap

declare stream.map_sel [simp]

text \<open>Lazy evaluation for streams with @{method code_simp}.\<close>
lemma SCons_lazy: "x = y \<Longrightarrow> x ## xs = y ## xs" by simp
setup {* Code_Simp.map_ss (Simplifier.add_cong @{thm SCons_lazy}) *}

fun stake :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a list" where
  "stake n (x ## xs) = (if n = 0 then [] else x # stake (n - 1) xs)"

primcorec zeros :: "nat stream"
  where "zeros = 0 ## zeros"

primcorec up :: "nat \<Rightarrow> nat stream"
  where "up n = n ## up (n + 1)"

section \<open>Sum\<close>

text \<open>Type "\oplus" for the symbol \<oplus>\<close>

primcorec pls :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infixl "\<oplus>" 66) where
  "s \<oplus> t = (shd s + shd t) ## stl s \<oplus> stl t"

friend_of_corec pls where
  "s \<oplus> t = (shd s + shd t) ## stl s \<oplus> stl t"
   apply (rule pls.code)
  apply transfer_prover
  done

section \<open>Shuffle Product\<close>

text \<open>Type "\otimes" for the symbol \<oplus>\<close>

corec prd :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infixl "\<otimes>" 76) where
  "s \<otimes> t = (shd s * shd t) ## stl s \<otimes> t \<oplus> s \<otimes> stl t"

friend_of_corec prd where
  "s \<otimes> t = (shd s * shd t) ## stl s \<otimes> t \<oplus> s \<otimes> stl t"
   apply (rule prd.code)
  apply transfer_prover
  done

lemma prd_sel[simp]:
  "shd (s \<otimes> t) = shd s * shd t"
  "stl (s \<otimes> t) = stl s \<otimes> t \<oplus> s \<otimes> stl t"
  by (subst prd.code; simp)+

section \<open>Exponentiation\<close>

corec (friend) pow2 where
  "pow2 s = (2 ^ shd s) ## stl s \<otimes> pow2 s"

lemma pow2_sel[simp]:
  "shd (pow2 s) = 2 ^ shd s"
  "stl (pow2 s) = stl s \<otimes> pow2 s"
  by (subst pow2.code; simp)+

corec (friend) selfie where
  "selfie s = shd s ## selfie (selfie (stl s) \<oplus> selfie s)"


lemma selfie_sel[simp]:
  "shd (selfie s) = shd s"
  "stl (selfie s) = selfie (selfie (stl s) \<oplus> selfie s)"
  by (subst selfie.code; simp)+

section \<open>Playing with OEIS\<close>

corec s1 :: "nat stream" where
  "s1 = (0 ## 1 ## s1) \<oplus> (0 ## s1)"

corec s2 :: "nat stream" where
  "s2 = 0 ## ((1 ## s2) \<oplus> s2)"

lemma s1_sel[simp]:
  "shd s1 = 0"
  "stl s1 = (1 ## s1) \<oplus> s1"
  by (subst s1.code; simp)+

lemma s2_sel[simp]:
  "shd s2 = 0"
  "stl s2 = (1 ## s2) \<oplus> s2"
  by (subst s2.code; simp)+

value [GHC] "stake 15 s1"
value [GHC] "stake 15 s2"

lemma "s1 = s2"
  by (coinduction rule: stream.coinduct_upto) (auto intro: stream.cong_intros)


corec t1 :: "nat stream" where
  "t1 = (1 ## t1) \<otimes> (1 ## t1)"

corec t2 :: "nat stream" where
  "t2 = 1 ## (t2 \<otimes> t2)"

corec t3 :: "nat stream" where
  "t3 = pow2 (0 ## t3)"

corec t4 :: "nat stream" where
  "t4 = 1 ## selfie t4"

lemma t2_sel[simp]:
  "shd t2 = 1"
  "stl t2 = t2 \<otimes> t2"
  by (subst t2.code; simp)+

value [GHC] "stake 10 t1"
value [GHC] "stake 10 t2"
value [GHC] "stake 10 t3"
value [GHC] "stake 10 t4"

lemma "stl t2 = t1"
proof (rule t1.unique)
  have "stl t2 = t2 \<otimes> t2" by simp
  also have "\<dots> = (1 ## (t2 \<otimes> t2)) \<otimes> (1 ## (t2 \<otimes> t2))" unfolding t2.code[symmetric] ..
  also have "\<dots> = (1 ## stl t2) \<otimes> (1 ## stl t2)" by simp
  finally show "stl t2 = (1 ## stl t2) \<otimes> (1 ## stl t2)" .
qed

section \<open>Properties of @{term pls} and @{term prd}\<close>

lemma pls_assoc[ac_simps]: "s \<oplus> t \<oplus> u = s \<oplus> (t \<oplus> u)"
  by (coinduction arbitrary: s t u) auto

lemma pls_comm[ac_simps]: "s \<oplus> t = t \<oplus> s"
  by (coinduction arbitrary: s t) auto

lemma pls_ac[ac_simps]: "s \<oplus> (t \<oplus> u) = t \<oplus> (s \<oplus> u)"
  using pls_assoc pls_comm by auto

lemma prd_distribR: "(s \<oplus> t) \<otimes> u = s \<otimes> u \<oplus> t \<otimes> u"
  apply (coinduction arbitrary: s t u rule: stream.coinduct_upto)
  apply safe
  subgoal by (simp add: algebra_simps)
  subgoal for s t u
  proof -
    let ?l = "\<lambda>s t u. (s \<oplus> t) \<otimes> u"
    let ?r = "\<lambda>s t u. s \<otimes> u \<oplus> t \<otimes> u"
    let ?R = "\<lambda>l r. \<exists>s t u. l = ?l s t u \<and> r = ?r s t u"
    define Rcl (infixl "~~" 35) where [simp]: "Rcl = stream.v4.congclp ?R"
    note stream.cong_refl[intro] stream.cong_base[intro] stream.cong_pls[intro]
    have [trans]: "\<And>s t u. s ~~ t \<Longrightarrow> t ~~ u \<Longrightarrow> s ~~ u" by (auto intro: stream.cong_trans)

    have "stl (?l s t u) ~~ ?l (stl s) (stl t) u \<oplus> ?l s t (stl u)"
      by auto
    also
    have "?l (stl s) (stl t) u \<oplus> ?l s t (stl u) ~~ ?r (stl s) (stl t) u \<oplus> ?r s t (stl u)"
      by fastforce
    also
    have "?r (stl s) (stl t) u \<oplus> ?r s t (stl u) ~~ stl (?r s t u)"
      by (auto simp: ac_simps)
    finally show ?thesis by simp
  qed
  done

lemma prd_comm: "s \<otimes> t = t \<otimes> s"
  apply (coinduction arbitrary: s t rule: stream.coinduct_upto)
  apply safe
  subgoal by simp
  subgoal for s t
    by (auto simp: algebra_simps pls_comm[of "stl s \<otimes> t"] intro: stream.cong_intros)
  done

lemma prd_distribL: "s \<otimes> (t \<oplus> u) = s \<otimes> t \<oplus> s \<otimes> u"
  using prd_comm prd_distribR by auto

lemma prd_assoc[ac_simps]: "s \<otimes> (t \<otimes> u) = s \<otimes> t \<otimes> u"
  by (coinduction arbitrary: s t u rule: stream.coinduct_upto)
    (auto intro: stream.cong_base intro!: stream.cong_pls simp: prd_distribL prd_distribR ac_simps)

lemma prd_ac[ac_simps]: "s \<otimes> (t \<otimes> u) = t \<otimes> (s \<otimes> u)"
  using prd_assoc prd_comm by force

declare prd_comm[ac_simps]

section \<open>Factorial Proof\<close>

text \<open>Proof that t2 is the stream of factorials (facts 0).\<close>

abbreviation facts :: "nat \<Rightarrow> nat stream" where
  "facts n \<equiv> smap fact (up n)"

value [GHC] "stake 5 (facts 0)"

text \<open>Hint 1: prove this following alternative characterization of facts\<close>
text \<open>Hint 2: you might need more helper lemmas about scale
  (including one nontrivial one about scale and facts)\<close>

abbreviation scale :: "nat \<Rightarrow> nat stream \<Rightarrow> nat stream" where
  "scale n \<equiv> smap (op * n)"

lemma facts_alt: "facts n = fact n ## facts n \<otimes> scale (n + 1) (facts 0)"
  sorry

lemma facts_t2: "facts 0 = t2"
  sorry

end
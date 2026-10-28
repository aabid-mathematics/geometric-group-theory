theory Word_Metric
  imports
    "Free-Groups.Generators"
    Quasi_Isometries
begin

section \<open>Word metric\<close>

(* Am I still using all the helper lemmas after I cleaned up the proofs? *)
(* Reorganize subsections before committing documentation? *)

subsection \<open>Words over a group\<close>

abbreviation g_word_mult :: "('a, 'b) monoid_scheme \<Rightarrow> 'a list \<Rightarrow> 'a"  ("\<pi>\<^bsub>_\<^esub> _")
  where "\<pi>\<^bsub>G\<^esub> w \<equiv> foldr (\<otimes>\<^bsub>G\<^esub>) w \<one>\<^bsub>G\<^esub>"

abbreviation g_word_inverse :: "'a list \<Rightarrow> ('a, 'b) monoid_scheme \<Rightarrow> 'a list"  ("_\<^sup>-\<^sup>1\<^bsub>_\<^esub>")
  where "w\<^sup>-\<^sup>1\<^bsub>G\<^esub> \<equiv> rev (map (m_inv G) w)"

definition g_word_eq_class :: "'a \<Rightarrow> ('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a list set"  ("\<lbrakk>_\<rbrakk>\<^bsub>_,_\<^esub>")
  where "\<lbrakk>g\<rbrakk>\<^bsub>G,S\<^esub> = {w. set w \<subseteq> S \<union> (m_inv G) ` S \<and> (\<pi>\<^bsub>G\<^esub> w) = g}"

definition g_word_length :: "'a \<Rightarrow> ('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> nat"  ("|_|\<^bsub>_,_\<^esub>")
  where "|g|\<^bsub>G,S\<^esub> \<equiv> LEAST n. \<exists>w \<in> \<lbrakk>g\<rbrakk>\<^bsub>G,S\<^esub>. length w = n"

definition minimal_g_word_set :: "'a \<Rightarrow> ('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a list set"
    ("Min\<lbrakk>_\<rbrakk>\<^bsub>_,_\<^esub>")
  where "Min\<lbrakk>g\<rbrakk>\<^bsub>G,S\<^esub> \<equiv> {w. w \<in> \<lbrakk>g\<rbrakk>\<^bsub>G,S\<^esub> \<and> length w = |g|\<^bsub>G,S\<^esub>}"

definition minimal_g_word :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a list"  ("\<gamma>\<^bsub> _,_\<^esub>")
  where "\<gamma>\<^bsub>G,S\<^esub> g \<equiv> (SOME w. w \<in> (Min\<lbrakk>g\<rbrakk>\<^bsub>G,S\<^esub>))"

abbreviation (in group) word_mult :: "'a list \<Rightarrow> 'a"  ("\<pi> _")
  where "\<pi> w \<equiv> \<pi>\<^bsub>G\<^esub> w"

abbreviation (in group) word_inverse :: "'a list \<Rightarrow> 'a list"  ("_\<^sup>-\<^sup>1")
  where "w\<^sup>-\<^sup>1 \<equiv> w\<^sup>-\<^sup>1\<^bsub>G\<^esub>"

abbreviation (in group) word_eq_class :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a list set"  ("\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>")
  where "\<lbrakk>g\<rbrakk>\<^bsub>S\<^esub> \<equiv> \<lbrakk>g\<rbrakk>\<^bsub>G,S\<^esub>"

abbreviation (in group) word_length :: "'a \<Rightarrow> 'a set \<Rightarrow> nat"  ("|_|\<^bsub>_\<^esub>")
  where "|g|\<^bsub>S\<^esub> \<equiv> |g|\<^bsub>G,S\<^esub>"

abbreviation (in group) minimal_word_set :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a list set"  ("Min\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>")
  where "Min\<lbrakk>g\<rbrakk>\<^bsub>S\<^esub> \<equiv> Min\<lbrakk>g\<rbrakk>\<^bsub>G,S\<^esub>"

abbreviation (in group) minimal_word :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a list"  ("\<gamma>\<^bsub>_\<^esub>")
  where "\<gamma>\<^bsub>S\<^esub> g \<equiv> \<gamma>\<^bsub>G,S\<^esub> g"


subsection \<open>Products and inverses of words\<close>

lemma (in group) word_in_span:
  assumes "set w \<subseteq> S \<union> m_inv G ` S"
  shows "(\<pi> w) \<in> \<langle>S\<rangle>"
  using assms
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then have IH: "(\<pi> w) \<in> \<langle>S\<rangle>" by simp
  have "a \<in> S \<union> m_inv G ` S" using Cons.prems by simp
  then have a: "a \<in> \<langle>S\<rangle>"
  proof
    assume "a \<in> S"
    then show ?thesis by (rule gen_span.gen_gens)
  next
    assume "a \<in> m_inv G ` S"
    then obtain s where s: "s \<in> S" and as: "a = inv s" by blast
    show ?thesis unfolding as using gen_span.gen_inv[OF gen_span.gen_gens[OF s]] .
  qed
  show ?case using gen_span.gen_mult[OF a IH] by simp
qed

lemma (in group) last_g_word_mult:
  assumes xs: "set xs \<subseteq> carrier G" and ne: "xs \<noteq> []"
  shows "(\<pi> xs) = (\<pi> (butlast xs)) \<otimes> (last xs)"
proof -
  have init_G: "set (butlast xs) \<subseteq> carrier G"
    using xs in_set_butlastD by fast
  have last_G: "set [last xs] \<subseteq> carrier G"
    using subsetD[OF xs last_in_set[OF ne]] by simp
  have "(\<pi> xs) = \<pi> (butlast xs @ [last xs])"
    using append_butlast_last_id[OF ne] by simp
  also have "\<dots> = (\<pi> (butlast xs)) \<otimes> (\<pi> [last xs])"
    using m_concat_append[OF init_G last_G] .
  also have "\<dots> = (\<pi> (butlast xs)) \<otimes> (last xs)"
    using last_G by simp
  finally show ?thesis .
qed

lemma (in group) g_word_inverse_dist:
  assumes "set (xs @ ys) \<subseteq> carrier G"
  shows "(xs @ ys)\<^sup>-\<^sup>1 = (ys\<^sup>-\<^sup>1) @ (xs\<^sup>-\<^sup>1)"
  by simp

lemma (in group) g_word_inverse_invol:
  assumes "set xs \<subseteq> carrier G"
  shows "(xs\<^sup>-\<^sup>1)\<^sup>-\<^sup>1 = xs"
  using assms by (induction xs) simp_all

lemma (in group) g_word_inverse_is_inverse:
  assumes "set xs \<subseteq> carrier G"
  shows "inv (\<pi> xs) = \<pi> (xs\<^sup>-\<^sup>1)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have a: "a \<in> carrier G" and xs: "set xs \<subseteq> carrier G" by simp_all
  have inv_xs: "set (xs\<^sup>-\<^sup>1) \<subseteq> carrier G" and inv_a: "set [inv a] \<subseteq> carrier G"
    using xs a by auto
  have "inv (\<pi> (a # xs)) = inv (a \<otimes> (\<pi> xs))"
    by simp
  also have "\<dots> = inv (\<pi> xs) \<otimes> inv a"
    using inv_mult_group[OF a m_concat_closed[OF xs]] .
  also have "\<dots> = (\<pi> (xs\<^sup>-\<^sup>1)) \<otimes> (\<pi> [inv a])"
    using Cons.IH[OF xs] a by simp
  also have "\<dots> = \<pi> ((xs\<^sup>-\<^sup>1) @ [inv a])"
    using m_concat_append[OF inv_xs inv_a, symmetric] .
  also have "\<dots> = \<pi> ((a # xs)\<^sup>-\<^sup>1)"
    by simp
  finally show ?case .
qed

lemma (in group) inverse_preserves_gens:
  assumes S: "S \<subseteq> carrier G" and A: "A \<subseteq> S \<union> m_inv G ` S"
  shows "m_inv G ` A \<subseteq> S \<union> m_inv G ` S"
proof
  fix x
  assume "x \<in> m_inv G ` A"
  then obtain a where a: "a \<in> S \<union> m_inv G ` S" and x: "x = inv a"
    using A by blast
  show "x \<in> S \<union> m_inv G ` S"
    using a x S by auto
qed

lemma (in group) g_word_inverse_preserves_length: "length xs = length (xs\<^sup>-\<^sup>1)"
  by simp

lemma (in group) g_word_inverse_preserves_gens:
  assumes "S \<subseteq> carrier G" and "set xs \<subseteq> S \<union> m_inv G ` S"
  shows "set (xs\<^sup>-\<^sup>1) \<subseteq> S \<union> m_inv G ` S"
  using inverse_preserves_gens[OF assms] by simp

lemma (in group) gen_word_closed:
  assumes "S \<subseteq> carrier G" and "set w \<subseteq> S \<union> m_inv G ` S"
  shows "set w \<subseteq> carrier G"
  using assms by auto


subsection \<open>Words representing an element\<close>

lemma (in group) gen_word_exists_in_span:
  assumes S: "S \<subseteq> carrier G" and g: "g \<in> \<langle>S\<rangle>"
  shows "\<exists>w. set w \<subseteq> S \<union> m_inv G ` S \<and> (\<pi> w) = g"
  using g
proof (induction rule: gen_span.induct)
  case gen_one
  show ?case by (rule exI[of _ "[]"]) simp
next
  case (gen_gens x)
  have "x \<in> carrier G" using subsetD[OF S gen_gens] .
  then have "set [x] \<subseteq> S \<union> m_inv G ` S \<and> (\<pi> [x]) = x"
    using gen_gens by simp
  then show ?case by (rule exI)
next
  case (gen_inv x)
  then obtain w where w: "set w \<subseteq> S \<union> m_inv G ` S" "(\<pi> w) = x" by blast
  have "(\<pi> (w\<^sup>-\<^sup>1)) = inv x"
    using g_word_inverse_is_inverse[OF gen_word_closed[OF S w(1)], symmetric] w(2) by simp
  moreover have "set (w\<^sup>-\<^sup>1) \<subseteq> S \<union> m_inv G ` S"
    using g_word_inverse_preserves_gens[OF S w(1)] .
  ultimately show ?case by blast
next
  case (gen_mult x y)
  then obtain u v where u: "set u \<subseteq> S \<union> m_inv G ` S" "(\<pi> u) = x"
    and v: "set v \<subseteq> S \<union> m_inv G ` S" "(\<pi> v) = y"
    by blast
  have "(\<pi> (u @ v)) = (\<pi> u) \<otimes> (\<pi> v)"
    using m_concat_append[OF gen_word_closed[OF S u(1)] gen_word_closed[OF S v(1)]] .
  also have "\<dots> = x \<otimes> y"
    using u(2) v(2) by simp
  finally have "(\<pi> (u @ v)) = x \<otimes> y" .
  moreover have "set (u @ v) \<subseteq> S \<union> m_inv G ` S"
    using u(1) v(1) by simp
  ultimately show ?case by blast
qed

lemma (in group) same_word_class:
  assumes "xs \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>" and "ys \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>"
  shows "(\<pi> xs) = (\<pi> ys)"
  using assms unfolding g_word_eq_class_def by simp

lemma (in group) gen_word_exists:
  assumes S: "S \<subseteq> carrier G"
    and gen: "carrier G = \<langle>S\<rangle>"
    and g: "g \<in> carrier G"
  shows "\<exists>w. (set w \<subseteq> S \<union> m_inv G ` S) \<and> (\<pi> w) = g"
  using gen_word_exists_in_span[OF S g[unfolded gen]] . (*Standard use of unfolded?*)

lemma (in group) word_eq_class_nonempty:
  assumes "S \<subseteq> carrier G"
    and "carrier G = \<langle>S\<rangle>"
    and "g \<in> carrier G"
  shows "\<lbrakk>g\<rbrakk>\<^bsub>S\<^esub> \<noteq> {}"
  using gen_word_exists[OF assms] unfolding g_word_eq_class_def by auto


subsection \<open>Word length and minimal words\<close>

lemma (in group) minimal_word_set_nonempty:
  assumes "S \<subseteq> carrier G"
    and "carrier G = \<langle>S\<rangle>"
    and "g \<in> carrier G"
  shows "Min\<lbrakk>g\<rbrakk>\<^bsub>S\<^esub> \<noteq> {}"
proof -
  have ex: "\<exists>n. \<exists>w \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>. length w = n"
    using word_eq_class_nonempty[OF assms] by blast
  have "\<exists>w \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>. length w = |g|\<^bsub>S\<^esub>"
    unfolding g_word_length_def by (rule LeastI_ex[OF ex])
  then show ?thesis unfolding minimal_g_word_set_def by auto
qed

lemma (in group) id_zero_length: "|\<one>|\<^bsub>S\<^esub> = 0"
  unfolding g_word_length_def by (simp add: g_word_eq_class_def)

lemma (in group) word_length_less_eq:
  assumes "xs \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>"
  shows "|g|\<^bsub>S\<^esub> \<le> length xs"
proof -
  have "\<exists>w \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>. length w = length xs" using assms by blast
  then show ?thesis unfolding g_word_length_def 
    by (rule Least_le[of "\<lambda>n. \<exists>w \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>. length w = n" "length xs"])
qed

lemma (in group) minimal_word_word_length:
  assumes "w \<in> Min\<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>"
  shows "length w = |g|\<^bsub>S\<^esub>"
  using assms unfolding minimal_g_word_set_def by simp

lemma (in group) minimal_word_exists:
  assumes "S \<subseteq> carrier G"
    and "carrier G = \<langle>S\<rangle>"
    and "g \<in> carrier G"
  shows "(\<gamma>\<^bsub>S\<^esub> g) \<in> Min\<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>"
  unfolding minimal_g_word_def some_in_eq 
  using minimal_word_set_nonempty[OF assms] .

lemma (in group) minimal_word_length:
  assumes "S \<subseteq> carrier G"
    and "carrier G = \<langle>S\<rangle>"
    and "g \<in> carrier G"
  shows "length (\<gamma>\<^bsub>S\<^esub> g) = |g|\<^bsub>S\<^esub>"
  using minimal_word_word_length[OF minimal_word_exists[OF assms]] .

lemma (in group) minimal_word_mult:
  assumes "S \<subseteq> carrier G"
    and "carrier G = \<langle>S\<rangle>"
    and "g \<in> carrier G"
  shows "\<pi> (\<gamma>\<^bsub>S\<^esub> g) = g"
  using minimal_word_exists[OF assms]
  unfolding minimal_g_word_set_def g_word_eq_class_def by simp

lemma (in group) minimal_word_eq_word_length:
  assumes "S \<subseteq> carrier G"
    and "carrier G = \<langle>S\<rangle>"
    and "g \<in> carrier G"
  shows "\<exists>w. (set w \<subseteq> S \<union> m_inv G ` S) \<and> (\<pi> w) = g \<and> (length w) = |g|\<^bsub>S\<^esub>"
  using minimal_word_exists[OF assms]
  unfolding minimal_g_word_set_def g_word_eq_class_def by auto

lemma (in group) minimal_word_set_min_length:
  assumes w: "w \<in> Min\<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>" and xs: "xs \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>"
  shows "length w \<le> length xs"
  using minimal_word_word_length[OF w] word_length_less_eq[OF xs] by simp

lemma (in group) minimal_word_min_length:
  assumes S: "S \<subseteq> carrier G"
    and gen: "carrier G = \<langle>S\<rangle>"
    and g: "g \<in> carrier G"
    and xs: "xs \<in> \<lbrakk>g\<rbrakk>\<^bsub>G,S\<^esub>"
  shows "length (\<gamma>\<^bsub>S\<^esub> g) \<le> length xs"
  using minimal_word_set_min_length[OF minimal_word_exists[OF S gen g] xs] .

lemma (in group) inv_g_word_eq_class:
  assumes S: "S \<subseteq> carrier G" and w: "w \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>"
  shows "w\<^sup>-\<^sup>1 \<in> \<lbrakk>inv g\<rbrakk>\<^bsub>S\<^esub>"
proof -
  have ws: "set w \<subseteq> S \<union> m_inv G ` S" and wg: "(\<pi> w) = g"
    using w unfolding g_word_eq_class_def by simp_all
  have "(\<pi> (w\<^sup>-\<^sup>1)) = inv g"
    using g_word_inverse_is_inverse[OF gen_word_closed[OF S ws]] wg by simp
  moreover have "set (w\<^sup>-\<^sup>1) \<subseteq> S \<union> m_inv G ` S"
    using g_word_inverse_preserves_gens[OF S ws] .
  ultimately show ?thesis unfolding g_word_eq_class_def by simp
qed

lemma (in group) inv_word_length_eq:
  assumes S: "S \<subseteq> carrier G"
    and gen: "carrier G = \<langle>S\<rangle>"
    and g: "g \<in> carrier G"
  shows "|g|\<^bsub>S\<^esub> = |inv g|\<^bsub>S\<^esub>"
proof -
  have le: "|h|\<^bsub>S\<^esub> \<le> |inv h|\<^bsub>S\<^esub>" if h: "h \<in> carrier G" for h
  proof -
    have ih: "inv h \<in> carrier G" using h by simp
    have w: "(\<gamma>\<^bsub>S\<^esub> (inv h)) \<in> \<lbrakk>inv h\<rbrakk>\<^bsub>S\<^esub>"
      using minimal_word_exists[OF S gen ih] unfolding minimal_g_word_set_def by simp
    have "(\<gamma>\<^bsub>S\<^esub> (inv h))\<^sup>-\<^sup>1 \<in> \<lbrakk>h\<rbrakk>\<^bsub>S\<^esub>"
      using inv_g_word_eq_class[OF S w] h by simp
    then have "|h|\<^bsub>S\<^esub> \<le> length ((\<gamma>\<^bsub>S\<^esub> (inv h))\<^sup>-\<^sup>1)"
      by (rule word_length_less_eq)
    also have "\<dots> = |inv h|\<^bsub>S\<^esub>"
      using minimal_word_length[OF S gen ih] by simp
    finally show ?thesis .
  qed
  show ?thesis using le[OF g] le[of "inv g"] g by simp
qed

lemma (in group) word_length_0_iff_id:
  assumes "S \<subseteq> carrier G"
    and "carrier G = \<langle>S\<rangle>"
    and "g \<in> carrier G"
  shows "|g|\<^bsub>S\<^esub> = 0 \<longleftrightarrow> (g = \<one>)"
proof
  assume "|g|\<^bsub>S\<^esub> = 0"
  then have "\<gamma>\<^bsub>S\<^esub> g = []"
    using minimal_word_length[OF assms] by simp
  then show "g = \<one>"
    using minimal_word_mult[OF assms] by simp
next
  assume "g = \<one>"
  then show "|g|\<^bsub>S\<^esub> = 0"
    using id_zero_length by simp
qed

lemma (in group) word_length_subadditivity:
  assumes S: "S \<subseteq> carrier G"
    and gen: "carrier G = \<langle>S\<rangle>"
    and a: "a \<in> carrier G"
    and b: "b \<in> carrier G"
  shows "|a \<otimes> b|\<^bsub>S\<^esub> \<le> |a|\<^bsub>S\<^esub> + |b|\<^bsub>S\<^esub>"
proof -
  obtain u where u: "set u \<subseteq> S \<union> m_inv G ` S" "(\<pi> u) = a" "length u = |a|\<^bsub>S\<^esub>"
    using minimal_word_eq_word_length[OF S gen a] by blast
  obtain v where v: "set v \<subseteq> S \<union> m_inv G ` S" "(\<pi> v) = b" "length v = |b|\<^bsub>S\<^esub>"
    using minimal_word_eq_word_length[OF S gen b] by blast
  have "(\<pi> (u @ v)) = (\<pi> u) \<otimes> (\<pi> v)"
    using m_concat_append[OF gen_word_closed[OF S u(1)] gen_word_closed[OF S v(1)]] .
  also have "\<dots> = a \<otimes> b"
    using u(2) v(2) by simp
  finally have "u @ v \<in> \<lbrakk>a \<otimes> b\<rbrakk>\<^bsub>S\<^esub>"
    using u(1) v(1) unfolding g_word_eq_class_def by simp
  then have "|a \<otimes> b|\<^bsub>S\<^esub> \<le> length (u @ v)"
    by (rule word_length_less_eq)
  also have "\<dots> = |a|\<^bsub>S\<^esub> + |b|\<^bsub>S\<^esub>"
    using u(3) v(3) by simp
  finally show ?thesis .
qed


subsection \<open>The word metric\<close>

definition g_word_metric :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"  ("d\<^bsub>_,_\<^esub>")
  where "d\<^bsub>G,S\<^esub> g h \<equiv>
           if g \<in> carrier G \<and> h \<in> carrier G then |(inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h|\<^bsub>G,S\<^esub> else 0"

abbreviation (in group) word_metric :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"  ("d\<^bsub>_\<^esub>")
  where "d\<^bsub>S\<^esub> g h \<equiv> d\<^bsub>G,S\<^esub> g h"

lemma (in group) word_metric_comm:
  assumes S: "S \<subseteq> carrier G" and gen: "carrier G = \<langle>S\<rangle>"
  shows "d\<^bsub>S\<^esub> x y = d\<^bsub>S\<^esub> y x"
proof (cases "x \<in> carrier G \<and> y \<in> carrier G")
  case True
  then have x: "x \<in> carrier G" and y: "y \<in> carrier G" by simp_all
  have h: "inv x \<otimes> y \<in> carrier G" using x y by simp
  have "d\<^bsub>S\<^esub> x y = |inv x \<otimes> y|\<^bsub>S\<^esub>"
    using x y unfolding g_word_metric_def by simp
  also have "\<dots> = |inv (inv x \<otimes> y)|\<^bsub>S\<^esub>"
    using inv_word_length_eq[OF S gen h] by simp
  also have "\<dots> = |inv y \<otimes> x|\<^bsub>S\<^esub>"
    using x y inv_mult_group by simp
  also have "\<dots> = d\<^bsub>S\<^esub> y x"
    using x y unfolding g_word_metric_def by simp
  finally show ?thesis .
next
  case False
  then show ?thesis unfolding g_word_metric_def by auto
qed

lemma (in group) word_metric_zero:
  assumes S: "S \<subseteq> carrier G"
    and gen: "carrier G = \<langle>S\<rangle>"
    and x: "x \<in> carrier G"
    and y: "y \<in> carrier G"
  shows "d\<^bsub>S\<^esub> x y = 0 \<longleftrightarrow> x = y"
proof -
  have h: "inv x \<otimes> y \<in> carrier G" using x y by simp
  have "d\<^bsub>S\<^esub> x y = 0 \<longleftrightarrow> |inv x \<otimes> y|\<^bsub>S\<^esub> = 0"
    using x y unfolding g_word_metric_def by simp
  also have "\<dots> \<longleftrightarrow> inv x \<otimes> y = \<one>"
    using word_length_0_iff_id[OF S gen h] .
  also have "\<dots> \<longleftrightarrow> x = y"
  proof
    assume "inv x \<otimes> y = \<one>"
    then have "inv x = inv y" using x y inv_equality by simp
    then show "x = y" using x y inv_inv  by fastforce
  next
    assume "x = y"
    then show "inv x \<otimes> y = \<one>" using y by simp
  qed
  finally show ?thesis .
qed

lemma (in group) word_metric_triangle:
  assumes S: "S \<subseteq> carrier G"
    and gen: "carrier G = \<langle>S\<rangle>"
    and x: "x \<in> carrier G"
    and y: "y \<in> carrier G"
    and z: "z \<in> carrier G"
  shows "(d\<^bsub>S\<^esub> x z) \<le> (d\<^bsub>S\<^esub> x y) + (d\<^bsub>S\<^esub> y z)"
proof -
  have xy: "inv x \<otimes> y \<in> carrier G" and yz: "inv y \<otimes> z \<in> carrier G"
    using x y z by simp_all
  have decomp: "inv x \<otimes> z = (inv x \<otimes> y) \<otimes> (inv y \<otimes> z)"
    using x y z inv_closed inv_solve_left m_assoc yz by metis
  have "|inv x \<otimes> z|\<^bsub>S\<^esub> \<le> |inv x \<otimes> y|\<^bsub>S\<^esub> + |inv y \<otimes> z|\<^bsub>S\<^esub>"
    unfolding decomp using word_length_subadditivity[OF S gen xy yz] .
  moreover have "d\<^bsub>S\<^esub> x z = |inv x \<otimes> z|\<^bsub>S\<^esub>"
    and "d\<^bsub>S\<^esub> x y = |inv x \<otimes> y|\<^bsub>S\<^esub>"
    and "d\<^bsub>S\<^esub> y z = |inv y \<otimes> z|\<^bsub>S\<^esub>"
    using x y z unfolding g_word_metric_def by simp_all
  ultimately show ?thesis by linarith
qed

lemma (in group) word_metric_is_metric:
  assumes "S \<subseteq> carrier G"
    and "carrier G = \<langle>S\<rangle>"
  shows "Metric_space (carrier G) (d\<^bsub>S\<^esub>)"
proof unfold_locales
  show "0 \<le> d\<^bsub>S\<^esub> x y" for x y
    unfolding g_word_metric_def by simp
  show "d\<^bsub>S\<^esub> x y = d\<^bsub>S\<^esub> y x" for x y
    by (rule word_metric_comm[OF assms])
  show "d\<^bsub>S\<^esub> x y = 0 \<longleftrightarrow> x = y"
    if "x \<in> carrier G" and "y \<in> carrier G" for x y
    by (rule word_metric_zero[OF assms that])
  show "d\<^bsub>S\<^esub> x z \<le> d\<^bsub>S\<^esub> x y + d\<^bsub>S\<^esub> y z"
    if "x \<in> carrier G" and "y \<in> carrier G" and "z \<in> carrier G" for x y z
    by (rule word_metric_triangle[OF assms that])
qed

subsection \<open>Changing the generating set\<close>

lemma (in group) finite_set_word_length_bounded:
  assumes "finite S"
  shows "\<exists>K. \<forall>s \<in> S. |s|\<^bsub>T\<^esub> \<le> K \<and> K \<ge> 0"
proof -
  define K where "K = Max (insert 0 ((\<lambda>s. |s|\<^bsub>T\<^esub>) ` S))"
  have "|s|\<^bsub>T\<^esub> \<le> K" if "s \<in> S" for s
    unfolding K_def using assms that Max_ge by auto
  then show ?thesis by blast
qed

lemma (in group) word_length_word_mult_bound:
  assumes T: "T \<subseteq> carrier G"
    and gen: "carrier G = \<langle>T\<rangle>"
    and wG: "set w \<subseteq> carrier G"
  shows "|(\<pi> w)|\<^bsub>T\<^esub> \<le> sum_list (map (\<lambda>x. |x|\<^bsub>T\<^esub>) w)"
  using wG
proof (induction w)
  case Nil
  then show ?case using id_zero_length by simp
next
  case (Cons a w)
  then have a: "a \<in> carrier G" and w: "set w \<subseteq> carrier G" by simp_all
  have "|(\<pi> (a # w))|\<^bsub>T\<^esub> = |a \<otimes> (\<pi> w)|\<^bsub>T\<^esub>"
    by simp
  also have "\<dots> \<le> |a|\<^bsub>T\<^esub> + |(\<pi> w)|\<^bsub>T\<^esub>"
    using word_length_subadditivity[OF T gen a m_concat_closed[OF w]] .
  also have "\<dots> \<le> |a|\<^bsub>T\<^esub> + sum_list (map (\<lambda>x. |x|\<^bsub>T\<^esub>) w)"
    using Cons.IH[OF w] by simp
  finally show ?case by simp
qed

(* MOVE? *)
lemma sum_list_le_const:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "\<forall>x \<in> set w. f x \<le> K"
  shows "sum_list (map f w) \<le> K * length w"
  using assms
proof(induction w)
  case Nil
  then show ?case by fastforce
next
  case (Cons a w)
  have rhs: "K * length (a # w) = (K * length w) + K" by simp
  have lhs: "sum_list (map f (a#w)) = f a + sum_list (map f w)" by force
  have "sum_list (map f w) \<le> (K * length w)" using Cons by simp
  moreover have "f a \<le> K" using Cons(2) by simp
  ultimately show ?case unfolding rhs lhs by linarith
qed

lemma (in group) change_generator_word_length_bounded:
  assumes S: "S \<subseteq> carrier G"
    and fin: "finite S"
    and genS: "carrier G = \<langle>S\<rangle>"
    and T: "T \<subseteq> carrier G"
    and genT: "carrier G = \<langle>T\<rangle>"
  shows "\<exists>K. \<forall>g \<in> carrier G. |g|\<^bsub>T\<^esub> \<le> K * |g|\<^bsub>S\<^esub> \<and> K \<ge> 0"
proof -
  obtain K where K: "\<forall>s \<in> S. |s|\<^bsub>T\<^esub> \<le> K"
    using finite_set_word_length_bounded[of S T, OF fin] by blast

  have gens: "|x|\<^bsub>T\<^esub> \<le> K" if "x \<in> S \<union> m_inv G ` S" for x
    using that
  proof
    assume "x \<in> S"
    then show ?thesis using K by blast
  next
    assume "x \<in> m_inv G ` S"
    then obtain s where s: "s \<in> S" and x: "x = inv s" by blast
    have "|x|\<^bsub>T\<^esub> = |s|\<^bsub>T\<^esub>"
      using inv_word_length_eq[OF T genT subsetD[OF S s]] x by simp
    then show ?thesis using K s by simp
  qed

  have "|g|\<^bsub>T\<^esub> \<le> K * |g|\<^bsub>S\<^esub>" if g: "g \<in> carrier G" for g
  proof -
    obtain w where w: "set w \<subseteq> S \<union> m_inv G ` S" "(\<pi> w) = g" "length w = |g|\<^bsub>S\<^esub>"
      using minimal_word_eq_word_length[OF S genS g] by blast
    have "|g|\<^bsub>T\<^esub> = |(\<pi> w)|\<^bsub>T\<^esub>"
      using w(2) by simp
    also have "\<dots> \<le> sum_list (map (\<lambda>x. |x|\<^bsub>T\<^esub>) w)"
      using word_length_word_mult_bound[OF T genT gen_word_closed[OF S w(1)]] .
    also have "\<dots> \<le> K * length w"
      using sum_list_le_const[of "w" "\<lambda>x. |x|\<^bsub>T\<^esub>" "K"] gens w(1) by fast
    also have "\<dots> = K * |g|\<^bsub>S\<^esub>"
      using w(3) by simp
    finally show ?thesis .
  qed
  then show ?thesis by blast
qed

lemma (in group) word_metric_bilipschitz:
  assumes finS: "finite S"
    and S: "S \<subseteq> carrier G"
    and genS: "carrier G = \<langle>S\<rangle>"
    and finT: "finite T"
    and T: "T \<subseteq> carrier G"
    and genT: "carrier G = \<langle>T\<rangle>"
  shows "\<exists>K \<ge> 1. \<forall>x \<in> carrier G. \<forall>y \<in> carrier G.
           d\<^bsub>T\<^esub> x y \<le> K * d\<^bsub>S\<^esub> x y \<and> d\<^bsub>S\<^esub> x y \<le> K * d\<^bsub>T\<^esub> x y"
proof -
  obtain K1 where K1: "\<forall>g \<in> carrier G. |g|\<^bsub>T\<^esub> \<le> K1 * |g|\<^bsub>S\<^esub>"
    using change_generator_word_length_bounded[OF S finS genS T genT] by blast
  obtain K2 where K2: "\<forall>g \<in> carrier G. |g|\<^bsub>S\<^esub> \<le> K2 * |g|\<^bsub>T\<^esub>"
    using change_generator_word_length_bounded[OF T finT genT S genS] by blast
  define K where "K = max 1 (real (max K1 K2))"
  have K_ge: "K \<ge> 1" and K1_le: "real K1 \<le> K" and K2_le: "real K2 \<le> K"
    unfolding K_def by auto

  have scale: "d\<^bsub>B\<^esub> x y \<le> K * d\<^bsub>A\<^esub> x y"
    if bound: "\<forall>g \<in> carrier G. |g|\<^bsub>B\<^esub> \<le> L * |g|\<^bsub>A\<^esub>" and L_le: "real L \<le> K"
      and x: "x \<in> carrier G" and y: "y \<in> carrier G"
    for A B L x y
  proof -
    let ?h = "inv x \<otimes> y"
    have h: "?h \<in> carrier G" using x y by simp
    have "d\<^bsub>B\<^esub> x y = |(?h)|\<^bsub>B\<^esub>"
      using x y unfolding g_word_metric_def by simp
    also have "\<dots> \<le> L * |(?h)|\<^bsub>A\<^esub>"
      using bound h of_nat_le_iff by blast
    also have "\<dots> \<le> K * |(?h)|\<^bsub>A\<^esub>"
      using L_le mult_right_mono by fastforce
    also have "\<dots> = K * d\<^bsub>A\<^esub> x y"
      using x y unfolding g_word_metric_def by simp
    finally show ?thesis .
  qed

  have "d\<^bsub>T\<^esub> x y \<le> K * d\<^bsub>S\<^esub> x y \<and> d\<^bsub>S\<^esub> x y \<le> K * d\<^bsub>T\<^esub> x y"
    if "x \<in> carrier G" and "y \<in> carrier G" for x y
    using scale[OF K1 K1_le that] scale[OF K2 K2_le that] .. (* Two dots vs one dot? *)
  then show ?thesis using K_ge by blast
qed

(* Move to quasi-isometry? *)
lemma bilipschitz_id_quasi_isometry:
  assumes M1: "Metric_space M d1"
    and M2: "Metric_space M d2"
    and K: "(K::real) \<ge> 1"
    and bl: "\<forall>x \<in> M. \<forall>y \<in> M. d2 x y \<le> K * d1 x y \<and> d1 x y \<le> K * d2 x y"
  shows "quasi_isometry (metric (M, d1)) (metric (M, d2)) id"
proof -
  let ?X = "metric (M, d1)" and ?Y = "metric (M, d2)"
  note X = Metric_space.mspace_metric[OF M1] Metric_space.mdist_metric[OF M1]
  note Y = Metric_space.mspace_metric[OF M2] Metric_space.mdist_metric[OF M2]
  (* note vs let? facts vs terms? *)

  have emb: "quasi_isometric_embedding ?X ?Y id"
  proof (rule quasi_isometric_embeddingI[where C = 0, OF _ K order_refl])
    show "id ` mspace ?X \<subseteq> mspace ?Y"
      using X Y by simp
    show "mdist ?Y (id a) (id b) \<le> K * mdist ?X a b + 0"
      if "a \<in> mspace ?X" and "b \<in> mspace ?X" for a b
      using bl that X Y by auto
    show "mdist ?X a b \<le> K * (mdist ?Y (id a) (id b) + 0)"
      if "a \<in> mspace ?X" and "b \<in> mspace ?X" for a b
      using bl that X Y by auto
  qed

  have surj: "\<exists>x \<in> mspace ?X. mdist ?Y (id x) y \<le> 0" if "y \<in> mspace ?Y" for y
  proof (rule bexI[where x = y])
    from that have y: "y \<in> M" using Y by simp
    show "mdist ?Y (id y) y \<le> 0"
      using Metric_space.zero[OF M2 y y] Y by simp
    show "y \<in> mspace ?X"
      using X y by simp
  qed

  show ?thesis
    by (rule quasi_isometryI[OF emb order_refl surj])
qed

lemma (in group) word_metric_quasi_isometric:
  assumes finA: "finite A"
    and A: "A \<subseteq> carrier G"
    and genA: "carrier G = \<langle>A\<rangle>"
    and finB: "finite B"
    and B: "B \<subseteq> carrier G"
    and genB: "carrier G = \<langle>B\<rangle>"
  shows "quasi_isometric (metric ((carrier G), (d\<^bsub>A\<^esub>))) (metric ((carrier G), (d\<^bsub>B\<^esub>)))"
proof -
  obtain K where K: "K \<ge> 1"
    and bl: "\<forall>x \<in> carrier G. \<forall>y \<in> carrier G.
               d\<^bsub>B\<^esub> x y \<le> K * d\<^bsub>A\<^esub> x y \<and> d\<^bsub>A\<^esub> x y \<le> K * d\<^bsub>B\<^esub> x y"
    using word_metric_bilipschitz[OF assms] by blast
  have "quasi_isometry (metric (carrier G, d\<^bsub>A\<^esub>)) (metric (carrier G, d\<^bsub>B\<^esub>)) id"
    by (rule bilipschitz_id_quasi_isometry[OF word_metric_is_metric[OF A genA]
                                               word_metric_is_metric[OF B genB] K bl])
  then show ?thesis unfolding quasi_isometric_def by blast
qed

end

theory Isometric_Actions
  imports "HOL-Algebra.Group_Action"
          Quasi_Isometries
begin

(* Clean-up sections? *)

context Metric_space
begin

definition self_isometry :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "self_isometry f \<longleftrightarrow> isometry Self Self f"

end

locale isometric_action =
  Metric_space M d +
  group_action G M \<phi>
  for M :: "'a set"
    and d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
    and G
    and \<phi> +
  assumes isometry:
    "\<And>g. g \<in> carrier G \<Longrightarrow> self_isometry (\<phi> g)"
begin

abbreviation action_on :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 100) where
  "g \<cdot> x \<equiv> \<phi> g x"

end

sublocale isometric_action \<subseteq> group G
  by (rule group_hom.axioms(1)[OF group_hom])

section \<open>Orbit maps\<close>

context isometric_action
begin

(* How to prioritize abbreviations in the output box? *)
(* Will it be confusing for readers? *)
abbreviation orbit_map where
  "orbit_map x \<equiv> \<lambda>g. g \<cdot> x"

lemma act_dist:
  assumes g: "g \<in> carrier G" and x: "x \<in> M" and y: "y \<in> M"
  shows "d (g \<cdot> x) (g \<cdot> y) = d x y"
proof -
  have iso: "isometric_embedding Self Self (\<phi> g)"
    using isometry[OF g] unfolding self_isometry_def by (rule isometry_embedding)
  have "mdist Self (g \<cdot> x) (g \<cdot> y) = mdist Self x y"
    using isometric_embedding_dist[OF iso, of x y] x y by force
  then show ?thesis by simp
qed

lemma orbit_map_in:
  assumes x: "x \<in> M" and g: "g \<in> carrier G"
  shows "g \<cdot> x \<in> M"
  using element_image[OF g x] by simp

lemma orbit_map_maps:
  assumes x: "x \<in> M"
  shows "orbit_map x ` carrier G \<subseteq> M"
  using orbit_map_in[OF x] by blast

lemma orbit_map_image: "orbit_map x ` carrier G = orbit G \<phi> x"
  unfolding orbit_def by blast

lemma orbit_map_one:
  assumes x: "x \<in> M"
  shows "\<one>\<^bsub>G\<^esub> \<cdot> x = x"
  using x id_eq_one[symmetric] by simp (* Why does simp only work with symmetric? *)

lemma orbit_map_mult:
  assumes x: "x \<in> M" and g: "g \<in> carrier G" and h: "h \<in> carrier G"
  shows "(g \<otimes>\<^bsub>G\<^esub> h) \<cdot> x = g \<cdot> (h \<cdot> x)"
  using composition_rule[OF x g h] . (* Already exists in group action? *)

lemma orbit_map_inv:
  assumes x: "x \<in> M" and g: "g \<in> carrier G"
  shows "(inv\<^bsub>G\<^esub> g) \<cdot> (g \<cdot> x) = x"
  using orbit_sym_aux[OF g x refl] .

lemma orbit_dist_reduce:
  assumes x: "x \<in> M" and g: "g \<in> carrier G" and h: "h \<in> carrier G"
  shows "d (g \<cdot> x) (h \<cdot> x) = d x ((inv\<^bsub>G\<^esub> g \<otimes>\<^bsub>G\<^esub> h) \<cdot> x)"
proof -
  have ig: "inv\<^bsub>G\<^esub> g \<in> carrier G" using inv_closed[OF g] .
  have gx: "g \<cdot> x \<in> M" using orbit_map_in[OF x g] .
  have hx: "h \<cdot> x \<in> M" using orbit_map_in[OF x h] .
  have "d (g \<cdot> x) (h \<cdot> x) = d ((inv\<^bsub>G\<^esub> g) \<cdot> (g \<cdot> x)) ((inv\<^bsub>G\<^esub> g) \<cdot> (h \<cdot> x))"
    using act_dist[OF ig gx hx, symmetric] .
  also have "\<dots> = d x ((inv\<^bsub>G\<^esub> g \<otimes>\<^bsub>G\<^esub> h) \<cdot> x)"
    using orbit_map_inv[OF x g] orbit_map_mult[OF x ig h] by simp
  finally show ?thesis .
qed

lemma orbit_dist_inv:
  assumes x: "x \<in> M" and g: "g \<in> carrier G"
  shows "d x (g \<cdot> x) = d x ((inv\<^bsub>G\<^esub> g) \<cdot> x)"
proof -
  have ig: "inv\<^bsub>G\<^esub> g \<in> carrier G" using inv_closed[OF g] .
  have "d x (g \<cdot> x) = d ((inv\<^bsub>G\<^esub> g) \<cdot> x) ((inv\<^bsub>G\<^esub> g) \<cdot> (g \<cdot> x))"
    using act_dist[OF ig x orbit_map_in[OF x g], symmetric] .
  also have "\<dots> = d ((inv\<^bsub>G\<^esub> g) \<cdot> x) x"
    using orbit_map_inv[OF x g] by simp
  also have "\<dots> = d x ((inv\<^bsub>G\<^esub> g) \<cdot> x)"
    using commute .
  finally show ?thesis .
qed

end

end
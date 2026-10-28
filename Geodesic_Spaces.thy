theory Geodesic_Spaces
  imports Quasi_Isometries
begin


section \<open>Subsets of the real line as metric spaces\<close>

(* Is this the best way to do this? Already done in the libraries? *)
(* Dangers of adding [simp]? Do I know what I'm doing? *)

lemma metric_dist_submetric: "metric (S, dist) = submetric euclidean_metric S"
  by (simp add: submetric_def)

lemma mspace_metric_dist [simp]: "mspace (metric (S, dist)) = S"
  unfolding metric_dist_submetric by simp

lemma mdist_metric_dist [simp]: "mdist (metric (S, dist)) = dist"
  unfolding metric_dist_submetric by simp

lemma mtopology_of_metric_dist [simp]: "mtopology_of (metric (S, dist)) = top_of_set S"
  unfolding metric_dist_submetric mtopology_of_submetric by simp


section \<open>Geodesic segments and geodesic spaces\<close>

context Metric_space
begin

definition geodesic_segment_between :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "geodesic_segment_between S x y \<equiv> (\<exists>g::real \<Rightarrow> 'a. g 0 = x \<and> g (d x y) = y \<and>
                                                           isometric_embedding (metric ({0..d x y}, dist)) Self g \<and>
                                                           S = g ` {0..d x y})"

definition geodesic_segment :: "'a set \<Rightarrow> bool"
  where "geodesic_segment S \<equiv> (\<exists>x y. geodesic_segment_between S x y)"

definition geodesic :: "bool"
  where "geodesic \<longleftrightarrow> (\<forall>x\<in> M. \<forall>y\<in> M. \<exists>S. geodesic_segment_between S x y)"

end

subsection \<open>Geodesic segments\<close>

context Metric_space
begin

lemma geodesic_segment_betweenE:
  assumes "geodesic_segment_between S x y"
  obtains c :: "real \<Rightarrow> 'a" where "c 0 = x" and "c (d x y) = y" and "S = c ` {0..d x y}"
    and "\<And>s. s \<in> {0..d x y} \<Longrightarrow> c s \<in> M"
    and "\<And>s t. s \<in> {0..d x y} \<Longrightarrow> t \<in> {0..d x y} \<Longrightarrow> d (c s) (c t) = \<bar>s - t\<bar>"
proof -
  obtain c where c0: "c 0 = x" and c1: "c (d x y) = y" and S: "S = c ` {0..d x y}"
    and iso: "isometric_embedding (metric ({0..d x y}, dist)) Self c"
    using assms unfolding geodesic_segment_between_def by blast
  have cM: "c s \<in> M" if s: "s \<in> {0..d x y}" for s
    using isometric_embedding_maps[OF iso] s by auto
  have cd: "d (c s) (c t) = \<bar>s - t\<bar>" if s: "s \<in> {0..d x y}" and t: "t \<in> {0..d x y}" for s t
  proof -
    have "mdist Self (c s) (c t) = mdist (metric ({0..d x y}, dist)) s t"
      using isometric_embedding_dist[OF iso] mspace_metric_dist s t by blast (* Cleaner? *)
    then show ?thesis using dist_real_def by simp
  qed
  show thesis using that[OF c0 c1 S cM cd] . (* Am I using "that" correctly for these "obtain" proofs? *)
qed

lemma geodesic_segment_betweenI:
  assumes c0: "c 0 = x" and c1: "c (d x y) = y"
    and cM: "\<And>s. s \<in> {0..d x y} \<Longrightarrow> c s \<in> M"
    and cd: "\<And>s t. s \<in> {0..d x y} \<Longrightarrow> t \<in> {0..d x y} \<Longrightarrow> d (c s) (c t) = \<bar>s - t\<bar>"
  shows "geodesic_segment_between (c ` {0..d x y}) x y"
proof -
  have "isometric_embedding (metric ({0..d x y}, dist)) Self c"
  proof (rule isometric_embeddingI)
    show "c ` mspace (metric ({0..d x y}, dist)) \<subseteq> mspace Self"
      using cM by auto
    show "mdist Self (c a) (c b) = mdist (metric ({0..d x y}, dist)) a b"
      if a: "a \<in> mspace (metric ({0..d x y}, dist))"
        and b: "b \<in> mspace (metric ({0..d x y}, dist))" for a b
    proof -
      have "d (c a) (c b) = \<bar>a - b\<bar>" using a b cd by simp (* OF? *)
      then show ?thesis using dist_real_def by force
    qed
  qed
  then show ?thesis
    unfolding geodesic_segment_between_def using c0 c1 by blast
qed

lemma geodesicE:
  assumes geod: "geodesic" and x: "x \<in> M" and y: "y \<in> M"
  obtains c :: "real \<Rightarrow> 'a" where "c 0 = x" and "c (d x y) = y"
    and "\<And>s. s \<in> {0..d x y} \<Longrightarrow> c s \<in> M"
    and "\<And>s t. s \<in> {0..d x y} \<Longrightarrow> t \<in> {0..d x y} \<Longrightarrow> d (c s) (c t) = \<bar>s - t\<bar>"
proof -
  obtain S where seg: "geodesic_segment_between S x y"
    using geod x y unfolding geodesic_def by blast
  obtain c :: "real \<Rightarrow> 'a" where c0: "c 0 = x" and c1: "c (d x y) = y"
    and "S = c ` {0..d x y}"
    and cM: "\<And>s. s \<in> {0..d x y} \<Longrightarrow> c s \<in> M"
    and cd: "\<And>s t. s \<in> {0..d x y} \<Longrightarrow> t \<in> {0..d x y} \<Longrightarrow> d (c s) (c t) = \<bar>s - t\<bar>"
    using geodesic_segment_betweenE[OF seg] by blast
  show thesis using that[OF c0 c1 cM cd] .
qed

lemma geodesic_chain:
  assumes geod: "geodesic" and x: "x \<in> M" and y: "y \<in> M" and \<epsilon>: "0 < \<epsilon>"
  obtains n :: nat and p :: "nat \<Rightarrow> 'a"
    where "0 < n" and "real n \<le> d x y / \<epsilon> + 2"
      and "p 0 = x" and "p n = y" and "\<And>i. p i \<in> M"
      and "\<And>i. d (p i) (p (Suc i)) \<le> \<epsilon>"
proof -
  let ?L = "d x y"
  obtain c where c0: "c 0 = x" and cL: "c ?L = y"
    and cM: "\<And>s. s \<in> {0..?L} \<Longrightarrow> c s \<in> M"
    and cd: "\<And>s t. s \<in> {0..?L} \<Longrightarrow> t \<in> {0..?L} \<Longrightarrow> d (c s) (c t) = \<bar>s - t\<bar>"
    using geodesicE[OF geod x y] by blast
  have L0: "0 \<le> ?L" using nonneg[of x y] .

  define n where "n = Suc (nat \<lceil>?L / \<epsilon>\<rceil>)"
  have n_pos: "0 < n"
    unfolding n_def by simp
  have ceil: "0 \<le> \<lceil>?L / \<epsilon>\<rceil>"
    using divide_nonneg_pos[OF L0 \<epsilon>] by force
  have n_ge: "?L / \<epsilon> \<le> real n"
    unfolding n_def using real_nat_ceiling_ge[of "?L / \<epsilon>"] by linarith
  have n_le: "real n \<le> ?L / \<epsilon> + 2"
    unfolding n_def of_nat_Suc of_nat_nat[OF ceil]
    using of_int_ceiling_le_add_one[of "?L / \<epsilon>"] by linarith (* Why are arithmetic proofs so tedious? *)

  define p where "p = (\<lambda>i::nat. c (min (real i * \<epsilon>) ?L))"
  have mem: "min (real i * \<epsilon>) ?L \<in> {0..?L}" for i
    using L0 less_imp_le[OF \<epsilon>] by auto
  have pM: "p i \<in> M" for i
    unfolding p_def using cM[OF mem] .
  have p0: "p 0 = x"
    unfolding p_def using min_absorb1[OF L0] c0 by simp
  have pn: "p n = y"
  proof -
    have L_le: "?L \<le> real n * \<epsilon>"
      using n_ge unfolding pos_divide_le_eq[OF \<epsilon>] . (* Nice. *)
    show ?thesis
      using cL unfolding p_def min_absorb2[OF L_le] .
  qed

  have p_step: "d (p i) (p (Suc i)) \<le> \<epsilon>" for i
  proof -
    have "d (p i) (p (Suc i)) = \<bar>min (real i * \<epsilon>) ?L - min (real (Suc i) * \<epsilon>) ?L\<bar>"
      unfolding p_def using cd[OF mem mem] .
    also have "\<dots> \<le> \<epsilon>"
    proof -
      have "real (Suc i) * \<epsilon> = real i * \<epsilon> + \<epsilon>"
        by (simp add: algebra_simps)
      then show ?thesis using \<epsilon> by linarith (* More detail here for readers? *)
    qed
    finally show ?thesis .
  qed
  show thesis using that[of n p, OF n_pos n_le p0 pn pM p_step] .
qed

end

end

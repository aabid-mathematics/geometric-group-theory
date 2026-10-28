theory Quasi_Isometries
  imports "HOL-Analysis.Abstract_Metric_Spaces"

begin

definition isometric_embedding :: "'a metric \<Rightarrow> 'b metric \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "isometric_embedding X Y f \<longleftrightarrow> f ` (mspace X) \<subseteq> (mspace Y)
                                    \<and> (\<forall>a\<in>mspace X. \<forall>b\<in>mspace X. (mdist Y) (f a) (f b) = (mdist X) a b)"

definition isometry :: "'a metric \<Rightarrow> 'b metric \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "isometry X Y f \<longleftrightarrow> isometric_embedding X Y f \<and> f ` (mspace X) = (mspace Y)"

definition isometric :: "'a metric \<Rightarrow> 'b metric \<Rightarrow> bool"
  where "isometric X Y \<longleftrightarrow> (\<exists>f. isometry X Y f)"

(* 1/K vs moving the inequality around for the lower bound? *)
definition quasi_isometric_embedding :: "'a metric \<Rightarrow> 'b metric \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "quasi_isometric_embedding X Y f \<longleftrightarrow> f ` (mspace X) \<subseteq> (mspace Y)
                                          \<and> (\<exists>K \<ge> 1. \<exists>C \<ge> 0. \<forall>a\<in>mspace X. \<forall>b\<in>mspace X.
                                                               ((mdist Y) (f a) (f b) \<le> K * (mdist X) a b + C 
                                                            \<and> (mdist Y) (f a) (f b) \<ge> (1/K) * (mdist X) a b - C))"

definition quasi_isometry :: "'a metric \<Rightarrow> 'b metric \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "quasi_isometry X Y f \<longleftrightarrow> (quasi_isometric_embedding X Y f
                                    \<and> (\<exists>D \<ge> 0. \<forall>y \<in> (mspace Y). \<exists>x \<in> (mspace X). (mdist Y) (f x) y \<le> D))"

definition quasi_isometric :: "'a metric \<Rightarrow> 'b metric \<Rightarrow> bool"
  where "quasi_isometric X Y \<longleftrightarrow> (\<exists>f. quasi_isometry X Y f)"

subsection \<open>Isometries: basic rules\<close>

lemma isometric_embeddingI:
  assumes "f ` mspace X \<subseteq> mspace Y"
      and "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow> mdist Y (f a) (f b) = mdist X a b"
  shows "isometric_embedding X Y f"
  using assms unfolding isometric_embedding_def by blast

lemma isometric_embedding_maps:
  assumes "isometric_embedding X Y f"
  shows "f ` mspace X \<subseteq> mspace Y"
  using assms unfolding isometric_embedding_def by blast

lemma isometric_embedding_dist:
  assumes "isometric_embedding X Y f" and "a \<in> mspace X" and "b \<in> mspace X"
  shows "mdist Y (f a) (f b) = mdist X a b"
  using assms unfolding isometric_embedding_def by blast

lemma isometric_embedding_inj_on:
  assumes "isometric_embedding X Y f"
  shows "inj_on f (mspace X)"
proof (rule inj_onI)
  fix a b assume a: "a \<in> mspace X" and b: "b \<in> mspace X" and eq: "f a = f b"
  have fa: "f a \<in> mspace Y" using isometric_embedding_maps[OF assms(1)] a by blast
  have "mdist X a b = mdist Y (f a) (f b)" using isometric_embedding_dist[OF assms(1) a b, symmetric] .
  also have "\<dots> = 0" using fa eq by auto
  finally show "a = b" using a b by simp
qed

lemma isometric_embedding_comp:
  assumes f: "isometric_embedding X Y f" and g: "isometric_embedding Y Z g"
  shows "isometric_embedding X Z (g \<circ> f)"
proof (rule isometric_embeddingI)
  have fm: "f ` mspace X \<subseteq> mspace Y" using isometric_embedding_maps[OF f] .
  have gm: "g ` mspace Y \<subseteq> mspace Z" using isometric_embedding_maps[OF g] .
  show "(g \<circ> f) ` mspace X \<subseteq> mspace Z" using fm gm by auto
  show "mdist Z ((g \<circ> f) a) ((g \<circ> f) b) = mdist X a b"
    if a: "a \<in> mspace X" and b: "b \<in> mspace X" for a b (* Use this pattern more often? Standard?*)
  proof -
    have fa: "f a \<in> mspace Y" and fb: "f b \<in> mspace Y" using fm a b by auto
    have "mdist Z ((g \<circ> f) a) ((g \<circ> f) b) = mdist Y (f a) (f b)"
      using isometric_embedding_dist[OF g fa fb] by simp
    also have "\<dots> = mdist X a b" using isometric_embedding_dist[OF f a b] .
    finally show ?thesis .
  qed
qed

lemma isometry_embedding:
  assumes "isometry X Y f"
  shows "isometric_embedding X Y f"
  using assms unfolding isometry_def by blast

lemma isometry_image:
  assumes "isometry X Y f"
  shows "f ` mspace X = mspace Y"
  using assms unfolding isometry_def by blast

lemma isometry_bij_betw:
  assumes "isometry X Y f"
  shows "bij_betw f (mspace X) (mspace Y)"
  unfolding bij_betw_def
  using isometric_embedding_inj_on[OF isometry_embedding[OF assms]] isometry_image[OF assms]
  by blast

lemma bij_betw_isometry:
  assumes "isometric_embedding X Y f" and "bij_betw f (mspace X) (mspace Y)"
  shows "isometry X Y f"
  using assms unfolding isometry_def bij_betw_def by blast

subsection \<open>Isometry is an equivalence relation\<close>

lemma isometry_id: "isometry X X id"
proof -
  have "isometric_embedding X X id"
    unfolding isometric_embedding_def by force
  then show ?thesis unfolding isometry_def by simp
qed

lemma isometric_refl: "isometric X X"
  unfolding isometric_def using isometry_id by blast

lemma isometry_comp:
  assumes f: "isometry X Y f" and g: "isometry Y Z g"
  shows "isometry X Z (g \<circ> f)"
proof -
  have "isometric_embedding X Z (g \<circ> f)"
    using  isometric_embedding_comp[OF isometry_embedding[OF f] isometry_embedding[OF g]] .
  moreover have "bij_betw (g \<circ> f) (mspace X) (mspace Z)"
    using bij_betw_trans[OF isometry_bij_betw[OF f] isometry_bij_betw[OF g]] .
  ultimately show ?thesis using bij_betw_isometry by blast
qed

lemma isometric_trans:
  assumes "isometric X Y" and "isometric Y Z"
  shows "isometric X Z"
proof -
  obtain f where f: "isometry X Y f" using assms(1) unfolding isometric_def by blast
  obtain g where g: "isometry Y Z g" using assms(2) unfolding isometric_def by blast
  have "isometry X Z (g \<circ> f)" using f g isometry_comp by blast
  then show ?thesis unfolding isometric_def by blast
qed

lemma isometry_inverse:
  assumes f: "isometry X Y f"
  shows "isometry Y X (inv_into (mspace X) f)"
proof -
  let ?f' = "inv_into (mspace X) f"
  have fbij: "bij_betw f (mspace X) (mspace Y)" using isometry_bij_betw[OF f] .
  have f'bij: "bij_betw ?f' (mspace Y) (mspace X)" using bij_betw_inv_into[OF fbij] .
  then have img: "?f' ` mspace Y = mspace X" unfolding bij_betw_def by simp
  have emb: "isometric_embedding Y X ?f'"
  proof (rule isometric_embeddingI)
    show "?f' ` mspace Y \<subseteq> mspace X" using img by simp
    show "mdist X (?f' a) (?f' b) = mdist Y a b"
      if a: "a \<in> mspace Y" and b: "b \<in> mspace Y" for a b
    proof -
      have f'a: "?f' a \<in> mspace X" and f'b: "?f' b \<in> mspace X" using img a b by auto
      have "mdist X (?f' a) (?f' b) = mdist Y (f (?f' a)) (f (?f' b))"
        using isometric_embedding_dist[OF isometry_embedding[OF f] f'a f'b] by simp (*symmetric?*)
      also have "\<dots> = mdist Y a b"
        using bij_betw_inv_into_right[OF fbij a] bij_betw_inv_into_right[OF fbij b] by simp
      finally show ?thesis .
    qed
  qed
  show ?thesis using bij_betw_isometry[OF emb f'bij]  .
qed

lemma isometric_sym:
  assumes "isometric X Y"
  shows "isometric Y X"
proof -
  obtain f where "isometry X Y f" using assms unfolding isometric_def by blast
  then have "isometry Y X (inv_into (mspace X) f)" by (rule isometry_inverse)
  then show ?thesis unfolding isometric_def by blast
qed

lemma equivp_isometric:
  "equivp (isometric :: 'a metric \<Rightarrow> 'a metric \<Rightarrow> bool)"
proof (rule equivpI)
  show "reflp (isometric :: 'a metric \<Rightarrow> 'a metric \<Rightarrow> bool)"
  proof (rule reflpI)
    fix X :: "'a metric"
    show "isometric X X" by (rule isometric_refl)
  qed
  show "symp (isometric :: 'a metric \<Rightarrow> 'a metric \<Rightarrow> bool)"
  proof (rule sympI)
    fix X Y :: "'a metric"
    assume "isometric X Y"
    then show "isometric Y X" by (rule isometric_sym)
  qed
  show "transp (isometric :: 'a metric \<Rightarrow> 'a metric \<Rightarrow> bool)"
  proof (rule transpI)
    fix X Y Z :: "'a metric"
    assume "isometric X Y" and "isometric Y Z"
    then show "isometric X Z" by (rule isometric_trans)
  qed
qed

subsection \<open>Arithmetic helpers\<close> (* MOVE? *)

lemma le_mult_ge_one:
  fixes x k :: real
  assumes "0 \<le> x" and "1 \<le> k"
  shows "x \<le> k * x"
proof -
  have "1 * x \<le> k * x" using assms mult_right_mono by blast
  then show ?thesis by simp
qed

lemma qi_lower_bound_iff:
  fixes K C x y :: real
  assumes "0 < K"
  shows "(1/K) * x - C \<le> y \<longleftrightarrow> x \<le> K * (y + C)"
proof -
  have "(1/K) * x = x / K" by simp
  then have "(1/K) * x - C \<le> y \<longleftrightarrow> x / K \<le> y + C" by linarith
  also have "\<dots> \<longleftrightarrow> x \<le> (y + C) * K" using pos_divide_le_eq[OF assms] by simp
  also have "\<dots> \<longleftrightarrow> x \<le> K * (y + C)" by argo
  finally show ?thesis .
qed


subsection \<open>Quasi-isometries: introduction and elimination rules\<close>

lemma quasi_isometric_embeddingI:
  assumes maps: "f ` mspace X \<subseteq> mspace Y"
      and K: "K \<ge> 1" and C: "C \<ge> 0"
      and upper: "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
                    mdist Y (f a) (f b) \<le> K * mdist X a b + C"
      and lower: "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
                    mdist X a b \<le> K * (mdist Y (f a) (f b) + C)"
  shows "quasi_isometric_embedding X Y f"
proof -
  have Kpos: "K > 0" using K by linarith
  have "\<forall>a\<in>mspace X. \<forall>b\<in>mspace X.
          mdist Y (f a) (f b) \<le> K * mdist X a b + C \<and>
          mdist Y (f a) (f b) \<ge> (1/K) * mdist X a b - C"
  proof (intro ballI conjI)
    fix a b assume a: "a \<in> mspace X" and b: "b \<in> mspace X"
    show "mdist Y (f a) (f b) \<le> K * mdist X a b + C" using upper[OF a b] .
    show "(1/K) * mdist X a b - C \<le> mdist Y (f a) (f b)"
      using lower[OF a b] qi_lower_bound_iff[OF Kpos] by blast
  qed
  then show ?thesis using maps K C 
    unfolding quasi_isometric_embedding_def by blast
qed

lemma quasi_isometric_embeddingE:
  assumes "quasi_isometric_embedding X Y f"
  obtains K C where "f ` mspace X \<subseteq> mspace Y" and "K \<ge> 1" and "C \<ge> 0"
    and "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
           mdist Y (f a) (f b) \<le> K * mdist X a b + C"
    and "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
           mdist X a b \<le> K * (mdist Y (f a) (f b) + C)"
proof -
  obtain K C where maps: "f ` mspace X \<subseteq> mspace Y" and K: "K \<ge> 1" and C: "C \<ge> 0"
    and bounds: "\<forall>a\<in>mspace X. \<forall>b\<in>mspace X.
                   mdist Y (f a) (f b) \<le> K * mdist X a b + C \<and>
                   mdist Y (f a) (f b) \<ge> (1/K) * mdist X a b - C"
    using assms unfolding quasi_isometric_embedding_def by blast
  have Kpos: "K > 0" using K by linarith
  show thesis
  proof (rule that[OF maps K C])
    show "mdist Y (f a) (f b) \<le> K * mdist X a b + C"
      if a: "a \<in> mspace X" and b: "b \<in> mspace X" for a b
      using bounds a b by blast
    show "mdist X a b \<le> K * (mdist Y (f a) (f b) + C)"
      if a: "a \<in> mspace X" and b: "b \<in> mspace X" for a b
    proof -
      have "(1/K) * mdist X a b - C \<le> mdist Y (f a) (f b)" using bounds a b by blast
      then show ?thesis using qi_lower_bound_iff[OF Kpos] by blast
    qed
  qed
qed

lemma quasi_isometryI:
  assumes "quasi_isometric_embedding X Y f" and "D \<ge> 0"
      and "\<And>y. y \<in> mspace Y \<Longrightarrow> \<exists>x\<in>mspace X. mdist Y (f x) y \<le> D"
  shows "quasi_isometry X Y f"
  using assms unfolding quasi_isometry_def by blast

lemma quasi_isometryE:
  assumes "quasi_isometry X Y f"
  obtains D where "quasi_isometric_embedding X Y f" and "D \<ge> 0"
    and "\<And>y. y \<in> mspace Y \<Longrightarrow> \<exists>x\<in>mspace X. mdist Y (f x) y \<le> D"
  using assms unfolding quasi_isometry_def by blast


subsection \<open>Quasi-isometry: reflexivity\<close>

lemma quasi_isometry_id: "quasi_isometry X X id"
proof(rule quasi_isometryI[where D = 0])
  show "quasi_isometric_embedding X X id"
  proof (rule quasi_isometric_embeddingI[where K = 1 and C = 0])
    show "id ` mspace X \<subseteq> mspace X" by simp
    show "mdist X (id a) (id b) \<le> 1 * mdist X a b + 0"
      if "a \<in> mspace X" and "b \<in> mspace X" for a b by simp
    show "mdist X a b \<le> 1 * (mdist X (id a) (id b) + 0)"
      if "a \<in> mspace X" and "b \<in> mspace X" for a b by simp
  qed simp_all
  show  "\<exists>x\<in>mspace X. mdist X (id x) y \<le> 0" if y: "y \<in> mspace X" for y
  proof -
    have "mdist X (id y) y = 0" using y by simp
    then have "mdist X (id y) y \<le> 0" by simp
    with y show ?thesis by blast
  qed
qed simp_all

lemma quasi_isometric_refl: "quasi_isometric X X"
  unfolding quasi_isometric_def using quasi_isometry_id by blast


subsection \<open>Quasi-isometry: transitivity\<close>

lemma quasi_isometric_embedding_comp:
  assumes f: "quasi_isometric_embedding X Y f"
    and g: "quasi_isometric_embedding Y Z g"
  shows "quasi_isometric_embedding X Z (g \<circ> f)"
proof -
  obtain K1 C1 where fm: "f ` mspace X \<subseteq> mspace Y" and K1: "K1 \<ge> 1" and C1: "C1 \<ge> 0"
    and fu: "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
               mdist Y (f a) (f b) \<le> K1 * mdist X a b + C1"
    and fl: "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
               mdist X a b \<le> K1 * (mdist Y (f a) (f b) + C1)"
    using quasi_isometric_embeddingE[OF f] by blast
  obtain K2 C2 where gm: "g ` mspace Y \<subseteq> mspace Z" and K2: "K2 \<ge> 1" and C2: "C2 \<ge> 0"
    and gu: "\<And>a b. a \<in> mspace Y \<Longrightarrow> b \<in> mspace Y \<Longrightarrow>
               mdist Z (g a) (g b) \<le> K2 * mdist Y a b + C2"
    and gl: "\<And>a b. a \<in> mspace Y \<Longrightarrow> b \<in> mspace Y \<Longrightarrow>
               mdist Y a b \<le> K2 * (mdist Z (g a) (g b) + C2)"
    using quasi_isometric_embeddingE[OF g] by blast
  have fx: "f x \<in> mspace Y" if x:"x \<in> mspace X" for x
    using fm x by blast

  define K where "K = K2 * K1"
  define C where "C = K2 * C1 + C2"
  have K1': "0 \<le> K1" and K2': "0 \<le> K2"
    using K1 K2 by auto

  have K1_le: "K1 \<le> K"
    unfolding K_def using le_mult_ge_one[OF K1' K2] .
  then have K: "K \<ge> 1" and K': "0 \<le> K"
    using K1 by auto
  have C1_le: "C1 \<le> K2 * C1"
    using le_mult_ge_one[OF C1 K2] .
  have C: "C \<ge> 0"
    unfolding C_def using mult_nonneg_nonneg[OF K2' C1] C2 by linarith

  show ?thesis
  proof (rule quasi_isometric_embeddingI[OF _ K C])
    show "(g \<circ> f) ` mspace X \<subseteq> mspace Z"
      using fm gm by auto
    
    show "mdist Z ((g \<circ> f) a) ((g \<circ> f) b) \<le> K * mdist X a b + C"
      if a: "a \<in> mspace X" and b: "b \<in> mspace X" for a b
    proof -
      have "mdist Z (g (f a)) (g (f b)) \<le> K2 * mdist Y (f a) (f b) + C2"
        using gu[OF fx[OF a] fx[OF b]] .
      also have "\<dots> \<le> K2 * (K1 * mdist X a b + C1) + C2"
        using mult_left_mono[OF fu[OF a b] K2'] by simp
      also have "\<dots> = K * mdist X a b + C"
        unfolding K_def C_def by argo
      finally show ?thesis by simp
    qed

    show "mdist X a b \<le> K * (mdist Z ((g \<circ> f) a) ((g \<circ> f) b) + C)"
      if a: "a \<in> mspace X" and b: "b \<in> mspace X" for a b
    proof -
      let ?dZ = "mdist Z (g (f a)) (g (f b))"
      have "mdist X a b \<le> K1 * (mdist Y (f a) (f b) + C1)"
        using fl[OF a b] .
      also have "\<dots> \<le> K1 * (K2 * (?dZ + C2) + C1)"
        using gl[OF fx[OF a] fx[OF b]] K1 by auto
      also have "\<dots> = K * (?dZ + C2) + K1 * C1" using K_def by algebra
      also have "\<dots> \<le> K * (?dZ + C2) + K * (K2 * C1)"
        using mult_mono[OF K1_le C1_le K' C1] by auto
      also have "\<dots> = K * (?dZ + C)"
        unfolding C_def by argo
      finally show ?thesis by simp
    qed
  qed
qed

lemma quasi_isometry_comp:
  assumes f: "quasi_isometry X Y f" and g: "quasi_isometry Y Z g"
  shows "quasi_isometry X Z (g \<circ> f)"
proof -
  obtain D1 where fe: "quasi_isometric_embedding X Y f" and D1: "D1 \<ge> 0"
    and fs: "\<And>y. y \<in> mspace Y \<Longrightarrow> \<exists>x\<in>mspace X. mdist Y (f x) y \<le> D1"
    using quasi_isometryE[OF f] by blast
  obtain D2 where ge: "quasi_isometric_embedding Y Z g" and D2: "D2 \<ge> 0"
    and gs: "\<And>z. z \<in> mspace Z \<Longrightarrow> \<exists>y\<in>mspace Y. mdist Z (g y) z \<le> D2"
    using quasi_isometryE[OF g] by blast
  obtain K2 C2 where gm: "g ` mspace Y \<subseteq> mspace Z" and K2: "K2 \<ge> 1" and C2: "C2 \<ge> 0"
    and gu: "\<And>a b. a \<in> mspace Y \<Longrightarrow> b \<in> mspace Y \<Longrightarrow>
               mdist Z (g a) (g b) \<le> K2 * mdist Y a b + C2"
    and "\<And>a b. a \<in> mspace Y \<Longrightarrow> b \<in> mspace Y \<Longrightarrow>
           mdist Y a b \<le> K2 * (mdist Z (g a) (g b) + C2)"
    using quasi_isometric_embeddingE[OF ge] by blast
  have fm: "f ` mspace X \<subseteq> mspace Y"
    using fe unfolding quasi_isometric_embedding_def by blast
  have K2': "0 \<le> K2"
    using K2 by linarith

  define D where "D = K2 * D1 + C2 + D2"
  have D: "D \<ge> 0"
    unfolding D_def using mult_nonneg_nonneg[OF K2' D1] C2 D2 by linarith

  have surj: "\<exists>x\<in>mspace X. mdist Z ((g \<circ> f) x) z \<le> D" if z: "z \<in> mspace Z" for z
  proof -
    obtain y where y: "y \<in> mspace Y" and yz: "mdist Z (g y) z \<le> D2"
      using gs[OF z] by blast
    obtain x where x: "x \<in> mspace X" and xy: "mdist Y (f x) y \<le> D1"
      using fs[OF y] by blast
    have fx: "f x \<in> mspace Y"
      using fm x by blast
    have gfx: "g (f x) \<in> mspace Z" and gy: "g y \<in> mspace Z"
      using gm fx y by auto
    have "mdist Z (g (f x)) z \<le> mdist Z (g (f x)) (g y) + mdist Z (g y) z"
      using mdist_triangle[OF gfx gy z] .
    also have "\<dots> \<le> (K2 * mdist Y (f x) y + C2) + D2"
      using gu[OF fx y] yz by linarith
    also have "\<dots> \<le> K2 * D1 + C2 + D2"
      using mult_left_mono[OF xy K2'] by linarith
    finally have "mdist Z ((g \<circ> f) x) z \<le> D"
      unfolding D_def by simp
    with x show ?thesis by blast
  qed

  show ?thesis
    using  quasi_isometryI[OF quasi_isometric_embedding_comp[OF fe ge] D surj] .
qed

lemma quasi_isometric_trans:
  assumes "quasi_isometric X Y" and "quasi_isometric Y Z"
  shows "quasi_isometric X Z"
proof -
  obtain f where f: "quasi_isometry X Y f"
    using assms(1) unfolding quasi_isometric_def by blast
  obtain g where g: "quasi_isometry Y Z g"
    using assms(2) unfolding quasi_isometric_def by blast
  have "quasi_isometry X Z (g \<circ> f)" using quasi_isometry_comp[OF f g] .
  then show ?thesis unfolding quasi_isometric_def by blast
qed


subsection \<open>Quasi-inverses\<close>

(* MOVE? *)
lemma mdist_quadrilateral:
  assumes a: "a \<in> mspace M" and b: "b \<in> mspace M"
    and y: "y \<in> mspace M" and y': "y' \<in> mspace M"
  shows "mdist M y y' \<le> mdist M a b + mdist M a y + mdist M b y'"
    and "mdist M a b \<le> mdist M y y' + mdist M a y + mdist M b y'"
proof -
  show "mdist M y y' \<le> mdist M a b + mdist M a y + mdist M b y'"
    using mdist_triangle[OF y a y'] mdist_triangle[OF a b y'] mdist_commute[of M y a]
    by linarith
  show "mdist M a b \<le> mdist M y y' + mdist M a y + mdist M b y'"
    using mdist_triangle[OF a y b] mdist_triangle[OF y y' b] mdist_commute[of M y' b]
    by linarith
qed

definition quasi_inverse :: "'a metric \<Rightarrow> 'b metric \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "quasi_inverse X Y f g \<longleftrightarrow> f ` mspace X \<subseteq> mspace Y \<and> g ` mspace Y \<subseteq> mspace X
                                  \<and> (\<exists>D \<ge> 0. (\<forall>x\<in>mspace X. mdist X (g (f x)) x \<le> D)
                                           \<and> (\<forall>y\<in>mspace Y. mdist Y (f (g y)) y \<le> D))"

lemma quasi_inverseI:
  assumes "f ` mspace X \<subseteq> mspace Y" and "g ` mspace Y \<subseteq> mspace X" and "D \<ge> 0"
      and "\<And>x. x \<in> mspace X \<Longrightarrow> mdist X (g (f x)) x \<le> D"
      and "\<And>y. y \<in> mspace Y \<Longrightarrow> mdist Y (f (g y)) y \<le> D"
  shows "quasi_inverse X Y f g"
  using assms unfolding quasi_inverse_def by blast

lemma quasi_inverseE:
  assumes "quasi_inverse X Y f g"
  obtains D where "f ` mspace X \<subseteq> mspace Y" and "g ` mspace Y \<subseteq> mspace X" and "D \<ge> 0"
    and "\<And>x. x \<in> mspace X \<Longrightarrow> mdist X (g (f x)) x \<le> D"
    and "\<And>y. y \<in> mspace Y \<Longrightarrow> mdist Y (f (g y)) y \<le> D"
  using assms unfolding quasi_inverse_def by blast

lemma quasi_inverse_sym:
  assumes "quasi_inverse X Y f g"
  shows "quasi_inverse Y X g f"
  using assms unfolding quasi_inverse_def by blast

lemma quasi_inverse_imp_quasi_isometry:
  assumes fe: "quasi_isometric_embedding X Y f" and fg: "quasi_inverse X Y f g"
  shows "quasi_isometry X Y f"
proof -
  obtain D where "f ` mspace X \<subseteq> mspace Y" and gm: "g ` mspace Y \<subseteq> mspace X" and D: "D \<ge> 0"
    and "\<And>x. x \<in> mspace X \<Longrightarrow> mdist X (g (f x)) x \<le> D"
    and fgy: "\<And>y. y \<in> mspace Y \<Longrightarrow> mdist Y (f (g y)) y \<le> D"
    using quasi_inverseE[OF fg] by blast
  have surj: "\<exists>x\<in>mspace X. mdist Y (f x) y \<le> D" if y: "y \<in> mspace Y" for y
  proof (rule bexI[where x = "g y"])
    show "mdist Y (f (g y)) y \<le> D" using fgy[OF y] .
    show "g y \<in> mspace X" using gm y by blast
  qed
  show ?thesis using quasi_isometryI[OF fe D surj] .
qed

lemma quasi_isometry_quasi_inverse:
  assumes f: "quasi_isometry X Y f"
  obtains g where "quasi_inverse X Y f g"
proof -
  obtain D where fe: "quasi_isometric_embedding X Y f" and D: "D \<ge> 0"
    and fs: "\<And>y. y \<in> mspace Y \<Longrightarrow> \<exists>x\<in>mspace X. mdist Y (f x) y \<le> D"
    using quasi_isometryE[OF f] by blast
  obtain K C where fm: "f ` mspace X \<subseteq> mspace Y" and K: "K \<ge> 1" and C: "C \<ge> 0"
    and fu: "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
               mdist Y (f a) (f b) \<le> K * mdist X a b + C"
    and fl: "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
               mdist X a b \<le> K * (mdist Y (f a) (f b) + C)"
    using quasi_isometric_embeddingE[OF fe] by blast
  have K0: "0 \<le> K"
    using K by linarith
  have fx: "f x \<in> mspace Y" if "x \<in> mspace X" for x
    using fm that by blast

  define g where "g = (\<lambda>y. SOME x. x \<in> mspace X \<and> mdist Y (f x) y \<le> D)"
  have gX: "g y \<in> mspace X" and fg: "mdist Y (f (g y)) y \<le> D"
    if y: "y \<in> mspace Y" for y
  proof -
    have "\<exists>x. x \<in> mspace X \<and> mdist Y (f x) y \<le> D"
      using fs[OF y] by blast
    then have "g y \<in> mspace X \<and> mdist Y (f (g y)) y \<le> D"
      unfolding g_def by (rule someI_ex)
    then show "g y \<in> mspace X" and "mdist Y (f (g y)) y \<le> D"
      by auto (* Extra step required? *)
  qed

  have gf: "mdist X (g (f x)) x \<le> K * (D + C)" if x: "x \<in> mspace X" for x
  proof -
    have y: "f x \<in> mspace Y" using fx[OF x] .
    have "mdist X (g (f x)) x \<le> K * (mdist Y (f (g (f x))) (f x) + C)"
      using fl[OF gX[OF y] x] .
    also have "\<dots> \<le> K * (D + C)" using fg[OF y] mult_left_mono[OF _ K0] by simp
    finally show ?thesis .
  qed

  have DC: "0 \<le> D + C"
    using C D by auto
  have D': "0 \<le> K * (D + C)"
    using mult_nonneg_nonneg[OF K0 DC] .(* Always seldgehammering these cases. Should I "know" these rules?  *)
  have D_le: "D \<le> K * (D + C)"
    using le_mult_ge_one[OF DC K] C by linarith
  have "quasi_inverse X Y f g"
  proof (rule quasi_inverseI[OF fm _ D'])
    show "g ` mspace Y \<subseteq> mspace X"
      using gX by blast
    show "mdist X (g (f x)) x \<le> K * (D + C)" if "x \<in> mspace X" for x
      using gf[OF that] . (* Should I be naming "that" when using OF? *) 
    show "mdist Y (f (g y)) y \<le> K * (D + C)" if "y \<in> mspace Y" for y
      using fg[OF that] D_le by linarith
  qed
  then show thesis by (rule that)
qed

lemma quasi_isometry_iff_quasi_inverse:
  assumes fe: "quasi_isometric_embedding X Y f"
  shows "quasi_isometry X Y f \<longleftrightarrow> (\<exists>g. quasi_inverse X Y f g)"
proof
  assume "quasi_isometry X Y f"
  then obtain g where "quasi_inverse X Y f g"
    by (rule quasi_isometry_quasi_inverse)
  then show "\<exists>g. quasi_inverse X Y f g" by blast
next
  assume "\<exists>g. quasi_inverse X Y f g"
  then obtain g where "quasi_inverse X Y f g" by blast
  then show "quasi_isometry X Y f"
    by (rule quasi_inverse_imp_quasi_isometry[OF fe])
qed

lemma quasi_inverse_quasi_isometric_embedding:
  assumes fe: "quasi_isometric_embedding X Y f" and fg: "quasi_inverse X Y f g"
  shows "quasi_isometric_embedding Y X g"
proof -
  obtain K C where fm: "f ` mspace X \<subseteq> mspace Y" and K: "K \<ge> 1" and C: "C \<ge> 0"
    and fu: "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
               mdist Y (f a) (f b) \<le> K * mdist X a b + C"
    and fl: "\<And>a b. a \<in> mspace X \<Longrightarrow> b \<in> mspace X \<Longrightarrow>
               mdist X a b \<le> K * (mdist Y (f a) (f b) + C)"
    using quasi_isometric_embeddingE[OF fe] by blast
  obtain D where "f ` mspace X \<subseteq> mspace Y" and gm: "g ` mspace Y \<subseteq> mspace X" and D: "D \<ge> 0"
    and "\<And>x. x \<in> mspace X \<Longrightarrow> mdist X (g (f x)) x \<le> D"
    and fgy: "\<And>y. y \<in> mspace Y \<Longrightarrow> mdist Y (f (g y)) y \<le> D"
    using quasi_inverseE[OF fg] by blast
  have K0: "0 \<le> K"
    using K by linarith
  have fx: "f x \<in> mspace Y" if "x \<in> mspace X" for x
    using fm that by blast
  have gX: "g y \<in> mspace X" if "y \<in> mspace Y" for y
    using gm that by blast

have near: "mdist Y y y' \<le> mdist Y (f (g y)) (f (g y')) + 2 * D"
    and far: "mdist Y (f (g y)) (f (g y')) \<le> mdist Y y y' + 2 * D"
    if y: "y \<in> mspace Y" and y': "y' \<in> mspace Y" for y y'
    using mdist_quadrilateral[OF fx[OF gX[OF y]] fx[OF gX[OF y']] y y'] fgy[OF y] fgy[OF y']
      apply linarith
    using mdist_quadrilateral[OF fx[OF gX[OF y]] fx[OF gX[OF y']] y y'] fgy[OF y] fgy[OF y']
      apply linarith(* Why doesn't "by linarith" work for both??? *) .

  define C' where "C' = K * (C + 2 * D)"
  have CD: "0 \<le> C + 2 * D"
    using C D by auto
  have C': "C' \<ge> 0"
    unfolding C'_def using mult_nonneg_nonneg[OF K0 CD] .
  have CD_le: "C + 2 * D \<le> C'"
    unfolding C'_def using le_mult_ge_one[OF CD K] .
  have C'_le: "C' \<le> K * C'"
    using le_mult_ge_one[OF C' K] .

  have upper: "mdist X (g y) (g y') \<le> K * mdist Y y y' + C'"
    if y: "y \<in> mspace Y" and y': "y' \<in> mspace Y" for y y'
  proof -
    have "mdist X (g y) (g y') \<le> K * (mdist Y (f (g y)) (f (g y')) + C)"
      using fl[OF gX[OF y] gX[OF y']] .
    also have "\<dots> \<le> K * (mdist Y y y' + 2 * D + C)"
      using far[OF y y'] mult_left_mono[OF _ K0] by simp
    also have "\<dots> = K * mdist Y y y' + C'"
      unfolding C'_def by argo
    finally show ?thesis .
  qed

  have lower: "mdist Y y y' \<le> K * (mdist X (g y) (g y') + C')"
    if y: "y \<in> mspace Y" and y': "y' \<in> mspace Y" for y y'
  proof -
    have "mdist Y y y' \<le> mdist Y (f (g y)) (f (g y')) + 2 * D"
      using near[OF y y'] .
    also have "\<dots> \<le> K * mdist X (g y) (g y') + (C + 2 * D)"
      using fu[OF gX[OF y] gX[OF y']] by linarith
    also have "\<dots> \<le> K * mdist X (g y) (g y') + K * C'"
      using CD_le C'_le by linarith
    also have "\<dots> = K * (mdist X (g y) (g y') + C')"
      by argo
    finally show ?thesis .
  qed

  show ?thesis
    using quasi_isometric_embeddingI[OF gm K C' upper lower] .
qed

(* Neat :) *)
lemma quasi_inverse_quasi_isometry:
  assumes fe: "quasi_isometric_embedding X Y f" and fg: "quasi_inverse X Y f g"
  shows "quasi_isometry Y X g"
  by (rule quasi_inverse_imp_quasi_isometry[OF quasi_inverse_quasi_isometric_embedding[OF fe fg]
                                               quasi_inverse_sym[OF fg]])

lemma quasi_isometry_inverse:
  assumes f: "quasi_isometry X Y f"
  obtains g where "quasi_isometry Y X g"
proof -
  obtain g where fg: "quasi_inverse X Y f g"
    using f by (rule quasi_isometry_quasi_inverse)
  have fe: "quasi_isometric_embedding X Y f"
    using f unfolding quasi_isometry_def by blast
  show thesis
    by (rule that[OF quasi_inverse_quasi_isometry[OF fe fg]])
qed

subsection \<open>Quasi-isometry: symmetry\<close>

lemma quasi_isometric_sym:
  assumes "quasi_isometric X Y"
  shows "quasi_isometric Y X"
proof -
  obtain f where "quasi_isometry X Y f"
    using assms unfolding quasi_isometric_def by blast
  then obtain g where "quasi_isometry Y X g" by (rule quasi_isometry_inverse)
  then show ?thesis unfolding quasi_isometric_def by blast
qed

subsection \<open>Quasi-isometry is an equivalence relation\<close>

lemma equivp_quasi_isometric:
  "equivp (quasi_isometric :: 'a metric \<Rightarrow> 'a metric \<Rightarrow> bool)"
proof (rule equivpI)
  show "reflp (quasi_isometric :: 'a metric \<Rightarrow> 'a metric \<Rightarrow> bool)"
  proof (rule reflpI)
    fix X :: "'a metric"
    show "quasi_isometric X X" by (rule quasi_isometric_refl)
  qed
  show "symp (quasi_isometric :: 'a metric \<Rightarrow> 'a metric \<Rightarrow> bool)"
  proof (rule sympI)
    fix X Y :: "'a metric"
    assume "quasi_isometric X Y"
    then show "quasi_isometric Y X" by (rule quasi_isometric_sym)
  qed
  show "transp (quasi_isometric :: 'a metric \<Rightarrow> 'a metric \<Rightarrow> bool)"
  proof (rule transpI)
    fix X Y Z :: "'a metric"
    assume "quasi_isometric X Y" and "quasi_isometric Y Z"
    then show "quasi_isometric X Z" by (rule quasi_isometric_trans)
  qed
qed

end
theory Milnor_Svarc
  imports Word_Metric Isometric_Actions Geodesic_Spaces
begin

(* TODO:
    1a. Reorganize files? (Move relevant lemmas to QI and WM files. Where should the orbit lemmas here go?)
    1b. Check lemma names (any idiosyncrasies making it difficult for readers). Removed unused helpers.
    1c. Fix section headers. Add introductions.
    2. Clean up proofs wherever possible (especially arithmetic arguments), maintain readability!
    3. Find out preferred try0 "by"s (I've just been choosing for the output at random.)
    4. Add comments for the reader (outline arguments).
    5. Are the definitions correct? Have I formalized "nothing"? ASK SOMEBODY!
*)

(* MOVE ALL THREE? Should I use this in Word_Metric.thy? Rewrite assumptions :( ? *)
abbreviation (in group) finite_generating_set :: "'a set \<Rightarrow> bool" where
  "finite_generating_set S \<equiv> finite S \<and> S \<subseteq> carrier G \<and> carrier G = \<langle>S\<rangle>"

abbreviation (in group) finitely_generated :: bool where
  "finitely_generated \<equiv> \<exists>S. finite_generating_set S"

abbreviation word_metric_space :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a metric"
  where "word_metric_space G S \<equiv> metric (carrier G, d\<^bsub>G,S\<^esub>)"

context isometric_action
begin

definition proper_action :: bool
  where "proper_action \<longleftrightarrow> (\<forall>x\<in>M. \<forall>c\<in>M. \<forall>r. finite {g \<in> carrier G. g \<cdot> x \<in> mcball c r})"

definition cobounded_action :: bool
  where "cobounded_action \<longleftrightarrow> (\<exists>c\<in>M. \<exists>R. (\<Union>g \<in> carrier G. \<phi> g ` mcball c R) = M)"

lemma proper_action_orbit:
  assumes proper_act: "proper_action" and x: "x \<in> M"
  shows "finite {g \<in> carrier G. d x (g \<cdot> x) \<le> r}"
proof -
  have eq: "{g \<in> carrier G. d x (g \<cdot> x) \<le> r} = {g \<in> carrier G. g \<cdot> x \<in> mcball x r}"
    using x orbit_map_in[OF x] by auto
  have "finite {g \<in> carrier G. g \<cdot> x \<in> mcball x r}"
    using proper_act x unfolding proper_action_def by blast
  then show ?thesis unfolding eq . (* Can I do this more often - unfolding for cleaner proofs? *)
qed

(* Show the other direction? *)
lemma cobounded_action_orbit:
  assumes cobd: "cobounded_action" and x: "x \<in> M"
  obtains R::real where "0 \<le> R" and "\<And>y. y \<in> M \<Longrightarrow> \<exists>g\<in>carrier G. d (g \<cdot> x) y \<le> R"
proof -
  obtain c R where c: "c \<in> M" and cover: "(\<Union>g\<in>carrier G. \<phi> g ` mcball c R) = M"
    using cobd unfolding cobounded_action_def by blast
  have cov_act: "\<exists>g\<in>carrier G. \<exists>z\<in>mcball c R. y = g \<cdot> z" if y: "y \<in> M" for y
  proof -
    have "y \<in> (\<Union>g\<in>carrier G. \<phi> g ` mcball c R)" using y cover by simp
    then show ?thesis by blast
  qed
  have R0: "0 \<le> R"
  proof -
    obtain z where "z \<in> mcball c R" using cov_act[OF c] by blast
    then have "d c z \<le> R" by simp
    with nonneg[of c z] show ?thesis by linarith
  qed

  have near: "\<exists>g\<in>carrier G. d (g \<cdot> x) y \<le> R + d c x" if y: "y \<in> M" for y
  proof -
    obtain g z where g: "g \<in> carrier G" and z: "z \<in> mcball c R" and yz: "y = g \<cdot> z"
      using cov_act[OF y] by blast
    have zM: "z \<in> M" and dcz: "d c z \<le> R" using z by auto
    have "d (g \<cdot> x) y = d x z"
      unfolding yz using act_dist[OF g x zM] .
    also have "\<dots> \<le> d x c + d c z"
      using triangle[OF x c zM] .
    also have "\<dots> \<le> R + d c x"
      using dcz commute[of x c] by linarith
    finally show ?thesis using g by blast
  qed
  have R'0: "0 \<le> R + d c x" using R0 nonneg[of c x] by linarith
  show thesis using that[OF R'0 near] .
qed

end

section \<open>Auxiliary lemmas\<close>

(* Move next to the nat variant? *)
lemma sum_list_le_const_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<And>s. s \<in> set w \<Longrightarrow> f s \<le> K"
  shows "sum_list (map f w) \<le> K * real (length w)"
  using assms
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  have fa: "f a \<le> K" using Cons.prems by simp
  have IH: "sum_list (map f w) \<le> K * real (length w)" using Cons.IH Cons.prems by simp
  have "sum_list (map f (a # w)) = f a + sum_list (map f w)" by simp
  moreover have "K * real (length (a # w)) = K + K * real (length w)" by (simp add: algebra_simps)
  (* Does algebra_simps always solve these situations? *)
  (* Check what it actually does, instead of using it as last resort. *)
  ultimately show ?case using fa IH by linarith
qed

(* nat \<Longrightarrow> element functions vs. using list? Better for indexing? *)
lemma (in group) telescoping:
  assumes "\<And>j::nat. j \<le> n \<Longrightarrow> f j \<in> carrier G"
  shows "(\<pi> (map (\<lambda>j. inv (f j) \<otimes> f (Suc j)) [0..<n])) = inv (f 0) \<otimes> f n"
  using assms
proof (induction n)
  case 0
  then have "f 0 \<in> carrier G" by simp
  then show ?case by simp
next
  case (Suc n)
  have f: "f j \<in> carrier G" if "j \<le> Suc n" for j
    using Suc.prems that by blast
  have IH: "(\<pi> (map (\<lambda>j. inv (f j) \<otimes> f (Suc j)) [0..<n])) = inv (f 0) \<otimes> f n"
    using f le_SucI Suc.IH by blast (* Better way to do this? *)
  let ?w = "map (\<lambda>j. inv (f j) \<otimes> f (Suc j)) [0..<n]"
  let ?l = "inv (f n) \<otimes> f (Suc n)"
  have c: "inv (f 0) \<in> carrier G" "f n \<in> carrier G" "inv (f n) \<in> carrier G" "f (Suc n) \<in> carrier G"
    using f by auto
  have wG: "set ?w \<subseteq> carrier G" using f by auto
  have lG: "set [?l] \<subseteq> carrier G" using c by simp
  have "(\<pi> (map (\<lambda>j. inv (f j) \<otimes> f (Suc j)) [0..<Suc n])) = \<pi> (?w @ [?l])"
    by simp
  also have "\<dots> = (\<pi> ?w) \<otimes> (\<pi> [?l])"
    using m_concat_append[OF wG lG] .
  also have "\<dots> = (inv (f 0) \<otimes> f n) \<otimes> ?l"
    using IH c by simp
  also have "\<dots> = inv (f 0) \<otimes> (f n \<otimes> ?l)"
    using m_assoc[OF c(1) c(2) m_closed[OF c(3) c(4)]] .
  also have "\<dots> = inv (f 0) \<otimes> ((f n \<otimes> inv (f n)) \<otimes> f (Suc n))"
    using m_assoc[OF c(2) c(3) c(4)] by simp
  also have "\<dots> = inv (f 0) \<otimes> f (Suc n)"
    using c by simp
  finally show ?case .
qed

(* Move to Word_Metric.thy?*)
lemma (in group) quasi_isometry_change_generators:
  assumes S: "finite_generating_set S" and T: "finite_generating_set T"
    and qi: "quasi_isometry (word_metric_space G S) Y f"
  shows "quasi_isometry (word_metric_space G T) Y f"
proof -
  have finS: "finite S" and S': "S \<subseteq> carrier G" and genS: "carrier G = \<langle>S\<rangle>"
    using S by auto
  have finT: "finite T" and T': "T \<subseteq> carrier G" and genT: "carrier G = \<langle>T\<rangle>"
    using T by auto
  obtain K where K: "K \<ge> 1"
    and bl: "\<forall>a\<in>carrier G. \<forall>b\<in>carrier G. d\<^bsub>S\<^esub> a b \<le> K * d\<^bsub>T\<^esub> a b \<and> d\<^bsub>T\<^esub> a b \<le> K * d\<^bsub>S\<^esub> a b"
    using word_metric_bilipschitz[OF finT T' genT finS S' genS] by blast
  have id_qi: "quasi_isometry (word_metric_space G T) (word_metric_space G S) id"
    using bilipschitz_id_quasi_isometry[OF word_metric_is_metric[OF T' genT]
                                               word_metric_is_metric[OF S' genS] K bl] .
  have "quasi_isometry (word_metric_space G T) Y (f \<circ> id)"
    using quasi_isometry_comp[OF id_qi qi] . (* Cleaner than using transitivity lemma? *)
  then show ?thesis unfolding comp_id . (* Too much? Just use simp? *)
qed

section \<open>Orbits and word length\<close>

context isometric_action
begin

(* Change name? *)
(* Move to isometric actions? *)
lemma orbit_dist_word:
  assumes x: "x \<in> M" and w: "set w \<subseteq> carrier G"
  shows "d x ((\<pi> w) \<cdot> x) \<le> sum_list (map (\<lambda>s. d x (s \<cdot> x)) w)"
  using w
proof (induction w)
  case Nil
  have "d x (\<one>\<^bsub>G\<^esub> \<cdot> x) = 0" using orbit_map_one[OF x] x by simp
  then show ?case by simp
next
  case (Cons s w)
  have s: "s \<in> carrier G" and wG: "set w \<subseteq> carrier G" using Cons.prems by auto
  have pwG: "(\<pi> w) \<in> carrier G" using m_concat_closed[OF wG] .
  let ?wx = "(\<pi> w) \<cdot> x"
  have wxM: "?wx \<in> M" using orbit_map_in[OF x pwG] .
  have sx: "s \<cdot> x \<in> M" using orbit_map_in[OF x s] .
  have "(\<pi> (s # w)) \<cdot> x = s \<cdot> ?wx" using orbit_map_mult[OF x s pwG] by simp
  then have "d x ((\<pi> (s # w)) \<cdot> x) = d x (s \<cdot> ?wx)" by simp
  also have "\<dots> \<le> d x (s \<cdot> x) + d (s \<cdot> x) (s \<cdot> ?wx)"
    using triangle[OF x sx orbit_map_in[OF wxM s]] .
  also have "\<dots> = d x (s \<cdot> x) + d x ?wx"
    using act_dist[OF s x wxM] by simp
  also have "\<dots> \<le> d x (s \<cdot> x) + sum_list (map (\<lambda>s. d x (s \<cdot> x)) w)"
    using Cons.IH[OF wG] by simp
  also have "\<dots> = sum_list (map (\<lambda>s. d x (s \<cdot> x)) (s # w))"
    by simp
  finally show ?case .
qed

lemma orbit_dist_le_word_length:
  assumes base: "x0 \<in> M" and S: "S \<subseteq> carrier G" and genS: "carrier G = \<langle>S\<rangle>\<^bsub>G\<^esub>" (* Why don't we "know" G?*)
    and bound: "\<And>s. s \<in> S \<Longrightarrow> d x0 (s \<cdot> x0) \<le> K"
    and g: "g \<in> carrier G"
  shows "d x0 (g \<cdot> x0) \<le> K * |g|\<^bsub>S\<^esub>"
proof -
  have letter: "d x0 (s \<cdot> x0) \<le> K" if s: "s \<in> S \<union> m_inv G ` S" for s
    using s
  proof (* Explicit way to introduce the cases? *)
    assume sS: "s \<in> S"
    show ?thesis using bound[OF sS] .
  next
    assume invS: "s \<in> m_inv G ` S"
    then obtain t where t: "t \<in> S" and st: "s = inv\<^bsub>G\<^esub> t" by blast
    have tG: "t \<in> carrier G" using t S by blast
    have "d x0 (s \<cdot> x0) = d x0 (t \<cdot> x0)"
      unfolding st using orbit_dist_inv[OF base tG, symmetric] .
    also have "\<dots> \<le> K" using bound[OF t] .
    finally show ?thesis .
  qed
  obtain w where wS: "set w \<subseteq> S \<union> m_inv G ` S" and wg: "(\<pi> w) = g" and wl: "length w = |g|\<^bsub>S\<^esub>"
    using minimal_word_eq_word_length[OF S genS g] by blast
  have wG: "set w \<subseteq> carrier G" using wS S by auto
  have "d x0 (g \<cdot> x0) = d x0 ((\<pi> w) \<cdot> x0)"
    using wg by simp
  also have "\<dots> \<le> sum_list (map (\<lambda>s. d x0 (s \<cdot> x0)) w)"
    using orbit_dist_word[OF base wG] .
  also have "\<dots> \<le> K * real (length w)"
  proof (rule sum_list_le_const_real)
    show "d x0 (s \<cdot> x0) \<le> K" if "s \<in> set w" for s
      using letter wS that by blast (* Issue using "for"? *) (* Try to recollect what I meant here. *)
  qed
  also have "\<dots> = K * |g|\<^bsub>S\<^esub>"
    using wl by simp
  finally show ?thesis .
qed

lemma orbit_map_quasi_isometric_embeddingI:
  assumes base: "x0 \<in> M" and S: "S \<subseteq> carrier G" and genS: "carrier G = \<langle>S\<rangle>\<^bsub>G\<^esub>"
    and K1: "(K::real) \<ge> 1" and C0: "(C::real) \<ge> 0"
    and upper: "\<And>g. g \<in> carrier G \<Longrightarrow> d x0 (g \<cdot> x0) \<le> K * |g|\<^bsub>S\<^esub> + C"
    and lower: "\<And>g. g \<in> carrier G \<Longrightarrow> real |g|\<^bsub>S\<^esub> \<le> K * d x0 (g \<cdot> x0) + C"
  shows "quasi_isometric_embedding (word_metric_space G S) Self (orbit_map x0)"
proof -
  let ?W = "word_metric_space G S"
  have W: "Metric_space (carrier G) (d\<^bsub>S\<^esub>)"
    using word_metric_is_metric[OF S genS] .
  have Wsp: "mspace ?W = carrier G"
    by (rule Metric_space.mspace_metric[OF W])

  have reduce:
    "inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> b \<in> carrier G"
    "mdist ?W a b = |inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> b|\<^bsub>S\<^esub>"
    "mdist Self (a \<cdot> x0) (b \<cdot> x0) = d x0 ((inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> b) \<cdot> x0)"
    if "a \<in> mspace ?W" and "b \<in> mspace ?W" for a b
  proof -
    have a: "a \<in> carrier G" and b: "b \<in> carrier G"
      using that Wsp by auto
    show "inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> b \<in> carrier G"
      using a b by simp
    show "mdist ?W a b = |inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> b|\<^bsub>S\<^esub>"
      using a b unfolding Metric_space.mdist_metric[OF W] g_word_metric_def by simp
    show "mdist Self (a \<cdot> x0) (b \<cdot> x0) = d x0 ((inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> b) \<cdot> x0)"
      using orbit_dist_reduce[OF base a b] by simp (* Confusing same notation (d vs. dist? *)
  qed

  show ?thesis
  proof (rule quasi_isometric_embeddingI[OF _ K1 C0])
    show "orbit_map x0 ` mspace ?W \<subseteq> mspace Self"
      unfolding Wsp mspace_Self by (rule orbit_map_maps[OF base])
    show "mdist Self (a \<cdot> x0) (b \<cdot> x0) \<le> K * mdist ?W a b + C"
      if "a \<in> mspace ?W" and "b \<in> mspace ?W" for a b
      unfolding reduce(2,3)[OF that] using upper[OF reduce(1)[OF that]] .
    show "mdist ?W a b \<le> K * (mdist Self (a \<cdot> x0) (b \<cdot> x0) + C)"
      if "a \<in> mspace ?W" and "b \<in> mspace ?W" for a b
    proof -
      let ?d = "d x0 ((inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> b) \<cdot> x0)"
      have "C \<le> K * C" using le_mult_ge_one[OF C0 K1] .
      then show ?thesis
        using lower[OF reduce(1)[OF that]] using distrib_left[of K ?d C]
        unfolding reduce(2,3)[OF that] by linarith (* Confusing for readers? *)
    qed
  qed
qed

(* Additional lemma required? (Non-empty M, geod+proper+cobd \<Longrightarrow> QI (word_metric_space) Self  *)
theorem milnor_svarc:
  assumes geod: "geodesic"
      and proper_act: "proper_action"
      and cobd: "cobounded_action"
      and base: "x0 \<in> M"
  shows "finitely_generated"
    and "\<And>S. finite_generating_set S \<Longrightarrow> quasi_isometry (word_metric_space G S) Self (orbit_map x0)"
proof -
  obtain R::real where R0: "0 \<le> R"
    and near: "\<And>y. y \<in> M \<Longrightarrow> \<exists>g\<in>carrier G. d (g \<cdot> x0) y \<le> R"
    using cobounded_action_orbit[OF cobd base] by blast

  define S where "S = {g \<in> carrier G. d x0 (g \<cdot> x0) \<le> 2 * R + 1}"
  have S_carrier: "S \<subseteq> carrier G" unfolding S_def by blast
  have S_fin: "finite S"
    unfolding S_def using proper_action_orbit[OF proper_act base] .

  have generates: "g \<in> \<langle>S\<rangle>\<^bsub>G\<^esub>" and lower_bound: "real |g|\<^bsub>S\<^esub> \<le> d x0 (g \<cdot> x0) + 2"
    if g: "g \<in> carrier G" for g
  proof -
    have gx0: "g \<cdot> x0 \<in> M" using orbit_map_in[OF base g] .

    obtain n p where n_pos: "0 < n" and n_le: "real n \<le> (d x0 (g \<cdot> x0) / 1) + 2"
      and p0: "p 0 = x0" and pn: "p n = g \<cdot> x0" and pM: "\<And>i. p i \<in> M"
      and p_step: "\<And>i. d (p i) (p (Suc i)) \<le> 1"
      using geodesic_chain[OF geod base gx0 zero_less_one] by blast
    have n0: "n \<noteq> 0" using n_pos by simp

    have kexists: "\<forall>i. \<exists>k. k \<in> carrier G \<and> d (k \<cdot> x0) (p i) \<le> R"
      using near[OF pM] by blast
    obtain k where k: "\<forall>i. k i \<in> carrier G \<and> d (k i \<cdot> x0) (p i) \<le> R"
      using choice[OF kexists] by blast (* try0 doesn't give anything here without explicitly using choice *)

    define h where "h = (\<lambda>i. if i = 0 then \<one>\<^bsub>G\<^esub> else if i = n then g else k i)"
    have hG: "h i \<in> carrier G" for i
      unfolding h_def using g k by simp
    have hp: "d (h i \<cdot> x0) (p i) \<le> R" for i
    proof -
      consider "i = 0" | "i \<noteq> 0" "i = n" | "i \<noteq> 0" "i \<noteq> n" by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis unfolding h_def using p0 orbit_map_one[OF base] base R0 by simp
      next
        case 2
        then show ?thesis unfolding h_def using pn gx0 R0 by simp
      next
        case 3
        then show ?thesis unfolding h_def using k by simp
      qed
    qed

    define s where "s = (\<lambda>i. inv\<^bsub>G\<^esub> (h i) \<otimes>\<^bsub>G\<^esub> h (Suc i))"
    have sS: "s i \<in> S" for i
    proof -
      have a: "h i \<cdot> x0 \<in> M" using orbit_map_in[OF base hG] .
      have b: "h (Suc i) \<cdot> x0 \<in> M" using orbit_map_in[OF base hG] .
      have "d x0 (s i \<cdot> x0) = d (h i \<cdot> x0) (h (Suc i) \<cdot> x0)"
        unfolding s_def using orbit_dist_reduce[OF base hG hG, symmetric] .
      also have "\<dots> \<le> d (h i \<cdot> x0) (p i) + d (p i) (h (Suc i) \<cdot> x0)"
        using triangle[OF a pM b] .
      also have "\<dots> \<le> d (h i \<cdot> x0) (p i) + (d (p i) (p (Suc i)) + d (p (Suc i)) (h (Suc i) \<cdot> x0))"
        using add_left_mono[OF triangle[OF pM[of i] pM[of "Suc i"] b], of "d (orbit_map x0 (h i)) (p i)"] .
      also have "\<dots> \<le> R + (1 + R)"
        using hp[of i] p_step[of i] hp[of "Suc i"] commute[of "p (Suc i)" "h (Suc i) \<cdot> x0"]
        by linarith
      finally have "d x0 (s i \<cdot> x0) \<le> 2 * R + 1" by linarith
      moreover have "s i \<in> carrier G" unfolding s_def using hG by simp
      ultimately show ?thesis unfolding S_def by simp
    qed

    define w where "w = map s [0..<n]"
    have wS: "set w \<subseteq> S \<union> m_inv G ` S"
      unfolding w_def using sS by auto
    have wg: "(\<pi> w) = g"
    proof -
      have "(\<pi> w) = inv\<^bsub>G\<^esub> (h 0) \<otimes>\<^bsub>G\<^esub> h n"
        unfolding w_def s_def using telescoping[OF hG] .
      also have "\<dots> = g"
        unfolding h_def using g n0 by simp
      finally show ?thesis .
    qed

    show "g \<in> \<langle>S\<rangle>\<^bsub>G\<^esub>"
      using word_in_span[OF wS] unfolding wg .
    have "w \<in> \<lbrakk>g\<rbrakk>\<^bsub>S\<^esub>"
      unfolding g_word_eq_class_def using wS wg by simp
    then have "|g|\<^bsub>S\<^esub> \<le> length w" by (rule word_length_less_eq)
    then have "real |g|\<^bsub>S\<^esub> \<le> real n" unfolding w_def by simp
    then show "real |g|\<^bsub>S\<^esub> \<le> d x0 (g \<cdot> x0) + 2" using n_le by linarith
  qed

  have genS: "carrier G = \<langle>S\<rangle>\<^bsub>G\<^esub>"
  proof
    show "carrier G \<subseteq> \<langle>S\<rangle>\<^bsub>G\<^esub>" using generates by blast
    show "\<langle>S\<rangle>\<^bsub>G\<^esub> \<subseteq> carrier G" using gen_span_closed[OF S_carrier] .
  qed
  have fgs: "finite_generating_set S"
    using S_fin S_carrier genS by blast

  have upper_bound: "d x0 (g \<cdot> x0) \<le> (2 * R + 1) * |g|\<^bsub>S\<^esub>" if g: "g \<in> carrier G" for g
    using orbit_dist_le_word_length[OF base S_carrier genS _  g, of "2 * R + 1"] unfolding S_def
    by simp

  let ?K = "2 * R + 1"
  have K1: "?K \<ge> 1" using R0 by linarith
  let ?C = "real 2"
  have C0: "?C \<ge> 0" by linarith
  have emb: "quasi_isometric_embedding (word_metric_space G S) Self (orbit_map x0)"
  proof(rule orbit_map_quasi_isometric_embeddingI[OF base S_carrier genS K1 C0])
    show "d x0 (g \<cdot> x0) \<le> ?K * |g|\<^bsub>S\<^esub> + ?C" if g: "g \<in> carrier G" for g
      using upper_bound[OF g] C0 by linarith
    show "real |g|\<^bsub>S\<^esub> \<le> ?K * d x0 (g \<cdot> x0) + ?C" if g: "g \<in> carrier G" for g
      using lower_bound[OF g] le_mult_ge_one[OF nonneg[of x0 "g \<cdot> x0"] K1] by linarith
  qed

  have Wsp: "mspace (word_metric_space G S) = carrier G"
    using Metric_space.mspace_metric[OF word_metric_is_metric[OF S_carrier genS]] .
  have dense: "\<exists>a\<in>mspace (word_metric_space G S). mdist Self (a \<cdot> x0) y \<le> R"
    if y: "y \<in> mspace Self" for y
  proof -
    have "y \<in> M" using y by simp
    then obtain a where a: "a \<in> carrier G" and ay: "d (a \<cdot> x0) y \<le> R"
      using near by blast
    show ?thesis using a ay Wsp by auto
  qed
  have qi: "quasi_isometry (word_metric_space G S) Self (orbit_map x0)"
    using quasi_isometryI[OF emb R0 dense] .

  show "finitely_generated" using fgs by blast
  show "quasi_isometry (word_metric_space G T) Self (orbit_map x0)"
    if T: "finite_generating_set T" for T
    using quasi_isometry_change_generators[OF fgs T qi] .
qed

end

end

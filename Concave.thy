theory Concave
imports Complex_Main
begin

lemma linorder_wlog':
  fixes   x :: "'a :: linorder"
  assumes "\<And>x y. x < y \<Longrightarrow> P x y"
  assumes "\<And>x. P x x"
  assumes "\<And>x y. P x y \<Longrightarrow> P y x"
  shows   "P x y"
  by (cases x y rule: linorder_cases) (auto intro: assms)

lemma 
  "(x::real) > 0 \<Longrightarrow> y > 0 \<Longrightarrow> log 2 x + log 2 y + 2 \<le> 2 * log 2 (x + y)"
proof (induction rule: linorder_wlog'[of _ x y])
  fix x y :: real
  assume xy: "x > 0" "y > 0" "x < y"
  from xy have "\<exists>\<xi>. \<xi> > x \<and> \<xi> < x + y \<and> log 2 (x + y) - log 2 x = ((x + y) - x) * (1 / (ln 2 * \<xi>))"
    by (intro MVT2) (auto intro: derivative_eq_intros)
  then obtain \<xi> where \<xi>: "\<xi> > x" "\<xi> < x + y" "log 2 (x + y) = log 2 x + y / ln 2 / \<xi>" by auto
  from xy 
    have "\<exists>\<eta>. \<eta> > y \<and> \<eta> < x + y \<and> log 2 (x + y) - log 2 y = ((x + y) - y) * (1 / (ln 2 * \<eta>))"
    by (intro MVT2) (auto intro: derivative_eq_intros)
  then obtain \<eta> where \<eta>: "\<eta> > y" "\<eta> < x + y" "log 2 (x + y) = log 2 y + x / ln 2 / \<eta>" by auto
  
  have "log 2 (x + y) + log 2 (x + y) = log 2 x + log 2 y + x / ln 2 / \<eta> + y / ln 2 / \<xi>"
    by (subst \<xi>(3), subst \<eta>(3)) simp

  
  note \<xi>(3)
  also have 
qed (auto simp: algebra_simps log_mult)
find_theorems "log _ (_ * _)"

lemma connected_contains_Icc:
  assumes "connected (A :: ('a :: {linorder_topology}) set)" "a \<in> A" "b \<in> A"
  shows   "{a..b} \<subseteq> A"
proof
  fix x assume "x \<in> {a..b}"
  hence "x = a \<or> x = b \<or> x \<in> {a<..<b}" by auto
  thus "x \<in> A" using assms connected_contains_Ioo[of A a b] by auto
qed


definition concave_on :: "(_ :: {ordered_ring, comm_monoid_mult}) set \<Rightarrow> _" where
  "concave_on A f = (\<forall>t\<in>{0..1}. \<forall>x\<in>A. \<forall>y\<in>A. f ((1 - t) * x + t * y) \<ge> (1 - t) * f x + t * f y)"

lemma concave_onI [intro?]:
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
             f ((1 - t) * x + t * y) \<ge> (1 - t) * f x + t * f y"
  shows   "concave_on A f"
  unfolding concave_on_def
proof clarify
  case (goal1 t x y)
  with assms show ?case by (cases "t = 0 \<or> t = 1") auto
qed

lemma concave_on_linorderI [intro?]:
  fixes A :: "('a::{linordered_ring,comm_monoid_mult}) set"
  assumes "\<And>t x y. t > 0 \<Longrightarrow> t < 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x < y \<Longrightarrow>
             f ((1 - t) * x + t * y) \<ge> (1 - t) * f x + t * f y"
  shows   "concave_on A f"
proof
  case (goal1 t x y)
  with goal1 assms[of t x y] assms[of "1 - t" y x]
    show ?case by (cases x y rule: linorder_cases) (auto simp: algebra_simps)
qed

lemma concave_onD:
  assumes "concave_on A f"
  shows   "\<And>t x y. t \<ge> 0 \<Longrightarrow> t \<le> 1 \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
             f ((1 - t) * x + t * y) \<ge> (1 - t) * f x + t * f y"
  using assms unfolding concave_on_def by auto

lemma concave_on_realI:
  assumes "connected A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> (f has_real_derivative f' x) (at x)"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f' x \<ge> f' y"
  shows   "concave_on A f"
proof (rule concave_on_linorderI)
  fix t x y :: real
  assume t: "t > 0" "t < 1" and xy: "x \<in> A" "y \<in> A" "x < y"
  def z \<equiv> "(1 - t) * x + t * y"
  with `connected A` and xy have ivl: "{x..y} \<subseteq> A" using connected_contains_Icc by blast
  
  from xy t have xz: "z > x" by (simp add: z_def algebra_simps)
  have "y - z = (1 - t) * (y - x)" by (simp add: z_def algebra_simps)
  also from xy t have "... > 0" by (intro mult_pos_pos) simp_all
  finally have yz: "z < y" by simp
    
  from assms xz yz ivl t have "\<exists>\<xi>. \<xi> > x \<and> \<xi> < z \<and> f z - f x = (z - x) * f' \<xi>"
    by (intro MVT2) (auto intro!: assms(2))
  then obtain \<xi> where \<xi>: "\<xi> > x" "\<xi> < z" "f' \<xi> = (f z - f x) / (z - x)" by auto
  from assms xz yz ivl t have "\<exists>\<eta>. \<eta> > z \<and> \<eta> < y \<and> f y - f z = (y - z) * f' \<eta>"
    by (intro MVT2) (auto intro!: assms(2))
  then obtain \<eta> where \<eta>: "\<eta> > z" "\<eta> < y" "f' \<eta> = (f y - f z) / (y - z)" by auto
  
  from \<eta>(3) have "(f y - f z) / (y - z) = f' \<eta>" ..
  also from \<xi> \<eta> ivl have "\<xi> \<in> A" "\<eta> \<in> A" by auto
  with \<xi> \<eta> have "f' \<eta> \<le> f' \<xi>" by (intro assms(3)) auto
  also from \<xi>(3) have "f' \<xi> = (f z - f x) / (z - x)" .
  finally have "(f y - f z) * (z - x) \<le> (f z - f x) * (y - z)"
    using xz yz by (simp add: field_simps)
  also have "z - x = t * (y - x)" by (simp add: z_def algebra_simps)
  also have "y - z = (1 - t) * (y - x)" by (simp add: z_def algebra_simps)
  finally have "(f y - f z) * t \<le> (f z - f x) * (1 - t)" using xy by simp
  thus "(1 - t) * f x + t * f y \<le> f ((1 - t) * x + t * y)"
    by (simp add: z_def algebra_simps)
qed
  
lemma concave_ln: "concave_on {0<..} (ln :: real \<Rightarrow> real)"
  by (rule concave_on_realI) (auto intro: derivative_intros simp: field_simps)

lemma concave_log: "b > 1 \<Longrightarrow> concave_on {0<..} (log b :: real \<Rightarrow> real)"
  by (intro concave_on_realI) (auto intro: derivative_intros simp: field_simps)

lemma 
  "(x::real) > 0 \<Longrightarrow> y > 0 \<Longrightarrow> log 2 x + log 2 y + 2 \<le> 2 * log 2 (x + y)"
  using concave_onD[OF concave_log, of 2 "1/2" x y] by (simp add: field_simps log_divide)

end
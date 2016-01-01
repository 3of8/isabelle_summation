theory Liminf_Limsup_Lemma_Bucket
imports
  Main
  "~~/src/HOL/Library/Extended_Real" 
  "~~/src/HOL/Library/Liminf_Limsup"
  Extended_Real_Lemma_Bucket
begin

lemma ge_Limsup_iff:
  fixes X :: "_ \<Rightarrow> _ :: complete_linorder"
  shows "C \<ge> Limsup F X \<longleftrightarrow> (\<forall>y>C. eventually (\<lambda>x. y > X x) F)"
proof -
  { fix y P assume "eventually P F" "y > SUPREMUM (Collect P) X"
    then have "eventually (\<lambda>x. y > X x) F"
      by (auto elim!: eventually_mono dest: SUP_lessD) }
  moreover
  { fix y P assume "y > C" and y: "\<forall>y>C. eventually (\<lambda>x. y > X x) F"
    have "\<exists>P. eventually P F \<and> y > SUPREMUM (Collect P) X"
    proof (cases "\<exists>z. C < z \<and> z < y")
      case True
      then obtain z where z: "C < z \<and> z < y" ..
      moreover from z have "z \<ge> SUPREMUM {x. z > X x} X"
        by (auto intro!: SUP_least)
      ultimately show ?thesis
        using y by (intro exI[of _ "\<lambda>x. z > X x"]) auto
    next
      case False
      then have "C \<ge> SUPREMUM {x. y > X x} X"
        by (intro SUP_least) (auto simp: not_less)
      with \<open>y > C\<close> show ?thesis
        using y by (intro exI[of _ "\<lambda>x. y > X x"]) auto
    qed }
  ultimately show ?thesis
    unfolding Limsup_def INF_le_iff by auto
qed

lemma Limsup_ereal_mult_right: 
  assumes "F \<noteq> bot" "(c::real) \<ge> 0"
  shows   "Limsup F (\<lambda>n. f n * ereal c) = Limsup F f * ereal c"
proof (cases "c = 0")
  assume "c \<noteq> 0"
  with assms have c: "c > 0" by simp
  show ?thesis
  proof (rule Limsup_eqI)
    fix P assume P: "eventually P F"
    hence "eventually (\<lambda>n. f n \<le> (SUP x:Collect P. f x)) F"
      by (rule eventually_mono) (auto intro: SUP_upper)
    with assms and P show " Limsup F f * ereal c \<le> (SUP n:Collect P. f n * ereal c)"
      by (subst Sup_ereal_mult_right'[symmetric])
         (auto dest: eventually_happens' intro!: ereal_mult_right_mono Limsup_bounded SUP_upper)
  next
    fix C assume C: "\<And>P. eventually P F \<Longrightarrow> C \<le> (SUP n:Collect P. f n * ereal c)"
    {
      fix P assume P: "eventually P F"
      note C[OF P]
      also from P assms have "(SUP n:Collect P. f n * ereal c) = SUPREMUM (Collect P) f * ereal c"
        by (subst Sup_ereal_mult_right'[symmetric])
           (auto dest: eventually_happens' intro!: ereal_mult_right_mono Limsup_bounded SUP_upper)
      finally have "C / ereal c \<le> SUPREMUM (Collect P) f" using c
        by (subst ereal_divide_le_pos) (simp_all add: mult.commute)
    }
    hence "C / ereal c \<le> (INF P:{P. eventually P F}. SUPREMUM (Collect P) f)"
      by (intro INF_greatest) simp
    with c show "C \<le> Limsup F f * ereal c" 
      unfolding Limsup_def by (simp add: ereal_divide_le_pos mult.commute)
  qed
qed (simp add: assms Limsup_const zero_ereal_def[symmetric])


lemma Inf_ereal_mult_right':
  assumes nonempty: "Y \<noteq> {}"
  and x: "x \<ge> 0"
  shows "(INF i:Y. f i) * ereal x = (INF i:Y. f i * ereal x)" (is "?lhs = ?rhs")
proof(cases "x = 0")
  case True thus ?thesis by(auto simp add: nonempty zero_ereal_def[symmetric])
next
  case False
  show ?thesis
  proof(rule antisym)
    show "?rhs \<ge> ?lhs"
      by(rule INF_greatest) (simp add: ereal_mult_right_mono INF_lower x)
  next
    have "?rhs = ?rhs / ereal x * ereal x" using False
      by (simp only: ereal_times_divide_eq_left ereal_times_divide_eq[symmetric] ereal_divide) 
         (simp add: one_ereal_def[symmetric])
    also have "?rhs / ereal x \<le> (INF i:Y. f i)"
    proof(rule INF_greatest)
      fix i
      assume "i \<in> Y"
      have "f i = f i * (ereal x / ereal x)" using False by simp
      also have "\<dots> = f i * x / x" by(simp only: ereal_times_divide_eq)
      also from \<open>i \<in> Y\<close> have "f i * x \<ge> ?rhs" by (rule INF_lower)
      hence "f i * x / x \<ge> ?rhs / x" using x False by simp
      finally show "f i \<ge> ?rhs / x" .
    qed
    hence "?rhs / ereal x * ereal x \<le> (INF i:Y. f i) * ereal x" using x
      by (intro ereal_mult_right_mono) simp_all
    finally show "?lhs \<ge> ?rhs" .
  qed
qed


lemma Liminf_ereal_mult_right: 
  assumes "F \<noteq> bot" "(c::real) \<ge> 0"
  shows   "Liminf F (\<lambda>n. f n * ereal c) = Liminf F f * ereal c"
proof (cases "c = 0")
  assume "c \<noteq> 0"
  with assms have c: "c > 0" by simp
  show ?thesis
  proof (rule Liminf_eqI)
    fix P assume P: "eventually P F"
    hence "eventually (\<lambda>n. f n \<ge> (INF x:Collect P. f x)) F"
      by (rule eventually_mono) (auto intro: INF_lower)
    with assms and P show " Liminf F f * ereal c \<ge> (INF n:Collect P. f n * ereal c)"
      by (subst Inf_ereal_mult_right'[symmetric])
         (auto dest: eventually_happens' intro!: ereal_mult_right_mono Liminf_bounded INF_lower)
  next
    fix C assume C: "\<And>P. eventually P F \<Longrightarrow> C \<ge> (INF n:Collect P. f n * ereal c)"
    {
      fix P assume P: "eventually P F"
      note C[OF P]
      also from P assms have "(INF n:Collect P. f n * ereal c) = INFIMUM (Collect P) f * ereal c"
        by (subst Inf_ereal_mult_right'[symmetric])
           (auto dest: eventually_happens' intro!: ereal_mult_right_mono Limsup_bounded SUP_upper)
      finally have "C / ereal c \<ge> INFIMUM (Collect P) f" using c
        by (subst ereal_le_divide_pos) (simp_all add: mult.commute)
    }
    hence "C / ereal c \<ge> (SUP P:{P. eventually P F}. INFIMUM (Collect P) f)"
      by (intro SUP_least) simp
    with c show "C \<ge> Liminf F f * ereal c" 
      unfolding Liminf_def by (simp add: ereal_le_divide_pos mult.commute)
  qed
qed (simp add: assms Liminf_const zero_ereal_def[symmetric])

lemma Limsup_ereal_mult_left: 
  assumes "F \<noteq> bot" "(c::real) \<ge> 0"
  shows   "Limsup F (\<lambda>n. ereal c * f n) = ereal c * Limsup F f"
  using Limsup_ereal_mult_right[OF assms] by (subst (1 2) mult.commute)

lemma limsup_ereal_mult_right: 
  "(c::real) \<ge> 0 \<Longrightarrow> limsup (\<lambda>n. f n * ereal c) = limsup f * ereal c"
  by (rule Limsup_ereal_mult_right) simp_all

lemma limsup_ereal_mult_left: 
  "(c::real) \<ge> 0 \<Longrightarrow> limsup (\<lambda>n. ereal c * f n) = ereal c * limsup f"
  by (subst (1 2) mult.commute, rule limsup_ereal_mult_right) simp_all

lemma Limsup_compose_continuous_antimono:
  fixes f :: "'a::{complete_linorder, linorder_topology} \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  assumes c: "continuous_on UNIV f" and am: "antimono f" and F: "F \<noteq> bot"
  shows "Limsup F (\<lambda>n. f (g n)) = f (Liminf F g)"
proof -
  { fix P assume "eventually P F"
    have "\<exists>x. P x"
    proof (rule ccontr)
      assume "\<not> (\<exists>x. P x)" then have "P = (\<lambda>x. False)"
        by auto
      with \<open>eventually P F\<close> F show False
        by auto
    qed }
  note * = this

  have "f (Liminf F g) = (INF P : {P. eventually P F}. f (Inf (g ` Collect P)))"
    unfolding Liminf_def SUP_def
    by (subst continuous_at_Sup_antimono[OF am continuous_on_imp_continuous_within[OF c]])
       (auto intro: eventually_True)
  also have "\<dots> = (INF P : {P. eventually P F}. SUPREMUM (g ` Collect P) f)"
    by (intro INF_cong refl continuous_at_Inf_antimono[OF am continuous_on_imp_continuous_within[OF c]])
       (auto dest!: eventually_happens simp: F)
  finally show ?thesis
    by (auto simp: Limsup_def)
qed

lemma Liminf_compose_continuous_mono:
  fixes f :: "'a::{complete_linorder, linorder_topology} \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  assumes c: "continuous_on UNIV f" and am: "mono f" and F: "F \<noteq> bot"
  shows "Liminf F (\<lambda>n. f (g n)) = f (Liminf F g)"
proof -
  { fix P assume "eventually P F"
    have "\<exists>x. P x"
    proof (rule ccontr)
      assume "\<not> (\<exists>x. P x)" then have "P = (\<lambda>x. False)"
        by auto
      with \<open>eventually P F\<close> F show False
        by auto
    qed }
  note * = this

  have "f (Liminf F g) = (SUP P : {P. eventually P F}. f (Inf (g ` Collect P)))"
    unfolding Liminf_def SUP_def
    by (subst continuous_at_Sup_mono[OF am continuous_on_imp_continuous_within[OF c]])
       (auto intro: eventually_True)
  also have "\<dots> = (SUP P : {P. eventually P F}. INFIMUM (g ` Collect P) f)"
    by (intro SUP_cong refl continuous_at_Inf_mono[OF am continuous_on_imp_continuous_within[OF c]])
       (auto dest!: eventually_happens simp: F)
  finally show ?thesis by (auto simp: Liminf_def)
qed

lemma Limsup_compose_continuous_mono:
  fixes f :: "'a::{complete_linorder, linorder_topology} \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  assumes c: "continuous_on UNIV f" and am: "mono f" and F: "F \<noteq> bot"
  shows "Limsup F (\<lambda>n. f (g n)) = f (Limsup F g)"
proof -
  { fix P assume "eventually P F"
    have "\<exists>x. P x"
    proof (rule ccontr)
      assume "\<not> (\<exists>x. P x)" then have "P = (\<lambda>x. False)"
        by auto
      with \<open>eventually P F\<close> F show False
        by auto
    qed }
  note * = this

  have "f (Limsup F g) = (INF P : {P. eventually P F}. f (Sup (g ` Collect P)))"
    unfolding Limsup_def INF_def
    by (subst continuous_at_Inf_mono[OF am continuous_on_imp_continuous_within[OF c]])
       (auto intro: eventually_True)
  also have "\<dots> = (INF P : {P. eventually P F}. SUPREMUM (g ` Collect P) f)"
    by (intro INF_cong refl continuous_at_Sup_mono[OF am continuous_on_imp_continuous_within[OF c]])
       (auto dest!: eventually_happens simp: F)
  finally show ?thesis by (auto simp: Limsup_def)
qed

lemma Limsup_add_ereal_right: 
  "F \<noteq> bot \<Longrightarrow> abs c \<noteq> \<infinity> \<Longrightarrow> Limsup F (\<lambda>n. g n + (c :: ereal)) = Limsup F g + c"
  by (rule Limsup_compose_continuous_mono) (auto simp: mono_def ereal_add_mono continuous_on_def)

lemma Limsup_add_ereal_left: 
  "F \<noteq> bot \<Longrightarrow> abs c \<noteq> \<infinity> \<Longrightarrow> Limsup F (\<lambda>n. (c :: ereal) + g n) = c + Limsup F g"
  by (subst (1 2) add.commute) (rule Limsup_add_ereal_right)

lemma Liminf_add_ereal_right: 
  "F \<noteq> bot \<Longrightarrow> abs c \<noteq> \<infinity> \<Longrightarrow> Liminf F (\<lambda>n. g n + (c :: ereal)) = Liminf F g + c"
  by (rule Liminf_compose_continuous_mono) (auto simp: mono_def ereal_add_mono continuous_on_def)

lemma Liminf_add_ereal_left: 
  "F \<noteq> bot \<Longrightarrow> abs c \<noteq> \<infinity> \<Longrightarrow> Liminf F (\<lambda>n. (c :: ereal) + g n) = c + Liminf F g"
  by (subst (1 2) add.commute) (rule Liminf_add_ereal_right)


lemma 
  assumes "F \<noteq> bot"
  assumes nonneg: "eventually (\<lambda>x. f x \<ge> (0::ereal)) F"
  shows   Liminf_inverse_ereal: "Liminf F (\<lambda>x. inverse (f x)) = inverse (Limsup F f)"
  and     Limsup_inverse_ereal: "Limsup F (\<lambda>x. inverse (f x)) = inverse (Liminf F f)"
proof -
  def inv \<equiv> "\<lambda>x. if x \<le> 0 then \<infinity> else inverse x :: ereal"
  have "continuous_on ({..0} \<union> {0..}) inv" unfolding inv_def
    by (intro continuous_on_If) (auto intro!: continuous_intros)
  also have "{..0} \<union> {0..} = (UNIV :: ereal set)" by auto
  finally have cont: "continuous_on UNIV inv" .
  have antimono: "antimono inv" unfolding inv_def antimono_def
    by (auto intro!: ereal_inverse_antimono)
  
  have "Liminf F (\<lambda>x. inverse (f x)) = Liminf F (\<lambda>x. inv (f x))" using nonneg
    by (auto intro!: Liminf_eq elim!: eventually_mono simp: inv_def)
  also have "... = inv (Limsup F f)"
    by (simp add: assms(1) Liminf_compose_continuous_antimono[OF cont antimono])
  also from assms have "Limsup F f \<ge> 0" by (intro le_Limsup) simp_all
  hence "inv (Limsup F f) = inverse (Limsup F f)" by (simp add: inv_def)
  finally show "Liminf F (\<lambda>x. inverse (f x)) = inverse (Limsup F f)" .

  have "Limsup F (\<lambda>x. inverse (f x)) = Limsup F (\<lambda>x. inv (f x))" using nonneg
    by (auto intro!: Limsup_eq elim!: eventually_mono simp: inv_def)
  also have "... = inv (Liminf F f)"
    by (simp add: assms(1) Limsup_compose_continuous_antimono[OF cont antimono])
  also from assms have "Liminf F f \<ge> 0" by (intro Liminf_bounded) simp_all
  hence "inv (Liminf F f) = inverse (Liminf F f)" by (simp add: inv_def)
  finally show "Limsup F (\<lambda>x. inverse (f x)) = inverse (Liminf F f)" .
qed

lemma less_LiminfD:
  "y < Liminf F (f :: _ \<Rightarrow> 'a :: complete_linorder) \<Longrightarrow> eventually (\<lambda>x. f x > y) F"
  using le_Liminf_iff[of "Liminf F f" F f] by simp

lemma gt_LimsupD:
  "y > Limsup F (f :: _ \<Rightarrow> 'a :: complete_linorder) \<Longrightarrow> eventually (\<lambda>x. f x < y) F"
  using ge_Limsup_iff[of F f "Limsup F f"] by simp

end
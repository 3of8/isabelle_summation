theory Extended_Real_Lemma_Bucket
imports Complex_Main "~~/src/HOL/Library/Extended_Real" "~~/src/HOL/Multivariate_Analysis/Extended_Real_Limits"
begin

lemma ereal_inverse_real: "\<bar>z\<bar> \<noteq> \<infinity> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> ereal (inverse (real_of_ereal z)) = inverse z"
  by (cases z) simp_all

lemma ereal_inverse_mult:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> inverse (a * (b::ereal)) = inverse a * inverse b"
  by (cases a; cases b) auto
  
lemma tendsto_PInfty': "(f ---> \<infinity>) F = (\<forall>r>c. eventually (\<lambda>x. ereal r < f x) F)"
proof (subst tendsto_PInfty, intro iffI allI impI)
  assume A: "\<forall>r>c. eventually (\<lambda>x. ereal r < f x) F"
  fix r :: real
  from A have A: "eventually (\<lambda>x. ereal r < f x) F" if "r > c" for r using that by blast
  show "eventually (\<lambda>x. ereal r < f x) F"
  proof (cases "r > c")
    case False
    hence B: "ereal r \<le> ereal (c + 1)" by simp
    have "c < c + 1" by simp
    from A[OF this] show "eventually (\<lambda>x. ereal r < f x) F"
      by eventually_elim (rule le_less_trans[OF B])
  qed (simp add: A)
qed simp

lemma tendsto_zero_erealI:
  assumes "\<And>e. e > 0 \<Longrightarrow> eventually (\<lambda>x. \<bar>f x\<bar> < ereal e) F"
  shows   "(f ---> 0) F"
proof (subst filterlim_cong[OF refl refl])
  from assms[OF zero_less_one] show "eventually (\<lambda>x. f x = ereal (real_of_ereal (f x))) F"
    by eventually_elim (auto simp: ereal_real)
  hence "eventually (\<lambda>x. abs (real_of_ereal (f x)) < e) F" if "e > 0" for e using assms[OF that]
    by eventually_elim (simp add: real_less_ereal_iff that)
  hence "((\<lambda>x. real_of_ereal (f x)) ---> 0) F" unfolding tendsto_iff 
    by (auto simp: tendsto_iff dist_real_def)
  thus "((\<lambda>x. ereal (real_of_ereal (f x))) ---> 0) F" by (simp add: zero_ereal_def)
qed

lemma tendsto_inverse_ereal:
  assumes lim:     "(f ---> (c :: ereal)) F"
  assumes nonneg:  "eventually (\<lambda>x. f x \<ge> 0) F"
  shows   "((\<lambda>x. inverse (f x)) ---> inverse c) F"
proof (cases "F = bot")
  assume F: "F \<noteq> bot"
  from F assms have c: "c \<ge> 0" by (rule tendsto_le_const)
  then consider "c = 0" | "c = \<infinity>" | c' where "c = ereal c'" "c' > 0"
    by (cases c) (auto simp: le_less)
  thus ?thesis
  proof cases
    fix c' assume c': "c = ereal c'" "c' > 0"
    with c' have f: "eventually (\<lambda>x. f x > 0) F" "eventually (\<lambda>x. f x < \<infinity>) F"
      by (intro order_tendstoD[OF lim]; simp)+
    hence "((ereal \<circ> (real_of_ereal \<circ> f)) ---> c) F"
      by (intro Lim_transform_eventually[OF _ lim], eventually_elim) (simp add: ereal_real)
    hence "((\<lambda>x. real_of_ereal (f x)) ---> c') F" by (simp add: c' o_def)
    with c' have "((inverse \<circ> real_of_ereal \<circ> f) ---> inverse c') F" unfolding o_def
      by (intro tendsto_inverse) simp_all
    with c' have "((ereal \<circ> inverse \<circ> real_of_ereal \<circ> f) ---> inverse c) F"
      by (simp add: o_def)
    moreover from f have "eventually (\<lambda>x. (ereal \<circ> inverse \<circ> real_of_ereal \<circ> f) x = inverse (f x)) F"
      by eventually_elim (simp add: ereal_inverse_real)
      
    ultimately show "((\<lambda>x. inverse (f x)) ---> inverse c) F"
      by (rule Lim_transform_eventually[rotated])
  next
    assume "c = 0"
    hence "c < \<infinity>" and c: "c = ereal 0" by simp_all
    note f = order_tendstoD(2)[OF lim this(1)]
    from lim c have lim': "((\<lambda>x. real_of_ereal (f x)) ---> 0) F" 
      using lim_real_of_ereal[of f 0 F] by simp
    have "eventually (\<lambda>x. ereal r < inverse (f x)) F" if "r > 0" for r
    proof -
      from that have "inverse r > 0" by simp
      from nonneg f order_tendstoD(2)[OF lim' this] show ?thesis
      proof eventually_elim
        fix x assume "f x \<ge> 0" "f x < \<infinity>" "real_of_ereal (f x) < inverse r"
        with that show "inverse (f x) > ereal r" by (cases "f x") (simp_all add: field_simps)
      qed
    qed
    thus ?thesis by (simp add: c tendsto_PInfty'[of _ _ 0])
  next
    assume c: "c = \<infinity>"
    hence f: "eventually (\<lambda>x. f x > 0) F" by (intro order_tendstoD[OF lim]) simp_all
    {
      fix r :: real assume r: "r > 0"
      from tendsto_PInfty lim have "eventually (\<lambda>x. f x > ereal (inverse r)) F"
        by (simp add: tendsto_PInfty c)
      with f have "eventually (\<lambda>x. abs (inverse (f x)) < ereal r) F"
      proof eventually_elim
        fix x assume "f x > 0" "ereal (inverse r) < f x"
        with r show "abs (inverse (f x)) < ereal r" by (cases "f x") (simp_all add: field_simps)
      qed
    }
    with c show "((\<lambda>x. inverse (f x)) ---> inverse c) F" by (force intro: tendsto_zero_erealI)
  qed
qed simp

lemma continuous_inverse_ereal_nonneg [continuous_intros]: "continuous_on ({0..} :: ereal set) inverse"
unfolding continuous_on_def
proof clarify
  fix x :: ereal assume "x \<ge> 0"
  thus "(inverse ---> inverse x) (at x within {0..})"
    by (intro tendsto_inverse_ereal) (auto simp: eventually_at_topological)
qed

lemma continuous_uminus_ereal [continuous_intros]: "continuous_on (A :: ereal set) uminus"
  unfolding continuous_on_def
  by (intro ballI tendsto_uminus_ereal[of "\<lambda>x. x::ereal"]) simp

lemma ereal_uminus_atMost [simp]: "uminus ` {..(a::ereal)} = {-a..}"
proof (intro equalityI subsetI)
  fix x :: ereal assume "x \<in> {-a..}"
  hence "-(-x) \<in> uminus ` {..a}" by (intro imageI) (simp add: ereal_uminus_le_reorder)
  thus "x \<in> uminus ` {..a}" by simp
qed auto
  
lemma continuous_inverse_ereal_nonpos: "continuous_on ({..<0} :: ereal set) inverse"
proof (subst continuous_on_cong[OF refl]) 
  have "continuous_on {(0::ereal)<..} inverse"
    by (rule continuous_on_subset[OF continuous_inverse_ereal_nonneg]) auto
  thus "continuous_on {..<(0::ereal)} (uminus \<circ> inverse \<circ> uminus)"
    by (intro continuous_intros) simp_all
qed simp

end
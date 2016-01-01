theory Ln_Arctan_Series
imports Complex_Main Summation "~~/src/HOL/Multivariate_Analysis/Complex_Transcendental"
begin

lemma Ln_series:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "(\<lambda>n. (-1)^Suc n / of_nat n * z^n) sums ln (1 + z)" (is "(\<lambda>n. ?f n * z^n) sums _")
proof -
  let ?F = "\<lambda>z. \<Sum>n. ?f n * z^n" and ?F' = "\<lambda>z. \<Sum>n. diffs ?f n * z^n"
  have r: "conv_radius ?f = 1"
    by (intro conv_radius_ratio_limit_nonzero[of _ 1])
       (simp_all add: norm_divide LIMSEQ_Suc_n_over_n del: of_nat_Suc)

  have "\<exists>c. \<forall>z\<in>ball 0 1. ln (1 + z) - ?F z = c"
  proof (rule has_field_derivative_zero_constant)
    fix z :: complex assume z': "z \<in> ball 0 1"
    hence z: "norm z < 1" by (simp add: dist_0_norm)
    def t \<equiv> "of_real (1 + norm z) / 2 :: complex"
    from z have t: "norm z < norm t" "norm t < 1" unfolding t_def
      by (simp_all add: field_simps norm_divide del: of_real_add)

    have "Re (-z) \<le> norm (-z)" by (rule complex_Re_le_cmod)
    also from z have "... < 1" by simp
    finally have "((\<lambda>z. ln (1 + z)) has_field_derivative inverse (1+z)) (at z)"
      by (auto intro!: derivative_eq_intros)
    moreover have "(?F has_field_derivative ?F' z) (at z)" using t r
      by (intro termdiffs_strong[of _ t] summable_in_conv_radius) simp_all
    ultimately have "((\<lambda>z. ln (1 + z) - ?F z) has_field_derivative (inverse (1 + z) - ?F' z)) 
                       (at z within ball 0 1)"
      by (intro derivative_intros) (simp_all add: at_within_open[OF z'])
    also have "(\<lambda>n. of_nat n * ?f n * z ^ (n - Suc 0)) sums ?F' z" using t r
      by (intro diffs_equiv termdiff_converges[OF t(1)] summable_in_conv_radius) simp_all
    from sums_split_initial_segment[OF this, of 1]
      have "(\<lambda>i. (-z) ^ i) sums ?F' z" by (simp add: power_minus[of z] del: of_nat_Suc)
    hence "?F' z = inverse (1 + z)" using z by (simp add: sums_iff suminf_geometric divide_inverse)
    also have "inverse (1 + z) - inverse (1 + z) = 0" by simp
    finally show "((\<lambda>z. ln (1 + z) - ?F z) has_field_derivative 0) (at z within ball 0 1)" .
  qed simp_all
  then obtain c where c: "\<And>z. z \<in> ball 0 1 \<Longrightarrow> ln (1 + z) - ?F z = c" by blast
  from c[of 0] have "c = 0" by (simp only: powser_zero) simp
  with c[of z] assms have "ln (1 + z) = ?F z" by (simp add: dist_0_norm)
  moreover have "summable (\<lambda>n. ?f n * z^n)" using assms r
    by (intro summable_in_conv_radius) simp_all
  ultimately show ?thesis by (simp add: sums_iff)
qed

lemma Ln_approx_linear:
  fixes z :: complex
  assumes "norm z < 1"
  shows   "norm (ln (1 + z) - z) \<le> norm z^2 / (1 - norm z)"
proof -
  let ?f = "\<lambda>n. (-1)^Suc n / of_nat n"
  from assms have "(\<lambda>n. ?f n * z^n) sums ln (1 + z)" using Ln_series by simp
  moreover have "(\<lambda>n. (if n = 1 then 1 else 0) * z^n) sums z" using powser_sums_if[of 1] by simp
  ultimately have "(\<lambda>n. (?f n - (if n = 1 then 1 else 0)) * z^n) sums (ln (1 + z) - z)"
    by (subst left_diff_distrib, intro sums_diff) simp_all
  from sums_split_initial_segment[OF this, of "Suc 1"]
    have "(\<lambda>i. (-(z^2)) * inverse (2 + of_nat i) * (- z)^i) sums (Ln (1 + z) - z)"
    by (simp add: power2_eq_square mult_ac power_minus[of z] divide_inverse)
  hence "(Ln (1 + z) - z) = (\<Sum>i. (-(z^2)) * inverse (of_nat (i+2)) * (-z)^i)"
    by (simp add: sums_iff)
  also have A: "summable (\<lambda>n. norm z^2 * (inverse (real_of_nat (Suc (Suc n))) * cmod z ^ n))"
    by (rule summable_mult, rule summable_comparison_test_ev[OF _ summable_geometric[of "norm z"]])
       (auto simp: assms field_simps intro!: always_eventually)
  hence "norm (\<Sum>i. (-(z^2)) * inverse (of_nat (i+2)) * (-z)^i) \<le> 
             (\<Sum>i. norm (-(z^2) * inverse (of_nat (i+2)) * (-z)^i))"
    by (intro summable_norm)
       (auto simp: norm_power norm_inverse norm_mult mult_ac simp del: of_nat_add of_nat_Suc)
  also have "norm ((-z)^2 * (-z)^i) * inverse (of_nat (i+2)) \<le> norm ((-z)^2 * (-z)^i) * 1" for i
    by (intro mult_left_mono) (simp_all add: divide_simps)
  hence "(\<Sum>i. norm (-(z^2) * inverse (of_nat (i+2)) * (-z)^i)) \<le> 
           (\<Sum>i. norm (-(z^2) * (-z)^i))" using A assms
    apply (simp_all only: norm_power norm_inverse norm_divide norm_mult)
    apply (intro suminf_le summable_mult summable_geometric)
    apply (auto simp: norm_power field_simps simp del: of_nat_add of_nat_Suc)
    done
  also have "... = norm z^2 * (\<Sum>i. norm z^i)" using assms
    by (subst suminf_mult [symmetric]) (auto intro!: summable_geometric simp: norm_mult norm_power)
  also have "(\<Sum>i. norm z^i) = inverse (1 - norm z)" using assms
    by (subst suminf_geometric) (simp_all add: divide_inverse)
  also have "norm z^2 * ... = norm z^2 / (1 - norm z)" by (simp add: divide_inverse)
  finally show ?thesis .
qed


lemma Arctan_series:
  assumes z: "norm (z :: complex) < 1"
  defines "g \<equiv> \<lambda>n. if odd n then -\<i>*\<i>^n / n else 0"
  defines "h \<equiv> \<lambda>z n. (-1)^n / of_nat (2*n+1) * (z::complex)^(2*n+1)"
  shows   "(\<lambda>n. g n * z^n) sums Arctan z"
  and     "h z sums Arctan z"
proof -
  def G \<equiv> "\<lambda>z. (\<Sum>n. g n * z^n)"
  have summable: "summable (\<lambda>n. g n * u^n)" if "norm u < 1" for u
  proof (cases "u = 0")
    assume u: "u \<noteq> 0"
    have "(\<lambda>n. ereal (norm (h u n) / norm (h u (Suc n)))) = (\<lambda>n. ereal (inverse (norm u)^2) * 
              ereal ((2 + inverse (real (Suc n))) / (2 - inverse (real (Suc n)))))"
    proof
      fix n
      have "ereal (norm (h u n) / norm (h u (Suc n))) = 
             ereal (inverse (norm u)^2) * ereal ((of_nat (2*Suc n+1) / of_nat (Suc n)) / 
                 (of_nat (2*Suc n-1) / of_nat (Suc n)))"
      by (simp add: h_def norm_mult norm_power norm_divide divide_simps 
                    power2_eq_square eval_nat_numeral del: of_nat_add of_nat_Suc)
      also have "of_nat (2*Suc n+1) / of_nat (Suc n) = (2::real) + inverse (real (Suc n))"
        by (auto simp: divide_simps simp del: of_nat_Suc) simp_all?
      also have "of_nat (2*Suc n-1) / of_nat (Suc n) = (2::real) - inverse (real (Suc n))"
        by (auto simp: divide_simps simp del: of_nat_Suc) simp_all?      
      finally show "ereal (norm (h u n) / norm (h u (Suc n))) = ereal (inverse (norm u)^2) * 
              ereal ((2 + inverse (real (Suc n))) / (2 - inverse (real (Suc n))))" .
    qed
    also have "\<dots> ----> ereal (inverse (norm u)^2) * ereal ((2 + 0) / (2 - 0))"
      by (intro tendsto_intros LIMSEQ_inverse_real_of_nat) simp_all
    finally have "liminf (\<lambda>n. ereal (cmod (h u n) / cmod (h u (Suc n)))) = inverse (norm u)^2"
      by (intro lim_imp_Liminf) simp_all
    moreover from power_strict_mono[OF that, of 2] u have "inverse (norm u)^2 > 1"
      by (simp add: divide_simps)
    ultimately have A: "liminf (\<lambda>n. ereal (cmod (h u n) / cmod (h u (Suc n)))) > 1" by simp
    from u have "summable (h u)"
      by (intro summable_norm_cancel[OF ratio_test_convergence[OF _ A]])
         (auto simp: h_def norm_divide norm_mult norm_power simp del: of_nat_Suc 
               intro!: mult_pos_pos divide_pos_pos always_eventually)
    thus "summable (\<lambda>n. g n * u^n)"
      by (subst summable_mono_reindex[of "\<lambda>n. 2*n+1", symmetric])
         (auto simp: power_mult subseq_def g_def h_def elim!: oddE)
  qed (simp add: h_def)

  have "\<exists>c. \<forall>u\<in>ball 0 1. Arctan u - G u = c"
  proof (rule has_field_derivative_zero_constant)
    fix u :: complex assume "u \<in> ball 0 1"
    hence u: "norm u < 1" by (simp add: dist_0_norm)
    def K \<equiv> "(norm u + 1) / 2"
    from u and abs_Im_le_cmod[of u] have Im_u: "\<bar>Im u\<bar> < 1" by linarith
    from u have K: "0 \<le> K" "norm u < K" "K < 1" by (simp_all add: K_def)
    hence "(G has_field_derivative (\<Sum>n. diffs g n * u ^ n)) (at u)" unfolding G_def
      by (intro termdiffs_strong[of _ "of_real K"] summable) simp_all
    also have "(\<lambda>n. diffs g n * u^n) = (\<lambda>n. if even n then (\<i>*u)^n else 0)"
      by (intro ext) (simp_all del: of_nat_Suc add: g_def diffs_def power_mult_distrib)
    also have "suminf \<dots> = (\<Sum>n. (-(u^2))^n)"
      by (subst suminf_mono_reindex[of "\<lambda>n. 2*n", symmetric]) 
         (auto elim!: evenE simp: subseq_def power_mult power_mult_distrib)
    also from u have "norm u^2 < 1^2" by (intro power_strict_mono) simp_all
    hence "(\<Sum>n. (-(u^2))^n) = inverse (1 + u^2)" 
      by (subst suminf_geometric) (simp_all add: norm_power inverse_eq_divide)
    finally have "(G has_field_derivative inverse (1 + u\<^sup>2)) (at u)" .
    from DERIV_diff[OF has_field_derivative_Arctan this] Im_u u
      show "((\<lambda>u. Arctan u - G u) has_field_derivative 0) (at u within ball 0 1)"
      by (simp_all add: dist_0_norm at_within_open[OF _ open_ball])
  qed simp_all
  then obtain c where c: "\<And>u. norm u < 1 \<Longrightarrow> Arctan u - G u = c" by (auto simp: dist_0_norm)
  from this[of 0] have "c = 0" by (simp add: G_def g_def powser_zero)
  with c z have "Arctan z = G z" by simp
  with summable[OF z] show "(\<lambda>n. g n * z^n) sums Arctan z" unfolding G_def by (simp add: sums_iff)
  thus "h z sums Arctan z" by (subst (asm) sums_mono_reindex[of "\<lambda>n. 2*n+1", symmetric])
                              (auto elim!: oddE simp: subseq_def power_mult g_def h_def)
qed

definition "moebius a b c d = (\<lambda>z. (a*z+b) / (c*z+d :: 'a :: field))"

lemma moebius_inverse: 
  assumes "a * d \<noteq> b * c" "c * z + d \<noteq> 0"
  shows   "moebius d (-b) (-c) a (moebius a b c d z) = z"
proof -
  from assms have "(-c) * moebius a b c d z + a \<noteq> 0" unfolding moebius_def
    by (simp add: field_simps)
  with assms show ?thesis
    unfolding moebius_def by (simp add: moebius_def divide_simps) (simp add: algebra_simps)?
qed

lemma moebius_inverse': 
  assumes "a * d \<noteq> b * c" "c * z - a \<noteq> 0"
  shows   "moebius a b c d (moebius d (-b) (-c) a z) = z"
  using assms moebius_inverse[of d a "-b" "-c" z]
  by (auto simp: algebra_simps)


lemma Arctan_def_moebius: "Arctan z = \<i>/2 * Ln (moebius (-\<i>) 1 \<i> 1 z)"
  by (simp add: Arctan_def moebius_def add_ac)

lemma Ln_conv_Arctan:
  assumes "z \<noteq> -1"
  shows   "Ln z = -2*\<i> * Arctan (moebius 1 (- 1) (- \<i>) (- \<i>) z)"
proof -
  have "Arctan (moebius 1 (- 1) (- \<i>) (- \<i>) z) =
             \<i>/2 * Ln (moebius (- \<i>) 1 \<i> 1 (moebius 1 (- 1) (- \<i>) (- \<i>) z))"
    by (simp add: Arctan_def_moebius)
  also from assms have "\<i> * z \<noteq> \<i> * (-1)" by (subst mult_left_cancel) simp
  hence "\<i> * z - -\<i> \<noteq> 0" by (simp add: eq_neg_iff_add_eq_0)
  from moebius_inverse'[OF _ this, of 1 1]
    have "moebius (- \<i>) 1 \<i> 1 (moebius 1 (- 1) (- \<i>) (- \<i>) z) = z" by simp
  finally show ?thesis by (simp add: field_simps)
qed

lemma ln_series_quadratic:
  assumes x: "x > (0::real)"
  shows "(\<lambda>n. (2*((x - 1) / (x + 1)) ^ (2*n+1) / of_nat (2*n+1))) sums ln x"
proof -
  def y \<equiv> "of_real ((x-1)/(x+1)) :: complex"
  from x have x': "complex_of_real x \<noteq> of_real (-1)"  by (subst of_real_eq_iff) auto
  from x have "\<bar>x - 1\<bar> < \<bar>x + 1\<bar>" by linarith
  hence "norm (complex_of_real (x - 1) / complex_of_real (x + 1)) < 1"
    by (simp add: norm_divide del: of_real_add of_real_diff)
  hence "norm (\<i> * y) < 1" unfolding y_def by (subst norm_mult) simp
  hence "(\<lambda>n. (-2*\<i>) * ((-1)^n / of_nat (2*n+1) * (\<i>*y)^(2*n+1))) sums ((-2*\<i>) * Arctan (\<i>*y))"
    by (intro Arctan_series sums_mult) simp_all
  also have "(\<lambda>n. (-2*\<i>) * ((-1)^n / of_nat (2*n+1) * (\<i>*y)^(2*n+1))) = 
                 (\<lambda>n. (-2*\<i>) * ((-1)^n * (\<i>*y*(-y\<^sup>2)^n)/of_nat (2*n+1)))"
    by (intro ext) (simp_all add: power_mult power_mult_distrib)
  also have "\<dots> = (\<lambda>n. 2*y* ((-1) * (-y\<^sup>2))^n/of_nat (2*n+1))"
    by (intro ext, subst power_mult_distrib) (simp add: algebra_simps power_mult)
  also have "\<dots> = (\<lambda>n. 2*y^(2*n+1) / of_nat (2*n+1))" 
    by (subst power_add, subst power_mult) (simp add: mult_ac)
  also have "\<dots> = (\<lambda>n. of_real (2*((x-1)/(x+1))^(2*n+1) / of_nat (2*n+1)))"
    by (intro ext) (simp add: y_def)
  also have "\<i> * y = (of_real x - 1) / (-\<i> * (of_real x + 1))"
    by (subst divide_divide_eq_left [symmetric]) (simp add: y_def)
  also have "\<dots> = moebius 1 (-1) (-\<i>) (-\<i>) (of_real x)" by (simp add: moebius_def algebra_simps)
  also from x' have "-2*\<i>*Arctan \<dots> = Ln (of_real x)" by (intro Ln_conv_Arctan [symmetric]) simp_all
  also from x have "\<dots> = ln x" by (rule Ln_of_real)
  finally show ?thesis by (subst (asm) sums_of_real_iff)
qed

end
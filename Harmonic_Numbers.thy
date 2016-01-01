theory Harmonic_Numbers
imports Complex_Main Summation Integral_Test
begin

text \<open>
  The harmonic numbers
\<close>
definition harm :: "nat \<Rightarrow> 'a :: real_normed_field" where
  "harm n = (\<Sum>k=1..n. inverse (of_nat k))"

lemma harm_altdef: "harm n = (\<Sum>k<n. inverse (of_nat (Suc k)))"
  unfolding harm_def by (induction n) simp_all

lemma harm_Suc: "harm (Suc n) = harm n + inverse (of_nat (Suc n))"
  by (simp add: harm_def)

lemma harm_nonneg: "harm n \<ge> (0 :: 'a :: {real_normed_field,linordered_field})"
  unfolding harm_def by (intro setsum_nonneg) simp_all

lemma of_real_harm: "of_real (harm n) = harm n"
  unfolding harm_def by simp
  
lemma norm_harm: "norm (harm n) = harm n"
  by (subst of_real_harm [symmetric]) (simp add: harm_nonneg)

lemma harm_expand: 
  "harm (Suc 0) = 1"
  "harm (numeral n) = harm (pred_numeral n) + inverse (numeral n)"
proof -
  have "numeral n = Suc (pred_numeral n)" by simp
  also have "harm \<dots> = harm (pred_numeral n) + inverse (numeral n)"
    by (subst harm_Suc, subst numeral_eq_Suc[symmetric]) simp
  finally show "harm (numeral n) = harm (pred_numeral n) + inverse (numeral n)" .
qed (simp add: harm_def)

lemma not_convergent_harm: "\<not>convergent (harm :: nat \<Rightarrow> 'a :: real_normed_field)"
proof -
  have "convergent (\<lambda>n. norm (harm n :: 'a)) \<longleftrightarrow>
            convergent (harm :: nat \<Rightarrow> real)" by (simp add: norm_harm)
  also have "\<dots> \<longleftrightarrow> convergent (\<lambda>n. \<Sum>k=Suc 0..Suc n. inverse (of_nat k) :: real)"
    unfolding harm_def[abs_def] by (subst convergent_Suc_iff) simp_all
  also have "... \<longleftrightarrow> convergent (\<lambda>n. \<Sum>k\<le>n. inverse (of_nat (Suc k)) :: real)"
    by (subst setsum_shift_bounds_cl_Suc_ivl) (simp add: atLeast0AtMost)
  also have "... \<longleftrightarrow> summable (\<lambda>n. inverse (of_nat n) :: real)"
    by (subst summable_Suc_iff [symmetric]) (simp add: summable_iff_convergent')
  also have "\<not>..." by (rule not_summable_harmonic)
  finally show ?thesis by (blast dest: convergent_norm)
qed


subsection \<open>The Euler–Mascheroni constant\<close>

text \<open>
  The limit of the difference between the partial harmonic sum and the natural logarithm
  (approximately 0.577216). This value occurs e.g. in the definition of the Gamma function.
 \<close>
definition euler_mascheroni :: "'a :: real_normed_algebra_1" where
  "euler_mascheroni = of_real (lim (\<lambda>n. harm n - ln (of_nat n)))"

lemma of_real_euler_mascheroni [simp]: "of_real euler_mascheroni = euler_mascheroni"
  by (simp add: euler_mascheroni_def)

interpretation euler_mascheroni: antimono_fun_sum_integral_diff "\<lambda>x. inverse (x + 1)"
  by unfold_locales (auto intro!: continuous_intros)

lemma euler_mascheroni_sum_integral_diff_series:
  "euler_mascheroni.sum_integral_diff_series n = harm (Suc n) - ln (of_nat (Suc n))"
proof -
  have "harm (Suc n) = (\<Sum>k=0..n. inverse (of_nat k + 1) :: real)" unfolding harm_def
    unfolding One_nat_def by (subst setsum_shift_bounds_cl_Suc_ivl) (simp add: add_ac)
  moreover have "((\<lambda>x. inverse (x + 1) :: real) has_integral ln (of_nat n + 1) - ln (0 + 1))
                   {0..of_nat n}"
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros simp: divide_inverse
           has_field_derivative_iff_has_vector_derivative[symmetric])
  hence "integral {0..of_nat n} (\<lambda>x. inverse (x + 1) :: real) = ln (of_nat (Suc n))"
    by (auto dest!: integral_unique)
  ultimately show ?thesis 
    by (simp add: euler_mascheroni.sum_integral_diff_series_def atLeast0AtMost)
qed

lemma euler_mascheroni_sequence_decreasing:
  "m > 0 \<Longrightarrow> m \<le> n \<Longrightarrow> harm n - ln (of_nat n) \<le> harm m - ln (of_nat m :: real)"
  by (cases m, simp, cases n, simp, hypsubst,
      subst (1 2) euler_mascheroni_sum_integral_diff_series [symmetric],
      rule euler_mascheroni.sum_integral_diff_series_antimono, simp)

lemma euler_mascheroni_sequence_nonneg:
  "n > 0 \<Longrightarrow> harm n - ln (of_nat n) \<ge> (0::real)"
  by (cases n, simp, hypsubst, subst euler_mascheroni_sum_integral_diff_series [symmetric],
      rule euler_mascheroni.sum_integral_diff_series_nonneg)

lemma euler_mascheroni_convergent: "convergent (\<lambda>n. harm n - ln (of_nat n) :: real)"
proof -
  have A: "(\<lambda>n. harm (Suc n) - ln (of_nat (Suc n))) = 
             euler_mascheroni.sum_integral_diff_series"
    by (subst euler_mascheroni_sum_integral_diff_series [symmetric]) (rule refl)
  have "convergent (\<lambda>n. harm (Suc n) - ln (of_nat (Suc n) :: real))"
    by (subst A) (fact euler_mascheroni.sum_integral_diff_series_convergent)
  thus ?thesis by (subst (asm) convergent_Suc_iff)
qed

lemma euler_mascheroni_LIMSEQ: 
  "(\<lambda>n. harm n - ln (of_nat n) :: real) ----> euler_mascheroni"
  unfolding euler_mascheroni_def
  by (simp add: convergent_LIMSEQ_iff [symmetric] euler_mascheroni_convergent)

lemma euler_mascheroni_LIMSEQ_of_real: 
  "(\<lambda>n. of_real (harm n - ln (of_nat n))) ----> 
      (euler_mascheroni :: 'a :: {real_normed_algebra_1, topological_space})"
proof -
  have "(\<lambda>n. of_real (harm n - ln (of_nat n))) ----> (of_real (euler_mascheroni) :: 'a)"
    by (intro tendsto_of_real euler_mascheroni_LIMSEQ)
  thus ?thesis by simp
qed

lemma euler_mascheroni_sum:
  "(\<lambda>n. inverse (of_nat (n+1)) + ln (of_nat (n+1)) - ln (of_nat (n+2)) :: real)
       sums euler_mascheroni" 
 using sums_add[OF telescope_sums[OF LIMSEQ_Suc[OF euler_mascheroni_LIMSEQ]]
                   telescope_sums'[OF LIMSEQ_inverse_real_of_nat]]
  by (simp_all add: harm_def algebra_simps)

lemma alternating_harmonic_series_sums: "(\<lambda>k. (-1)^k / real_of_nat (Suc k)) sums ln 2"
proof -
  let ?f = "\<lambda>n. harm n - ln (real_of_nat n)"
  let ?g = "\<lambda>n. if even n then 0 else (2::real)"
  let ?em = "\<lambda>n. harm n - ln (real_of_nat n)"
  have "eventually (\<lambda>n. ?em (2*n) - ?em n + ln 2 = (\<Sum>k<2*n. (-1)^k / real_of_nat (Suc k))) at_top"
    using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    fix n :: nat assume n: "n > 0"
    have "(\<Sum>k<2*n. (-1)^k / real_of_nat (Suc k)) =
              (\<Sum>k<2*n. ((-1)^k + ?g k) / of_nat (Suc k)) - (\<Sum>k<2*n. ?g k / of_nat (Suc k))"
      by (simp add: setsum.distrib algebra_simps divide_inverse)
    also have "(\<Sum>k<2*n. ((-1)^k + ?g k) / real_of_nat (Suc k)) = harm (2*n)"
      unfolding harm_altdef by (intro setsum.cong) (auto simp: field_simps)
    also have "(\<Sum>k<2*n. ?g k / real_of_nat (Suc k)) = (\<Sum>k|k<2*n \<and> odd k. ?g k / of_nat (Suc k))"
      by (intro setsum.mono_neutral_right) auto
    also have "\<dots> = (\<Sum>k|k<2*n \<and> odd k. 2 / (real_of_nat (Suc k)))"
      by (intro setsum.cong) auto
    also have "(\<Sum>k|k<2*n \<and> odd k. 2 / (real_of_nat (Suc k))) = harm n" 
      unfolding harm_altdef
      by (intro setsum.reindex_cong[of "\<lambda>n. 2*n+1"]) (auto simp: inj_on_def field_simps elim!: oddE)
    also have "harm (2*n) - harm n = ?em (2*n) - ?em n + ln 2" using n
      by (simp_all add: algebra_simps ln_mult)
    finally show "?em (2*n) - ?em n + ln 2 = (\<Sum>k<2*n. (-1)^k / real_of_nat (Suc k))" ..
  qed
  moreover have "(\<lambda>n. ?em (2*n) - ?em n + ln (2::real)) 
                     ----> euler_mascheroni - euler_mascheroni + ln 2"
    by (intro tendsto_intros euler_mascheroni_LIMSEQ filterlim_compose[OF euler_mascheroni_LIMSEQ]
              filterlim_subseq) (auto simp: subseq_def)
  hence "(\<lambda>n. ?em (2*n) - ?em n + ln (2::real)) ----> ln 2" by simp
  ultimately have "(\<lambda>n. (\<Sum>k<2*n. (-1)^k / real_of_nat (Suc k))) ----> ln 2"
    by (rule Lim_transform_eventually)
  
  moreover have "summable (\<lambda>k. (-1)^k * inverse (real_of_nat (Suc k)))"
    using LIMSEQ_inverse_real_of_nat
    by (intro summable_Leibniz(1) decseq_imp_monoseq decseq_SucI) simp_all
  hence A: "(\<lambda>n. \<Sum>k<n. (-1)^k / real_of_nat (Suc k)) ----> (\<Sum>k. (-1)^k / real_of_nat (Suc k))"
    by (simp add: summable_sums_iff divide_inverse sums_def)
  from filterlim_compose[OF this filterlim_subseq[of "op * (2::nat)"]]
    have "(\<lambda>n. \<Sum>k<2*n. (-1)^k / real_of_nat (Suc k)) ----> (\<Sum>k. (-1)^k / real_of_nat (Suc k))"
    by (simp add: subseq_def)
  ultimately have "(\<Sum>k. (- 1) ^ k / real_of_nat (Suc k)) = ln 2" by (intro LIMSEQ_unique)
  with A show ?thesis by (simp add: sums_def)
qed

lemma alternating_harmonic_series_sums': 
  "(\<lambda>k. inverse (real_of_nat (2*k+1)) - inverse (real_of_nat (2*k+2))) sums ln 2"
unfolding sums_def
proof (rule Lim_transform_eventually)
  show "(\<lambda>n. \<Sum>k<2*n. (-1)^k / (real_of_nat (Suc k))) ----> ln 2"
    using alternating_harmonic_series_sums unfolding sums_def 
    by (rule filterlim_compose) (rule mult_nat_left_at_top, simp)
  show "eventually (\<lambda>n. (\<Sum>k<2*n. (-1)^k / (real_of_nat (Suc k))) =
            (\<Sum>k<n. inverse (real_of_nat (2*k+1)) - inverse (real_of_nat (2*k+2)))) sequentially"
  proof (intro always_eventually allI)
    fix n :: nat
    show "(\<Sum>k<2*n. (-1)^k / (real_of_nat (Suc k))) =
              (\<Sum>k<n. inverse (real_of_nat (2*k+1)) - inverse (real_of_nat (2*k+2)))"
      by (induction n) (simp_all add: inverse_eq_divide)
  qed
qed               

end
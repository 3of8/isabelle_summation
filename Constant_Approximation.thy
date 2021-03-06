theory Constant_Approximation
imports Complex_Main Ln_Arctan_Series Harmonic_Numbers
begin

(* FIXME: ugly *)
lemma ln_inverse_approx_le:
  assumes "(x::real) > 0" "a > 0"
  shows   "ln (x + a) - ln x \<le> a * (inverse x + inverse (x + a))/2" (is "_ \<le> ?A")
proof -
  def f' \<equiv> "(inverse (x + a) - inverse x)/a"
  have f'_nonpos: "f' \<le> 0" using assms by (simp add: f'_def divide_simps)
  let ?f = "\<lambda>t. (t - x) * f' + inverse x"
  let ?F = "\<lambda>t. (t - x)^2 * f' / 2 + t * inverse x"
  have diff: "\<forall>t\<in>{x..x+a}. (?F has_vector_derivative ?f t) 
                               (at t within {x..x+a})" using assms
    by (auto intro!: derivative_eq_intros 
             simp: has_field_derivative_iff_has_vector_derivative[symmetric])
  from assms have "(?f has_integral (?F (x+a) - ?F x)) {x..x+a}"
    by (intro fundamental_theorem_of_calculus[OF _ diff])
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric] field_simps
             intro!: derivative_eq_intros)
  also have "?F (x+a) - ?F x = (a*2 + f'*a\<^sup>2*x) / (2*x)" using assms by (simp add: field_simps)
  also have "f'*a^2 = - (a^2) / (x*(x + a))" using assms 
    by (simp add: divide_simps f'_def power2_eq_square)
  also have "(a*2 + - a\<^sup>2/(x*(x+a))*x) / (2*x) = ?A" using assms
    by (simp add: divide_simps power2_eq_square) (simp add: algebra_simps)
  finally have int1: "((\<lambda>t. (t - x) * f' + inverse x) has_integral ?A) {x..x + a}" .

  from assms have int2: "(inverse has_integral (ln (x + a) - ln x)) {x..x+a}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric] divide_simps
             intro!: derivative_eq_intros)
  hence "ln (x + a) - ln x = integral {x..x+a} inverse" by (simp add: integral_unique)
  also have ineq: "\<forall>xa\<in>{x..x + a}. inverse xa \<le> (xa - x) * f' + inverse x"
  proof
    fix t assume t': "t \<in> {x..x+a}"
    with assms have t: "0 \<le> (t - x) / a" "(t - x) / a \<le> 1" by simp_all
    have "inverse t = inverse ((1 - (t - x) / a) *\<^sub>R x + ((t - x) / a) *\<^sub>R (x + a))" (is "_ = ?A")
      using assms t' by (simp add: field_simps)
    also from assms have "convex_on {x..x+a} inverse" by (intro convex_on_inverse) auto
    from convex_onD_Icc[OF this _ t] assms 
      have "?A \<le> (1 - (t - x) / a) * inverse x + (t - x) / a * inverse (x + a)" by simp
    also have "\<dots> = (t - x) * f' + inverse x" using assms
      by (simp add: f'_def divide_simps) (simp add: f'_def field_simps)
    finally show "inverse t \<le> (t - x) * f' + inverse x" .
  qed
  hence "integral {x..x+a} inverse \<le> integral {x..x+a} ?f" using f'_nonpos assms
    by (intro integral_le has_integral_integrable[OF int1] has_integral_integrable[OF int2] ineq)
  also have "\<dots> = ?A" using int1 by (rule integral_unique)
  finally show ?thesis .
qed

lemma setsum_Suc_diff':
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
  assumes "m \<le> n"
  shows "(\<Sum>i = m..<n. f(Suc i) - f i) = f n - f m"
using assms by (induct n) (auto simp: le_Suc_eq)

lemma ln_inverse_approx_ge:
  assumes "(x::real) > 0" "x < y"
  shows   "ln y - ln x \<ge> 2 * (y - x) / (x + y)" (is "_ \<ge> ?A")
proof -
  def m \<equiv> "(x+y)/2"
  def f' \<equiv> "-inverse (m^2)"
  from assms have m: "m > 0" by (simp add: m_def)
  let ?F = "\<lambda>t. (t - m)^2 * f' / 2 + t / m"
  from assms have "((\<lambda>t. (t - m) * f' + inverse m) has_integral (?F y - ?F x)) {x..y}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric] divide_simps
             intro!: derivative_eq_intros)
  also from m have "?F y - ?F x = ((y - m)^2 - (x - m)^2) * f' / 2 + (y - x) / m" 
    by (simp add: field_simps)
  also have "((y - m)^2 - (x - m)^2) = 0" by (simp add: m_def power2_eq_square field_simps)
  also have "0 * f' / 2 + (y - x) / m = ?A" by (simp add: m_def)
  finally have int1: "((\<lambda>t. (t - m) * f' + inverse m) has_integral ?A) {x..y}" .

  from assms have int2: "(inverse has_integral (ln y - ln x)) {x..y}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric] divide_simps
             intro!: derivative_eq_intros)
  hence "ln y - ln x = integral {x..y} inverse" by (simp add: integral_unique)
  also have ineq: "\<forall>xa\<in>{x..y}. inverse xa \<ge> (xa - m) * f' + inverse m"
  proof
    fix t assume t: "t \<in> {x..y}"
    from t assms have "inverse t - inverse m \<ge> f' * (t - m)"
      by (intro convex_on_imp_above_tangent[of "{0<..}"] convex_on_inverse)
         (auto simp: m_def interior_open f'_def power2_eq_square intro!: derivative_eq_intros)
    thus "(t - m) * f' + inverse m \<le> inverse t" by (simp add: algebra_simps)
  qed
  hence "integral {x..y} inverse \<ge> integral {x..y} (\<lambda>t. (t - m) * f' + inverse m)"
    using int1 int2 by (intro integral_le has_integral_integrable)
  also have "integral {x..y} (\<lambda>t. (t - m) * f' + inverse m) = ?A"
    using integral_unique[OF int1] by simp
  finally show ?thesis .
qed


lemma euler_mascheroni_lower: 
        "euler_mascheroni \<ge> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 2))"
  and euler_mascheroni_upper:
        "euler_mascheroni \<le> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 1))"
proof -
  def D \<equiv> "\<lambda>n. inverse (of_nat (n+1)) + ln (of_nat (n+1)) - ln (of_nat (n+2)) :: real"
  let ?g = "\<lambda>n. ln (of_nat (n+2)) - ln (of_nat (n+1)) - inverse (of_nat (n+1)) :: real"
  def inv \<equiv> "\<lambda>n. inverse (real_of_nat n)"
  fix n :: nat
  note summable = sums_summable[OF euler_mascheroni_sum, folded D_def]
  have sums: "(\<lambda>k. (inv (Suc (k + (n+1))) - inv (Suc (Suc k + (n+1))))/2) sums ((inv (Suc (0 + (n+1))) - 0)/2)"
    unfolding inv_def
    by (intro sums_divide telescope_sums' LIMSEQ_ignore_initial_segment LIMSEQ_inverse_real_of_nat)
  have sums': "(\<lambda>k. (inv (Suc (k + n)) - inv (Suc (Suc k + n)))/2) sums ((inv (Suc (0 + n)) - 0)/2)"
    unfolding inv_def
    by (intro sums_divide telescope_sums' LIMSEQ_ignore_initial_segment LIMSEQ_inverse_real_of_nat)
  from euler_mascheroni_sum have "euler_mascheroni = (\<Sum>k. D k)"
    by (simp add: sums_iff D_def)
  also have "\<dots> = (\<Sum>k. D (k + Suc n)) + (\<Sum>k\<le>n. D k)"
    by (subst suminf_split_initial_segment[OF summable, of "Suc n"], subst lessThan_Suc_atMost) simp
  finally have sum: "(\<Sum>k\<le>n. D k) - euler_mascheroni = -(\<Sum>k. D (k + Suc n))" by simp

  note sum
  also have "\<dots> \<le> -(\<Sum>k. (inv (k + Suc n + 1) - inv (k + Suc n + 2)) / 2)"
  proof (intro le_imp_neg_le suminf_le allI summable_ignore_initial_segment[OF summable])
    fix k' :: nat
    def k \<equiv> "k' + Suc n"
    hence k: "k > 0" by (simp add: k_def)
    have "real_of_nat (k+1) > 0" by (simp add: k_def)
    with ln_inverse_approx_le[OF this zero_less_one]
      have "ln (of_nat k + 2) - ln (of_nat k + 1) \<le> (inv (k+1) + inv (k+2))/2"
      by (simp add: inv_def add_ac)
    hence "(inv (k+1) - inv (k+2))/2 \<le> inv (k+1) + ln (of_nat (k+1)) - ln (of_nat (k+2))"
      by (simp add: field_simps)
    also have "\<dots> = D k" unfolding D_def inv_def ..
    finally show "D (k' + Suc n) \<ge> (inv (k' + Suc n + 1) - inv (k' + Suc n + 2)) / 2"
      by (simp add: k_def)
    from sums_summable[OF sums] 
      show "summable (\<lambda>k. (inv (k + Suc n + 1) - inv (k + Suc n + 2))/2)" by simp
  qed
  also from sums have "\<dots> = -inv (n+2) / 2" by (simp add: sums_iff)
  finally have "euler_mascheroni \<ge> (\<Sum>k\<le>n. D k) + 1 / (of_nat (2 * (n+2)))" 
    by (simp add: inv_def field_simps of_nat_mult)
  also have "(\<Sum>k\<le>n. D k) = harm (Suc n) - (\<Sum>k\<le>n. ln (real_of_nat (Suc k+1)) - ln (of_nat (k+1)))"
    unfolding harm_altdef D_def by (subst lessThan_Suc_atMost) (simp add:  setsum.distrib setsum_subtractf)
  also have "(\<Sum>k\<le>n. ln (real_of_nat (Suc k+1)) - ln (of_nat (k+1))) = ln (of_nat (n+2))"
    by (subst atLeast0AtMost [symmetric], subst setsum_Suc_diff) simp_all
  finally show "euler_mascheroni \<ge> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 2))"
    by simp
  
  note sum
  also have "-(\<Sum>k. D (k + Suc n)) \<ge> -(\<Sum>k. (inv (Suc (k + n)) - inv (Suc (Suc k + n)))/2)"
  proof (intro le_imp_neg_le suminf_le allI summable_ignore_initial_segment[OF summable])
    fix k' :: nat
    def k \<equiv> "k' + Suc n"
    hence k: "k > 0" by (simp add: k_def)
    have "real_of_nat (k+1) > 0" by (simp add: k_def)
    from ln_inverse_approx_ge[of "of_nat k + 1" "of_nat k + 2"]
      have "2 / (2 * real_of_nat k + 3) \<le> ln (of_nat (k+2)) - ln (real_of_nat (k+1))"
      by (simp add: add_ac)
    hence "D k \<le> 1 / real_of_nat (k+1) - 2 / (2 * real_of_nat k + 3)" 
      by (simp add: D_def inverse_eq_divide inv_def)
    also have "\<dots> = inv ((k+1)*(2*k+3))" unfolding inv_def by (simp add: field_simps)
    also have "\<dots> \<le> inv (2*k*(k+1))" unfolding inv_def using k
      by (intro le_imp_inverse_le) 
         (simp add: algebra_simps, simp del: of_nat_add)
    also have "\<dots> = (inv k - inv (k+1))/2" unfolding inv_def using k
      by (simp add: divide_simps del: of_nat_mult) (simp add: algebra_simps)
    finally show "D k \<le> (inv (Suc (k' + n)) - inv (Suc (Suc k' + n)))/2" unfolding k_def by simp
  next
    from sums_summable[OF sums'] 
      show "summable (\<lambda>k. (inv (Suc (k + n)) - inv (Suc (Suc k + n)))/2)" by simp
  qed
  also from sums' have "(\<Sum>k. (inv (Suc (k + n)) - inv (Suc (Suc k + n)))/2) = inv (n+1)/2"
    by (simp add: sums_iff)
  finally have "euler_mascheroni \<le> (\<Sum>k\<le>n. D k) + 1 / of_nat (2 * (n+1))" 
    by (simp add: inv_def field_simps)
  also have "(\<Sum>k\<le>n. D k) = harm (Suc n) - (\<Sum>k\<le>n. ln (real_of_nat (Suc k+1)) - ln (of_nat (k+1)))"
    unfolding harm_altdef D_def by (subst lessThan_Suc_atMost) (simp add:  setsum.distrib setsum_subtractf)
  also have "(\<Sum>k\<le>n. ln (real_of_nat (Suc k+1)) - ln (of_nat (k+1))) = ln (of_nat (n+2))"
    by (subst atLeast0AtMost [symmetric], subst setsum_Suc_diff) simp_all
  finally show "euler_mascheroni \<le> harm (Suc n) - ln (real_of_nat (n + 2)) + 1/real_of_nat (2 * (n + 1))"
    by simp
qed

lemma ln_2_less_1: "ln 2 < (1::real)"
proof -
  have "2 < 5/(2::real)" by simp
  also have "5/2 \<le> exp (1::real)" using exp_lower_taylor_quadratic[of 1, simplified] by simp
  finally have "exp (ln 2) < exp (1::real)" by simp
  thus "ln 2 < (1::real)" by (subst (asm) exp_less_cancel_iff) simp
qed

lemma euler_mascheroni_pos: "euler_mascheroni > (0::real)"
  using euler_mascheroni_lower[of 0] ln_2_less_1 by (simp add: harm_def)

lemma ln_approx_aux:
  fixes n :: nat and x :: real
  defines "y \<equiv> (x-1)/(x+1)"
  assumes x: "x > 0" "x \<noteq> 1"
  shows "inverse (2*y^(2*n+1)) * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))) \<in> 
            {0..(1 / (1 - y^2) / of_nat (2*n+1))}"
proof -
  from x have norm_y: "norm y < 1" unfolding y_def by simp
  from power_strict_mono[OF this, of 2] have norm_y': "norm y^2 < 1" by simp

  let ?f = "\<lambda>k. 2 * y ^ (2*k+1) / of_nat (2*k+1)"
  note sums = ln_series_quadratic[OF x(1)]
  def c \<equiv> "inverse (2*y^(2*n+1))"
  let ?d = "c * (ln x - (\<Sum>k<n. ?f k))"
  have "\<forall>k. y\<^sup>2^k / of_nat (2*(k+n)+1) \<le> y\<^sup>2 ^ k / of_nat (2*n+1)"
    by (intro allI divide_left_mono mult_right_mono mult_pos_pos zero_le_power[of "y^2"]) simp_all
  moreover {
    have "(\<lambda>k. ?f (k + n)) sums (ln x - (\<Sum>k<n. ?f k))"
      using sums_split_initial_segment[OF sums] by (simp add: y_def)
    hence "(\<lambda>k. c * ?f (k + n)) sums ?d" by (rule sums_mult)
    also have "(\<lambda>k. c * (2*y^(2*(k+n)+1) / of_nat (2*(k+n)+1))) =
                   (\<lambda>k. (c * (2*y^(2*n+1))) * ((y^2)^k / of_nat (2*(k+n)+1)))"
      by (simp only: ring_distribs power_add power_mult) (simp add: mult_ac)
    also from x have "c * (2*y^(2*n+1)) = 1" by (simp add: c_def y_def)
    finally have "(\<lambda>k. (y^2)^k / of_nat (2*(k+n)+1)) sums ?d" by simp
  } note sums' = this
  moreover from norm_y' have "(\<lambda>k. (y^2)^k / of_nat (2*n+1)) sums (1 / (1 - y^2) / of_nat (2*n+1))"
    by (intro sums_divide geometric_sums) (simp_all add: norm_power)
  ultimately have "?d \<le> (1 / (1 - y^2) / of_nat (2*n+1))" by (rule sums_le)
  moreover have "c * (ln x - (\<Sum>k<n. 2 * y ^ (2 * k + 1) / real_of_nat (2 * k + 1))) \<ge> 0"
    by (intro sums_le[OF _ sums_zero sums']) simp_all
  ultimately show ?thesis unfolding c_def by simp
qed

lemma
  fixes n :: nat and x :: real
  defines "y \<equiv> (x-1)/(x+1)"
  defines "approx \<equiv> (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))"
  defines "d \<equiv> y^(2*n+1) / (1 - y^2) / of_nat (2*n+1)"
  assumes x: "x > 1"
  shows   ln_approx_bounds: "ln x \<in> {approx..approx + 2*d}"
  and     ln_approx_abs:    "abs (ln x - (approx + d)) \<le> d"
proof -
  def c \<equiv> "2*y^(2*n+1)"
  from x have c_pos: "c > 0" unfolding c_def y_def 
    by (intro mult_pos_pos zero_less_power) simp_all
  have A: "inverse c * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))) \<in>
              {0.. (1 / (1 - y^2) / of_nat (2*n+1))}" using assms unfolding y_def c_def
    by (intro ln_approx_aux) simp_all
  hence "inverse c * (ln x - (\<Sum>k<n. 2*y^(2*k+1)/of_nat (2*k+1))) \<le> (1 / (1-y^2) / of_nat (2*n+1))"
    by simp
  hence "(ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))) / c \<le> (1 / (1 - y^2) / of_nat (2*n+1))" 
    by (auto simp add: divide_simps)
  with c_pos have "ln x \<le> c / (1 - y^2) / of_nat (2*n+1) + approx"
    by (subst (asm) pos_divide_le_eq) (simp_all add: mult_ac approx_def)
  moreover {
    from A c_pos have "0 \<le> c * (inverse c * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1))))"
      by (intro mult_nonneg_nonneg[of c]) simp_all
    also have "\<dots> = (c * inverse c) * (ln x - (\<Sum>k<n. 2*y^(2*k+1) / of_nat (2*k+1)))"  
      by (simp add: mult_ac)
    also from c_pos have "c * inverse c = 1" by simp
    finally have "ln x \<ge> approx" by (simp add: approx_def)
  }
  ultimately show "ln x \<in> {approx..approx + 2*d}" by (simp add: c_def d_def)
  thus "abs (ln x - (approx + d)) \<le> d" by auto
qed

lemma ln_approx_abs': 
  assumes "x > (1::real)"
  assumes "(x-1)/(x+1) = y"
  assumes "y^2 = ysqr"
  assumes "(\<Sum>k<n. inverse (of_nat (2*k+1)) * ysqr^k) = approx"
  assumes "y*ysqr^n / (1 - ysqr) / of_nat (2*n+1) = d"
  assumes "d \<le> e"
  shows   "abs (ln x - (2*y*approx + d)) \<le> e"
proof -
  note ln_approx_abs[OF assms(1), of n]
  also note assms(2)
  also have "y^(2*n+1) = y*ysqr^n" by (simp add: assms(3)[symmetric] power_mult)
  also note assms(3)
  also note assms(5)
  also note assms(5)
  also note assms(6)
  also have "(\<Sum>k<n. 2*y^(2*k+1) / real_of_nat (2 * k + 1)) = (2*y) * approx"
    apply (subst assms(4)[symmetric], subst setsum_right_distrib)
    apply (simp add: assms(3)[symmetric] power_mult)
    apply (simp add: mult_ac divide_simps)?
    done
  finally show ?thesis .
qed

lemma ln_2_approx: "\<bar>ln 2 - 0.69314718055\<bar> < inverse (2 ^ 36 :: real)" (is ?thesis1)
  and ln_2_bounds: "ln (2::real) \<in> {0.693147180549..0.693147180561}" (is ?thesis2)
proof -
  def approx \<equiv> "0.69314718055 :: real" and approx' \<equiv> "4465284211343447 / 6442043387911560 :: real"
  def d \<equiv> "inverse (195259926456::real)"
  have "dist (ln 2) approx \<le> dist (ln 2) approx' + dist approx' approx" by (rule dist_triangle)
  also have "\<bar>ln (2::real) - (2 * (1/3) * (651187280816108 / 626309773824735) +
                 inverse 195259926456)\<bar> \<le> inverse 195259926456"
  proof (rule ln_approx_abs'[where n = 10])
    show "(1/3::real)^2 = 1/9" by (simp add: power2_eq_square)
  qed (simp_all add: eval_nat_numeral)
  hence A: "dist (ln 2) approx' \<le> d" by (simp add: dist_real_def approx'_def d_def)
  hence "dist (ln 2) approx' + dist approx' approx \<le> \<dots> + dist approx' approx"
    by (rule add_right_mono)
  also have "\<dots> < inverse (2 ^ 36)" by (simp add: dist_real_def approx'_def approx_def d_def)
  finally show ?thesis1 unfolding dist_real_def approx_def .
  
  from A have "ln 2 \<in> {approx' - d..approx' + d}" 
    by (simp add: dist_real_def abs_real_def split: split_if_asm)
  also have "\<dots> \<subseteq> {0.693147180549..0.693147180561}"
    by (subst atLeastatMost_subset_iff, rule disjI2) (simp add: approx'_def d_def)
  finally show ?thesis2 .
qed

lemma euler_mascheroni_bounds:
  fixes n :: nat assumes "n \<ge> 1" defines "t \<equiv> harm n - ln (of_nat (Suc n)) :: real"
  shows "euler_mascheroni \<in> {t + inverse (of_nat (2*(n+1)))..t + inverse (of_nat (2*n))}"
  using assms euler_mascheroni_upper[of "n-1"] euler_mascheroni_lower[of "n-1"]
  unfolding t_def by (cases n) (simp_all add: harm_Suc t_def inverse_eq_divide of_nat_mult)

lemma euler_mascheroni_bounds':
  fixes n :: nat assumes "n \<ge> 1" "ln (real_of_nat (Suc n)) \<in> {l<..<u}"
  shows "euler_mascheroni \<in> {harm n - u + inverse (of_nat (2*(n+1)))<..<harm n - l + inverse (of_nat (2*n))}"
  using euler_mascheroni_bounds[OF assms(1)] assms(2) by auto

lemma setsum_poly_horner_expand:
  "(\<Sum>k<(numeral n::nat). f k * x^k) = f 0 + (\<Sum>k<pred_numeral n. f (k+1) * x^k) * x"
  "(\<Sum>k<Suc 0. f k * x^k) = (f 0 :: 'a :: semiring_1)"
  "(\<Sum>k<(0::nat). f k * x^k) = 0"
proof -
  {
    fix m :: nat
    have "(\<Sum>k<Suc m. f k * x^k) = f 0 + (\<Sum>k=Suc 0..<Suc m. f k * x^k)"
      by (subst atLeast0LessThan [symmetric], subst setsum_head_upt_Suc) simp_all
    also have "(\<Sum>k=Suc 0..<Suc m. f k * x^k) = (\<Sum>k<m. f (k+1) * x^k) * x"
      by (subst setsum_shift_bounds_Suc_ivl)
         (simp add: setsum_left_distrib algebra_simps atLeast0LessThan power_commutes)
    finally have "(\<Sum>k<Suc m. f k * x ^ k) = f 0 + (\<Sum>k<m. f (k + 1) * x ^ k) * x" .
  }
  from this[of "pred_numeral n"] 
    show "(\<Sum>k<numeral n. f k * x^k) = f 0 + (\<Sum>k<pred_numeral n. f (k+1) * x^k) * x" 
    by (simp add: numeral_eq_Suc)
qed simp_all

lemma eval_fact:
  "fact 0 = 1"
  "fact (Suc 0) = 1"
  "fact (numeral n) = numeral n * fact (pred_numeral n)"
  by (simp, simp, simp_all only: numeral_eq_Suc fact_Suc,
      simp only: numeral_eq_Suc [symmetric] of_nat_numeral)

lemma euler_mascheroni_approx: 
  defines "approx \<equiv> 0.577257 :: real" and "e \<equiv> 0.000063 :: real"
  shows   "abs (euler_mascheroni - approx :: real) < e"
  (is "abs (_ - ?approx) < ?e")
proof -
  def l \<equiv> "47388813395531028639296492901910937/82101866951584879688289000000000000 :: real"
  def u \<equiv> "142196984054132045946501548559032969 / 246305600854754639064867000000000000 :: real"
  have impI: "P \<longrightarrow> Q" if Q for P Q using that by blast
  have hsum_63: "harm 63 = (310559566510213034489743057 / 65681493561267903750631200 ::real)"
    by (simp add: harm_expand)
  from harm_Suc[of 63] have hsum_64: "harm 64 = 
          623171679694215690971693339 / (131362987122535807501262400::real)" 
    by (subst (asm) hsum_63) simp
  have "ln (64::real) = real (6::nat) * ln 2" by (subst ln_realpow[symmetric]) simp_all
  hence "ln (real_of_nat (Suc 63)) \<in> {4.158883083293<..<4.158883083367}" using ln_2_bounds by simp
  from euler_mascheroni_bounds'[OF _ this]
    have "(euler_mascheroni :: real) \<in> {l<..<u}" 
    by (simp add: hsum_63 del: greaterThanLessThan_iff) (simp only: l_def u_def)
  also have "\<dots> \<subseteq> {approx - e<..<approx + e}"
    by (subst greaterThanLessThan_subseteq_greaterThanLessThan, rule impI) 
       (simp add: approx_def e_def u_def l_def)
  finally show ?thesis by (simp add: abs_real_def)
qed

end
theory Natlog2
imports Complex_Main
begin

definition "natlog2 n = (if n = 0 then 0 else nat \<lfloor>log 2 (real_of_nat n)\<rfloor>)"

lemma natlog2_0: "natlog2 0 = 0" by (simp add: natlog2_def)  

lemma natlog2_power_of_two [simp]: "natlog2 (2 ^ n) = n"
  by (simp add: natlog2_def log_nat_power)

lemma powr_real_of_int: 
  "x > 0 \<Longrightarrow> x powr real_of_int n = (if n \<ge> 0 then x ^ nat n else inverse (x ^ nat (-n)))"
  using powr_realpow[of x "nat n"] powr_realpow[of x "nat (-n)"]
  by (auto simp: field_simps powr_minus)


lemma natlog2_mono: "m \<le> n \<Longrightarrow> natlog2 m \<le> natlog2 n"
  unfolding natlog2_def by (simp_all add: nat_mono floor_mono)

lemma pow_natlog2_le: "n > 0 \<Longrightarrow> 2 ^ natlog2 n \<le> n"
proof -
  assume n: "n > 0"
  from n have "of_nat (2 ^ natlog2 n) = 2 powr real_of_nat (nat \<lfloor>log 2 (real_of_nat n)\<rfloor>)"
    by (subst powr_realpow) (simp_all add: natlog2_def)
  also have "\<dots> = 2 powr of_int \<lfloor>log 2 (real_of_nat n)\<rfloor>" using n by simp
  also have "\<dots> \<le> 2 powr log 2 (real_of_nat n)" by (intro powr_mono) (linarith, simp_all)
  also have "\<dots> = of_nat n" using n by simp
  finally show ?thesis by simp
qed

lemma pow_natlog2_gt: "n > 0 \<Longrightarrow> 2 * 2 ^ natlog2 n > n"
  and pow_natlog2_ge: "n > 0 \<Longrightarrow> 2 * 2 ^ natlog2 n \<ge> n"
proof -
  assume n: "n > 0"
  from n have "of_nat n = 2 powr log 2 (real_of_nat n)" by simp
  also have "\<dots> < 2 powr (1 + of_int \<lfloor>log 2 (real_of_nat n)\<rfloor>)" 
    by (intro powr_less_mono) (linarith, simp_all)
  also from n have "\<dots> = 2 powr (1 + real_of_nat (nat \<lfloor>log 2 (real_of_nat n)\<rfloor>))" by simp
  also from n have "\<dots> = of_nat (2 * 2 ^ natlog2 n)"
    by (simp_all add: natlog2_def powr_real_of_int powr_add)
  finally show "2 * 2 ^ natlog2 n > n" by (rule of_nat_less_imp_less)
  thus "2 * 2 ^ natlog2 n \<ge> n" by simp
qed

lemma natlog2_eqI:
  assumes "n > 0" "2^k \<le> n" "n < 2 * 2^k"
  shows   "natlog2 n = k"
proof -
  from assms have "of_nat (2 ^ k) \<le> real_of_nat n"  by (subst of_nat_le_iff) simp_all
  hence "real_of_int (int k) \<le> log (of_nat 2) (real_of_nat n)"
    by (subst le_log_iff) (simp_all add: powr_realpow assms del: of_nat_le_iff)
  moreover from assms have "real_of_nat n < of_nat (2 ^ Suc k)" by (subst of_nat_less_iff) simp_all
  hence "log 2 (real_of_nat n) < of_nat k + 1"
    by (subst log_less_iff) (simp_all add: assms powr_realpow powr_add)
  ultimately have "\<lfloor>log 2 (real_of_nat n)\<rfloor> = of_nat k" by (intro floor_unique) simp_all
  with assms show ?thesis by (simp add: natlog2_def)
qed

end
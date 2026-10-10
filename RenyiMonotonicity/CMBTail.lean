module
public import RenyiMonotonicity.CMBDefinitions
public import RenyiMonotonicity.HarmonicSeries

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RenyiMonotonicity

theorem cmbGrid_le_one (N : ℕ) (hN : 0 < N) (k : Fin (N+1)) : cmbGrid N k ≤ 1 := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hk0 : (0:ℝ) ≤ k.val := Nat.cast_nonneg _
  have hkN : (k.val:ℝ) ≤ N := by exact_mod_cast (show k.val ≤ N by omega)
  have hl : -1 ≤ ((N:ℝ)-2*k.val)/N := (le_div_iff₀ hn).mpr (by nlinarith)
  have hr : ((N:ℝ)-2*k.val)/N ≤ 1 := (div_le_iff₀ hn).mpr (by nlinarith)
  unfold cmbGrid
  nlinarith

theorem one_le_cmbMoment (N : ℕ) (hN : 0 < N) (q : ℝ) (ell : ℕ) : 1 ≤ cmbMoment N q ell := by
  have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (N+1))))
    (f := fun k => (N.choose k.val:ℝ)^q*(cmbGrid N k)^ell)
    (fun i _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (cmbGrid_nonneg _ _) _))
    (Finset.mem_univ (0:Fin (N+1)))
  simpa only [Fin.val_zero,Nat.choose_zero_right,Nat.cast_one,Real.one_rpow,
    cmbGrid_zero N (by omega),one_pow,mul_one,cmbMoment] using hh

theorem cmbMoment_sub_succ (N : ℕ) (q : ℝ) (ell : ℕ) :
    cmbMoment N q ell-cmbMoment N q (ell+1) =
      ∑ k : Fin (N+1), (N.choose k.val:ℝ)^q*(cmbGrid N k)^ell*(1-cmbGrid N k) := by
  simp only [cmbMoment,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ]
  ring

theorem cmbMoment_sub_succ_nonneg (N : ℕ) (hN : 0 < N) (q : ℝ) (ell : ℕ) :
    0 ≤ cmbMoment N q ell-cmbMoment N q (ell+1) := by
  rw [cmbMoment_sub_succ]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (cmbGrid_nonneg _ _) _))
    (sub_nonneg.mpr (cmbGrid_le_one N hN k)))

/-- The non-endpoint part of the finite moment difference decays faster than a
linear factor. Nodes at squared distance one cancel exactly. -/
theorem tendsto_cmbMoment_difference_mul (N : ℕ) (hN : 0 < N) (q : ℝ) :
    Tendsto (fun ell : ℕ => (2*(ell:ℝ)+1)*(cmbMoment N q ell-cmbMoment N q (ell+1)))
      atTop (𝓝 0) := by
  have he (ell : ℕ) : (2*(ell:ℝ)+1)*(cmbMoment N q ell-cmbMoment N q (ell+1)) =
      ∑ k : Fin (N+1), (N.choose k.val:ℝ)^q*
        ((2*(ell:ℝ)+1)*(cmbGrid N k)^ell)*(1-cmbGrid N k) := by
    rw [cmbMoment_sub_succ,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  have ht (k : Fin (N+1)) : Tendsto (fun ell : ℕ => (N.choose k.val:ℝ)^q*
      ((2*(ell:ℝ)+1)*(cmbGrid N k)^ell)*(1-cmbGrid N k)) atTop (𝓝 0) := by
    by_cases hk : cmbGrid N k = 1
    · simp [hk]
    · have hk1 : cmbGrid N k < 1 := lt_of_le_of_ne (cmbGrid_le_one N hN k) hk
      have h₁ := tendsto_pow_const_mul_const_pow_of_lt_one 1 (cmbGrid_nonneg N k) hk1
      have h₀ := tendsto_pow_atTop_nhds_zero_of_lt_one (cmbGrid_nonneg N k) hk1
      have h := (((h₁.const_mul 2).add h₀).const_mul ((N.choose k.val:ℝ)^q)).mul_const (1-cmbGrid N k)
      convert h using 1
      · funext ell; simp only [pow_one]; ring
      · simp
  simpa using tendsto_finsetSum Finset.univ (fun k _ => ht k)

def cmbMomentRatio (N : ℕ) (q : ℝ) (ell : ℕ) : ℝ :=
  (2*(ell:ℝ)+1)*(cmbMoment N q ell / cmbMoment N q (ell+1)-1)

theorem cmbMomentRatio_eq (N : ℕ) (hN : 0 < N) (q : ℝ) (ell : ℕ) :
    cmbMomentRatio N q ell =
      ((2*(ell:ℝ)+1)*(cmbMoment N q ell-cmbMoment N q (ell+1))) / cmbMoment N q (ell+1) := by
  have hp := cmbMoment_pos N (by omega) q (ell+1)
  unfold cmbMomentRatio
  field_simp

theorem tendsto_cmbMomentRatio (N : ℕ) (hN : 0 < N) (q : ℝ) :
    Tendsto (cmbMomentRatio N q) atTop (𝓝 0) := by
  have hp (ell : ℕ) : 0 ≤ (2*(ell:ℝ)+1)*(cmbMoment N q ell-cmbMoment N q (ell+1)) :=
    mul_nonneg (by positivity) (cmbMoment_sub_succ_nonneg N hN q ell)
  apply squeeze_zero (fun ell => ?_) (fun ell => ?_) (tendsto_cmbMoment_difference_mul N hN q)
  · rw [cmbMomentRatio_eq N hN q ell]
    exact div_nonneg (hp ell) (cmbMoment_pos N (by omega) q (ell+1)).le
  · rw [cmbMomentRatio_eq N hN q ell]
    exact div_le_self (hp ell) (one_le_cmbMoment N hN q (ell+1))

/-- The even real binomial coefficients of a negative exponent are positive. -/
theorem real_choose_negative_even_pos (r : ℝ) (hr : r < 0) (ell : ℕ) :
    0 < Ring.choose r (2*ell) := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    have ho := real_choose_mul_succ r (2*ell)
    have he := real_choose_mul_succ r (2*ell+1)
    have hr0 : r-(2*ell:ℕ) < 0 := by push_cast; nlinarith
    have hr1 : r-(2*ell+1:ℕ) < 0 := by push_cast; nlinarith
    have hn0 : (0:ℝ) < (2*ell:ℕ)+1 := by positivity
    have hn1 : (0:ℝ) < (2*ell+1:ℕ)+1 := by positivity
    have hneg : Ring.choose r (2*ell+1) < 0 := by nlinarith [mul_neg_of_neg_of_pos hr0 ih]
    have hpos : 0 < Ring.choose r (2*ell+1+1) := by nlinarith [mul_pos_of_neg_of_neg hr1 hneg]
    convert hpos using 1

end RenyiMonotonicity

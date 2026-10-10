module
public import RenyiMonotonicity.MidpointFunctional
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RenyiMonotonicity

def resolventConstant (q : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ q t 1)⁻¹

theorem resolventConstant_pos {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < resolventConstant q := inv_pos.mpr (Real.integral_rpowIntegrand₀₁_one_pos hq)

/-- A weighted negative power, including a vanishing pair with zero weight,
represented by Mathlib's convergent positive-order integral. -/
theorem weighted_rpow_resolvent {q s d : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : 0 ≤ s) (hd : s = 0 → d = 0) :
    d * s ^ (q - 1) = resolventConstant q *
      ∫ t in Ioi (0 : ℝ), d / s * Real.rpowIntegrand₀₁ q t s := by
  rcases eq_or_lt_of_le hs with he | hs
  · have hs0 : s = 0 := he.symm
    simp [hs0, hd hs0]
  · rw [integral_const_mul, ← mul_assoc, mul_comm (resolventConstant q), mul_assoc,
      resolventConstant,
      ← Real.rpow_eq_const_mul_integral hq hs.le]
    rw [Real.rpow_sub_one hs.ne']
    ring

theorem weighted_resolvent_integrable {q s d : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : 0 ≤ s) :
    IntegrableOn (fun t => d / s * Real.rpowIntegrand₀₁ q t s) (Ioi (0 : ℝ)) :=
  (Real.integrableOn_rpowIntegrand₀₁_Ioi hq hs).const_mul _

theorem weighted_resolvent_integrand {q s d t : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : 0 ≤ s) (hd : s = 0 → d = 0) (ht : 0 < t) :
    d / s * Real.rpowIntegrand₀₁ q t s = t ^ (q - 1) * (d / (t + s)) := by
  rw [Real.rpowIntegrand₀₁_eq_pow_div hq ht.le hs]
  rcases eq_or_lt_of_le hs with he | hs
  · have hs0 : s = 0 := he.symm
    simp [hs0, hd hs0]
  · field_simp

/-- A nonnegative finite resolvent sum implies the corresponding negative-power
sum is nonnegative. Integrability and every zero-pair contribution are proved. -/
theorem power_sum_nonneg_of_resolvent {m : ℕ} {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (s d : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i) (hd : ∀ i, s i = 0 → d i = 0)
    (hr : ∀ t : ℝ, 0 < t → 0 ≤ ∑ i, d i / (t + s i)) :
    0 ≤ ∑ i, d i * (s i) ^ (q - 1) := by
  have hrepr : (∑ i, d i * (s i) ^ (q - 1)) = resolventConstant q *
      ∫ t in Ioi (0 : ℝ), ∑ i, d i / s i * Real.rpowIntegrand₀₁ q t (s i) := by
    simp_rw [weighted_rpow_resolvent hq (hs _) (hd _)]
    rw [← Finset.mul_sum, integral_finsetSum]
    intro i _
    exact weighted_resolvent_integrable hq (hs i)
  rw [hrepr]
  apply mul_nonneg (resolventConstant_pos hq).le
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  simp_rw [weighted_resolvent_integrand hq (hs _) (hd _) ht]
  rw [← Finset.mul_sum]
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (hr t ht)

end RenyiMonotonicity

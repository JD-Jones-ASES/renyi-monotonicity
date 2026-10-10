module

public import RenyiMonotonicity.ContactCurvature
public import RenyiMonotonicity.CubicIdentities

/-! First mass-moment annihilation derived from actual coin stationarity. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace RenyiMonotonicity

/-- Differentiating the generating polynomial counts successful coins exactly. -/
theorem bernoulliMass_weighted_omit_shift {n : ℕ} (p : Fin (n + 1) → ℝ) (k : ℕ) :
    ∑ i, p i * bernoulliMass (omitCoin p i) ((k : ℤ) - 1) =
      (k : ℝ) * bernoulliMass p (k : ℤ) := by
  cases k with
  | zero => simp
  | succ k =>
      have h := congrArg (fun P : Polynomial ℝ => P.coeff k) (derivative_bernoulliPolynomial p)
      simp only [Polynomial.coeff_derivative, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at h
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega]
      simp only [bernoulliMass_natCast]
      simpa only [mul_comm, Nat.cast_add, Nat.cast_one] using h.symm

/-- The common odds tangent is exactly centered multiplication by the count. -/
theorem bernoulliMass_odds_tangent {n : ℕ} (p : Fin (n + 1) → ℝ) (k : ℕ) :
    ∑ i, p i * (1 - p i) *
      (bernoulliMass (omitCoin p i) ((k : ℤ) - 1) - bernoulliMass (omitCoin p i) (k : ℤ)) =
      ((k : ℝ) - ∑ i, p i) * bernoulliMass p (k : ℤ) := by
  have he (i : Fin (n + 1)) : p i * (1 - p i) *
      (bernoulliMass (omitCoin p i) ((k : ℤ) - 1) - bernoulliMass (omitCoin p i) (k : ℤ)) =
      p i * bernoulliMass (omitCoin p i) ((k : ℤ) - 1) - p i * bernoulliMass p (k : ℤ) := by
    have h := bernoulliMass_update p i (p i) (k : ℤ)
    rw [Function.update_eq_self] at h
    rw [h]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, bernoulliMass_weighted_omit_shift, ← Finset.sum_mul]
  ring

/-- Weighted coin-coordinate derivatives equal the centered first mass moment. -/
theorem midpoint_odds_direction_identity {n : ℕ} (q : ℝ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) :
    (∑ i, p i * (1 - p i) * deriv (fun t => midpointFunctional q (Function.update p i t)) (p i)) =
      massGradientPairing q (n + 1) (bernoulliMass p) (fun k => (k : ℝ) * bernoulliMass p k) -
      (∑ i, p i) * massGradientPairing q (n + 1) (bernoulliMass p) (bernoulliMass p) := by
  simp_rw [(hasDerivAt_midpointFunctional_update_gradient q p hp hp₁ _).deriv]
  unfold massGradientPairing
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hh := bernoulliMass_odds_tangent p k.val
  rw [show (∑ i, p i * (1 - p i) *
      ((bernoulliMass (omitCoin p i) ((k.val : ℤ) - 1) - bernoulliMass (omitCoin p i) (k.val : ℤ)) *
        massGradientEntry q (bernoulliMass p ((k.val : ℤ) - 1)) (bernoulliMass p (k.val : ℤ))
          (bernoulliMass p ((k.val : ℤ) + 1)))) =
      (∑ i, p i * (1 - p i) *
        (bernoulliMass (omitCoin p i) ((k.val : ℤ) - 1) - bernoulliMass (omitCoin p i) (k.val : ℤ))) *
        massGradientEntry q (bernoulliMass p ((k.val : ℤ) - 1)) (bernoulliMass p (k.val : ℤ))
          (bernoulliMass p ((k.val : ℤ) + 1)) by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring]
  rw [hh]
  push_cast
  ring

/-- At a zero contact with stationary coins, the first weighted mass moment
vanishes. No separate escort stationarity certificate is assumed. -/
theorem firstMassMoment_eq_zero_of_stationary {n : ℕ} (q : ℝ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) (hD : midpointFunctional q p = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) = 0) :
    massGradientPairing q (n + 1) (bernoulliMass p) (fun k => (k : ℝ) * bernoulliMass p k) = 0 := by
  have he := midpoint_odds_direction_identity q p hp hp₁
  simp only [hstat, mul_zero, Finset.sum_const_zero] at he
  rw [massGradientPairing_euler q (n + 1) _ (bernoulliMass_outer_left p)
    (bernoulliMass_outer_right p) (edgeSum_pos p hp hp₁), finiteMassFunctional_bernoulliMass,
    hD, mul_zero, mul_zero, sub_zero] at he
  exact he.symm

end RenyiMonotonicity

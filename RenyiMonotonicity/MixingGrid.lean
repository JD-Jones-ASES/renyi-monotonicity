module

public import RenyiMonotonicity.CubicIdentities

@[expose] public section

open scoped BigOperators

namespace RenyiMonotonicity

/-- Hillion--Johnson's mixing coefficient on the integer-extended actual count law. -/
noncomputable def mixingCoefficient {n : ℕ} (p : Fin n → ℝ) (k : ℤ) : ℝ :=
  bernoulliMass p (k - 1) / (bernoulliMass p (k - 1) + bernoulliMass p k)

/-- A single mixing-grid gap, before any log-concavity sign is invoked. -/
theorem mixing_gap_algebra (a b c : ℝ) (hab : a + b ≠ 0) (hbc : b + c ≠ 0) :
    b / (b + c) - a / (a + b) = (b ^ 2 - a * c) / ((a + b) * (b + c)) := by
  field_simp
  ring

/-- The exact numerator of the difference of two consecutive mixing-grid gaps. -/
theorem mixing_curvature_algebra (a b c d : ℝ)
    (hab : a + b ≠ 0) (hbc : b + c ≠ 0) (hcd : c + d ≠ 0) :
    (b / (b + c) - a / (a + b)) - (c / (c + d) - b / (b + c)) =
      ((b ^ 2 * c + a * b * d - 2 * a * c ^ 2) -
        (b * c ^ 2 + a * c * d - 2 * b ^ 2 * d)) /
        ((a + b) * (b + c) * (c + d)) := by
  field_simp
  ring

/-- Positive coin parameters give every mass on the full count support strictly positive. -/
theorem bernoulliMass_pos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : ℤ)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) : 0 < bernoulliMass p k := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  rw [bernoulliMass_natCast, coeff_bernoulliPolynomial_pos_iff p
    (fun i => (hp i).le) hp1]
  have hcount : positiveCoinCount p = n := by
    simp [positiveCoinCount, hp]
  rw [hcount]
  omega

/-- The left outer mixing coefficient is exactly zero. -/
@[simp] theorem mixingCoefficient_zero {n : ℕ} (p : Fin n → ℝ) :
    mixingCoefficient p 0 = 0 := by simp [mixingCoefficient]

/-- The right outer mixing coefficient is exactly one for a positive full law. -/
theorem mixingCoefficient_outer_right {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    mixingCoefficient p (n + 1) = 1 := by
  have hpos := bernoulliMass_pos p hp hp1 n (by omega) (by omega)
  simp only [mixingCoefficient, add_sub_cancel_right, bernoulliMass_outer_right, add_zero]
  exact div_self (ne_of_gt hpos)

/-- Actual-law curvature identity. Strict minor positivity, not a hidden certificate,
is the remaining mathematical input needed to turn this equality into concavity. -/
theorem mixingCoefficient_curvature_identity {n : ℕ} (p : Fin (n + 1) → ℝ)
    (k : ℤ)
    (h₀ : bernoulliMass p (k - 1) + bernoulliMass p k ≠ 0)
    (h₁ : bernoulliMass p k + bernoulliMass p (k + 1) ≠ 0)
    (h₂ : bernoulliMass p (k + 1) + bernoulliMass p (k + 2) ≠ 0) :
    (mixingCoefficient p (k + 1) - mixingCoefficient p k) -
      (mixingCoefficient p (k + 2) - mixingCoefficient p (k + 1)) =
      (∑ i, p i * (1 - p i) * (1 - 2 * p i) * omittedToeplitzCubic p i k) /
        ((bernoulliMass p (k - 1) + bernoulliMass p k) *
          (bernoulliMass p k + bernoulliMass p (k + 1)) *
          (bernoulliMass p (k + 1) + bernoulliMass p (k + 2))) := by
  have e₁ : k + 1 - 1 = k := by omega
  have e₂ : k + 2 - 1 = k + 1 := by omega
  simp only [mixingCoefficient, e₁, e₂]
  rw [mixing_curvature_algebra _ _ _ _ h₀ h₁ h₂,
    bernoulli_cubic_left, bernoulli_cubic_right, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The curvature identity on the entire actual edge grid has no denominator assumptions:
positive Bernoulli parameters establish them, including both exterior edges. -/
theorem mixingCoefficient_curvature_identity_of_pos {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : ℤ)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    (mixingCoefficient p (k + 1) - mixingCoefficient p k) -
      (mixingCoefficient p (k + 2) - mixingCoefficient p (k + 1)) =
      (∑ i, p i * (1 - p i) * (1 - 2 * p i) * omittedToeplitzCubic p i k) /
        ((bernoulliMass p (k - 1) + bernoulliMass p k) *
          (bernoulliMass p k + bernoulliMass p (k + 1)) *
          (bernoulliMass p (k + 1) + bernoulliMass p (k + 2))) := by
  have hb := bernoulliMass_pos p hp hp1 k hk0 (by omega)
  have hc := bernoulliMass_pos p hp hp1 (k + 1) (by omega) (by omega)
  have ha := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp1 i).le) (k - 1)
  have hd := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp1 i).le) (k + 2)
  apply mixingCoefficient_curvature_identity
  · linarith
  · linarith
  · linarith

/-- At the left boundary the omitted three-row minor is the positive endpoint cube. -/
@[simp] theorem omittedToeplitzCubic_zero {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    omittedToeplitzCubic p i 0 = bernoulliMass (omitCoin p i) 0 ^ 3 := by
  simp [omittedToeplitzCubic, toeplitzCubic, bernoulliMass]

/-- Strict positivity of the actual left omitted minor, even for a zero-coin omitted law. -/
theorem omittedToeplitzCubic_zero_pos {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (i : Fin (n + 1)) :
    0 < omittedToeplitzCubic p i 0 := by
  rw [omittedToeplitzCubic_zero]
  apply pow_pos
  exact bernoulliMass_pos (omitCoin p i) (fun j => hp _) (fun j => hp1 _)
    0 (by omega) (by omega)

/-- Counts above the full dimension have zero mass, independently of parameter signs. -/
theorem bernoulliMass_eq_zero_above {n : ℕ} (p : Fin n → ℝ) (k : ℤ) (hk : n < k) :
    bernoulliMass p k = 0 := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  rw [bernoulliMass_natCast]
  exact coeff_bernoulliPolynomial_eq_zero p k (by omega)

/-- The right omitted minor is also exactly the endpoint cube. -/
theorem omittedToeplitzCubic_outer_right {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    omittedToeplitzCubic p i n = bernoulliMass (omitCoin p i) n ^ 3 := by
  have h₁ := bernoulliMass_eq_zero_above (omitCoin p i) (n + 1) (by omega)
  have h₂ := bernoulliMass_eq_zero_above (omitCoin p i) (n + 2) (by omega)
  simp [omittedToeplitzCubic, toeplitzCubic, h₁, h₂]

/-- Strict positivity at the right omitted-law boundary. -/
theorem omittedToeplitzCubic_outer_right_pos {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (i : Fin (n + 1)) :
    0 < omittedToeplitzCubic p i n := by
  rw [omittedToeplitzCubic_outer_right]
  apply pow_pos
  exact bernoulliMass_pos (omitCoin p i) (fun j => hp _) (fun j => hp1 _)
    n (by omega) (by omega)

end RenyiMonotonicity

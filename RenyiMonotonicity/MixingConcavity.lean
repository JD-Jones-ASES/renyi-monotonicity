module

public import RenyiMonotonicity.MixingGrid
public import RenyiMonotonicity.ToeplitzMinors

@[expose] public section

open scoped BigOperators

namespace RenyiMonotonicity

/-- Every step of the actual mixing grid is strictly increasing, including
both outer edges. -/
theorem mixingCoefficient_gap_pos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) (k : ℤ)
    (hk₀ : 0 ≤ k) (hkn : k ≤ n) :
    0 < mixingCoefficient p (k + 1) - mixingCoefficient p k := by
  have ha := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp₁ i).le) (k - 1)
  have hb := bernoulliMass_pos p hp hp₁ k hk₀ hkn
  have hc := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp₁ i).le) (k + 1)
  have hab : 0 < bernoulliMass p (k - 1) + bernoulliMass p k := by positivity
  have hbc : 0 < bernoulliMass p k + bernoulliMass p (k + 1) := by positivity
  simp only [mixingCoefficient, add_sub_cancel_right]
  rw [mixing_gap_algebra _ _ _ (ne_of_gt hab) (ne_of_gt hbc)]
  exact div_pos (sub_pos.mpr (bernoulliMass_strict_logconcave p hp hp₁ k hk₀ hkn))
    (mul_pos hab hbc)

private theorem mixing_denominator_pos {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) (k : ℤ)
    (hk₀ : 0 ≤ k) (hkn : k ≤ n) :
    0 < (bernoulliMass p (k - 1) + bernoulliMass p k) *
      (bernoulliMass p k + bernoulliMass p (k + 1)) *
      (bernoulliMass p (k + 1) + bernoulliMass p (k + 2)) := by
  have ha := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp₁ i).le) (k - 1)
  have hb := bernoulliMass_pos p hp hp₁ k hk₀ (by omega)
  have hc := bernoulliMass_pos p hp hp₁ (k + 1) (by omega) (by omega)
  have hd := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp₁ i).le) (k + 2)
  positivity

/-- Hillion--Johnson mixing-grid concavity for the actual half-cube law. -/
theorem mixingCoefficient_gap_antitone_step {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) (k : ℤ)
    (hk₀ : 0 ≤ k) (hkn : k ≤ n) :
    mixingCoefficient p (k + 2) - mixingCoefficient p (k + 1) ≤
      mixingCoefficient p (k + 1) - mixingCoefficient p k := by
  have hp₁ : ∀ i, p i < 1 := by intro i; linarith [hpHalf i]
  apply sub_nonneg.mp
  rw [mixingCoefficient_curvature_identity_of_pos p hp hp₁ k hk₀ hkn]
  apply div_nonneg _ (mixing_denominator_pos p hp hp₁ k hk₀ hkn).le
  apply Finset.sum_nonneg
  intro i _
  have h₁ : 0 ≤ 1 - p i := sub_nonneg.mpr (hp₁ i).le
  have h₂ : 0 ≤ 1 - 2 * p i := by linarith [hpHalf i]
  have hΔ := omittedToeplitzCubic_pos p hp hp₁ i k hk₀ hkn
  exact mul_nonneg (mul_nonneg (mul_nonneg (hp i).le h₁) h₂) hΔ.le

/-- A single biased coin makes every mixing-grid second difference strictly
negative; the strict omitted minor is proved from the actual product law. -/
theorem mixingCoefficient_gap_strict_antitone_step {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (hbiased : ∃ i, p i < 1 / 2) (k : ℤ) (hk₀ : 0 ≤ k) (hkn : k ≤ n) :
    mixingCoefficient p (k + 2) - mixingCoefficient p (k + 1) <
      mixingCoefficient p (k + 1) - mixingCoefficient p k := by
  have hp₁ : ∀ i, p i < 1 := by intro i; linarith [hpHalf i]
  apply sub_pos.mp
  rw [mixingCoefficient_curvature_identity_of_pos p hp hp₁ k hk₀ hkn]
  apply div_pos _ (mixing_denominator_pos p hp hp₁ k hk₀ hkn)
  apply Finset.sum_pos'
  · intro i _
    have h₁ : 0 ≤ 1 - p i := sub_nonneg.mpr (hp₁ i).le
    have h₂ : 0 ≤ 1 - 2 * p i := by linarith [hpHalf i]
    have hΔ := omittedToeplitzCubic_pos p hp hp₁ i k hk₀ hkn
    exact mul_nonneg (mul_nonneg (mul_nonneg (hp i).le h₁) h₂) hΔ.le
  · obtain ⟨i, hi⟩ := hbiased
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have h₁ : 0 < 1 - p i := sub_pos.mpr (hp₁ i)
    have h₂ : 0 < 1 - 2 * p i := by linarith
    have hΔ := omittedToeplitzCubic_pos p hp hp₁ i k hk₀ hkn
    exact mul_pos (mul_pos (mul_pos (hp i) h₁) h₂) hΔ

/-- Equality in any mixing-grid second difference occurs precisely at the fair
binomial vector. -/
theorem mixingCoefficient_gap_eq_iff_all_half {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) (k : ℤ)
    (hk₀ : 0 ≤ k) (hkn : k ≤ n) :
    (mixingCoefficient p (k + 2) - mixingCoefficient p (k + 1) =
      mixingCoefficient p (k + 1) - mixingCoefficient p k) ↔ ∀ i, p i = 1 / 2 := by
  constructor
  · intro heq
    by_contra hn
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    have hb : p i < 1 / 2 := lt_of_le_of_ne (hpHalf i) hi
    have hs := mixingCoefficient_gap_strict_antitone_step p hp hpHalf ⟨i, hb⟩ k hk₀ hkn
    linarith
  · intro hf
    have hp₁ : ∀ i, p i < 1 := by intro i; linarith [hpHalf i]
    have h := mixingCoefficient_curvature_identity_of_pos p hp hp₁ k hk₀ hkn
    simp only [hf] at h
    norm_num at h
    linarith

end RenyiMonotonicity

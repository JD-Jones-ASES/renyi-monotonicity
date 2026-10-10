module

public import RenyiMonotonicity.ScalarGradient
public import RenyiMonotonicity.MixingConcavity

/-! The strict cubic gate and increasing threshold gaps for the actual mass gradient. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

/-- The exact adjacent curvature-ratio identity (G10). -/
theorem tripleKappa_step (a b c d : ℝ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hJ : a - 2*b + c ≠ 0) (hJ' : b - 2*c + d ≠ 0) :
    tripleKappa b c d - tripleKappa a b c =
      (c-b) * ((b^2*c+a*b*d-2*a*c^2) + (b*c^2+a*c*d-2*b^2*d)) /
        (b*c*(a-2*b+c)*(b-2*c+d)) := by
  unfold tripleKappa
  rw [div_sub_div _ _ (mul_ne_zero hc hJ') (mul_ne_zero hb hJ)]
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hc hJ') (mul_ne_zero hb hJ))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hJ) hJ')).mpr
  ring

/-- Strict positivity of the sum of the two actual Hillion--Johnson cubics. -/
theorem bernoulli_cubic_sum_pos {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : ℤ) (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    0 < (bernoulliMass p k ^ 2 * bernoulliMass p (k+1) +
      bernoulliMass p (k-1) * bernoulliMass p k * bernoulliMass p (k+2) -
      2 * bernoulliMass p (k-1) * bernoulliMass p (k+1)^2) +
      (bernoulliMass p k * bernoulliMass p (k+1)^2 +
      bernoulliMass p (k-1) * bernoulliMass p (k+1) * bernoulliMass p (k+2) -
      2 * bernoulliMass p k^2 * bernoulliMass p (k+2)) := by
  rw [bernoulli_cubic_left, bernoulli_cubic_right]
  apply add_pos
  · apply Finset.sum_pos
    · intro i _
      exact mul_pos (mul_pos (hp i) (sq_pos_of_pos (sub_pos.mpr (hp1 i))))
        (omittedToeplitzCubic_pos p hp hp1 i k hk0 hkn)
    · exact Finset.univ_nonempty
  · apply Finset.sum_pos
    · intro i _
      exact mul_pos (mul_pos (sq_pos_of_pos (hp i)) (sub_pos.mpr (hp1 i)))
        (omittedToeplitzCubic_pos p hp hp1 i k hk0 hkn)
    · exact Finset.univ_nonempty

/-- The normalized left coordinate strictly decreases under strict log-concavity. -/
theorem gradientCoordinate_step_lt {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (hlog : a*c < b^2) : gradientCoordinate b c < gradientCoordinate a b := by
  unfold gradientCoordinate
  apply (div_lt_div_iff₀ (by linarith : 0 < c+b) (by linarith : 0 < b+a)).mpr
  nlinarith

/-- The actual mass-gradient kernel, with integer zero extension at both outer neighbours. -/
def bernoulliMassGradient {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (k : ℤ) : ℝ :=
  massGradientEntry q (bernoulliMass p (k-1)) (bernoulliMass p k) (bernoulliMass p (k+1))

/-- The threshold comparison for an actual three-mass entry. -/
def bernoulliGradientThresholdGap {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (k : ℤ) : ℝ :=
  tripleKappa (bernoulliMass p (k-1)) (bernoulliMass p k) (bernoulliMass p (k+1)) -
    scalarKappa q (gradientCoordinate (bernoulliMass p (k-1)) (bernoulliMass p k))

/-- Consecutive actual curvature ratios strictly increase on an increasing positive-curvature block. -/
theorem bernoulli_tripleKappa_step_lt {n : ℕ} (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : ℤ) (hk0 : 0 ≤ k) (hkn : k ≤ n)
    (hinc : bernoulliMass p k < bernoulliMass p (k+1))
    (hJ : 0 < bernoulliMass p (k-1) - 2*bernoulliMass p k + bernoulliMass p (k+1))
    (hJ' : 0 < bernoulliMass p k - 2*bernoulliMass p (k+1) + bernoulliMass p (k+2)) :
    tripleKappa (bernoulliMass p (k-1)) (bernoulliMass p k) (bernoulliMass p (k+1)) <
      tripleKappa (bernoulliMass p k) (bernoulliMass p (k+1)) (bernoulliMass p (k+2)) := by
  have hb := bernoulliMass_pos p hp hp1 k hk0 (by omega)
  have hc := bernoulliMass_pos p hp hp1 (k+1) (by omega) (by omega)
  have H := tripleKappa_step (bernoulliMass p (k-1)) (bernoulliMass p k)
    (bernoulliMass p (k+1)) (bernoulliMass p (k+2)) hb.ne' hc.ne' hJ.ne' hJ'.ne'
  have hp' := div_pos (mul_pos (sub_pos.mpr hinc) (bernoulli_cubic_sum_pos p hp hp1 k hk0 hkn))
    (mul_pos (mul_pos (mul_pos hb hc) hJ) hJ')
  linarith

/-- The actual threshold gaps strictly increase across every adjacent increasing
positive-curvature pair; every structural inequality is derived from the Bernoulli product. -/
theorem bernoulliGradientThresholdGap_step_lt {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (k : ℤ) (hk0 : 0 ≤ k) (hkn : k ≤ n)
    (hinc₀ : bernoulliMass p (k-1) < bernoulliMass p k)
    (hinc₁ : bernoulliMass p k < bernoulliMass p (k+1))
    (hJ : 0 < bernoulliMass p (k-1) - 2*bernoulliMass p k + bernoulliMass p (k+1))
    (hJ' : 0 < bernoulliMass p k - 2*bernoulliMass p (k+1) + bernoulliMass p (k+2)) :
    bernoulliGradientThresholdGap q p k < bernoulliGradientThresholdGap q p (k+1) := by
  have ha := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp1 i).le) (k-1)
  have hb := bernoulliMass_pos p hp hp1 k hk0 (by omega)
  have hc := bernoulliMass_pos p hp hp1 (k+1) (by omega) (by omega)
  have hlog := bernoulliMass_strict_logconcave p hp hp1 k hk0 (by omega)
  have hx := gradientCoordinate_step_lt ha hb hc hlog
  have hκ := scalarKappa_strictMonoOn hq0 hq1 (gradientCoordinate_mem hb.le hinc₁)
    (gradientCoordinate_mem ha hinc₀) hx
  have hT := bernoulli_tripleKappa_step_lt p hp hp1 k hk0 hkn hinc₁ hJ hJ'
  unfold bernoulliGradientThresholdGap
  rw [show k+1-1=k by omega, show k+1+1=k+2 by omega]
  linarith

end RenyiMonotonicity

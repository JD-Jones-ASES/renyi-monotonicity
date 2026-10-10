module

public import Mathlib

/-! Elementary finite-interval single-crossing calculus used in the scalar threshold. -/

@[expose] public section
noncomputable section
open Set

namespace RenyiMonotonicity

/-- A quadratic with negative constant term and nonnegative leading coefficient
has at most one positive zero, with the indicated strict sign orientation. -/
lemma thresholdQuadratic_before {a b c u t : ℝ} (ha : a < 0) (hb : 0 ≤ b)
    (ht : 0 < t) (htu : t < u) (hu : a * (1 + c * u) + b * u^2 ≤ 0) :
    a * (1 + c * t) + b * t^2 < 0 := by
  have hp : 0 < (u - t) * (-a + b * t * u) := by
    apply mul_pos (sub_pos.mpr htu)
    have hu0 : 0 < u := ht.trans htu
    nlinarith [mul_nonneg (mul_nonneg hb ht.le) hu0.le]
  have hmul := mul_nonpos_of_nonpos_of_nonneg hu ht.le
  nlinarith

lemma thresholdQuadratic_after {a b c u t : ℝ} (ha : a < 0) (hb : 0 ≤ b)
    (hu : 0 < u) (hut : u < t) (hQ : 0 ≤ a * (1 + c * u) + b * u^2) :
    0 < a * (1 + c * t) + b * t^2 := by
  have hp : 0 < (t - u) * (-a + b * t * u) := by
    apply mul_pos (sub_pos.mpr hut)
    have ht0 : 0 < t := hu.trans hut
    nlinarith [mul_nonneg (mul_nonneg hb ht0.le) hu.le]
  have hmul := mul_nonneg hQ (show 0 ≤ t by linarith)
  nlinarith

/-- A logarithmic ratio whose derivative has the quadratic sign can only cross zero upwards. -/
theorem thresholdLog_crossing {g : ℝ → ℝ} {a b c : ℝ}
    (ha : a < 0) (hb : 0 ≤ b) (hg : ContinuousOn g (Icc 0 1)) (hg0 : g 0 = 0)
    (hdneg : ∀ t ∈ Ioo (0 : ℝ) 1, a * (1 + c * t) + b * t^2 < 0 → deriv g t < 0)
    (hdpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < a * (1 + c * t) + b * t^2 → 0 < deriv g t)
    {u t : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) (hut : u < t)
    (hgu : 0 ≤ g u) : 0 < g t := by
  have hQu : 0 < a * (1 + c * u) + b * u^2 := by
    by_contra h
    have hQ := le_of_not_gt h
    have hm : StrictAntiOn g (Icc 0 u) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hg.mono (by intro z hz; exact ⟨hz.1, hz.2.trans hu.2⟩))
      intro z hz
      rw [interior_Icc] at hz
      exact hdneg z ⟨hz.1, hz.2.trans_le hu.2⟩ (thresholdQuadratic_before ha hb hz.1 hz.2 hQ)
    have hlt := hm (show (0 : ℝ) ∈ Icc 0 u by exact ⟨le_rfl, hu.1.le⟩)
      (show u ∈ Icc 0 u by exact ⟨hu.1.le, le_rfl⟩) hu.1
    rw [hg0] at hlt
    linarith
  have hm : StrictMonoOn g (Icc u t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hg.mono (by intro z hz; exact ⟨hu.1.le.trans hz.1, hz.2.trans ht.2⟩))
    intro z hz
    rw [interior_Icc] at hz
    exact hdpos z ⟨hu.1.trans hz.1, hz.2.trans_le ht.2⟩ (thresholdQuadratic_after ha hb hu.1 hz.1 hQu.le)
  exact lt_of_le_of_lt hgu (hm ⟨le_rfl, hut.le⟩ ⟨hut.le, le_rfl⟩ hut)

/-- A primitive with derivative opposite to a single-crossing logarithmic ratio
crosses zero strictly downwards and remains negative thereafter. -/
theorem thresholdPrimitive_crossing {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hf0 : f 0 = 0)
    (hcross : ∀ {u t : ℝ}, u ∈ Ioc (0 : ℝ) 1 → t ∈ Ioc (0 : ℝ) 1 → u < t → 0 ≤ g u → 0 < g t)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, g t < 0 → 0 < deriv f t)
    (hneg : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g t → deriv f t < 0)
    {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (hfu : f u = 0) :
    0 < g u ∧ ∀ t ∈ Ioc (0 : ℝ) 1, u < t → f t < 0 := by
  have hgu : 0 < g u := by
    by_contra h
    have hgu := le_of_not_gt h
    have hgneg : ∀ z ∈ Ioo (0 : ℝ) u, g z < 0 := by
      intro z hz
      by_contra hn
      have hh := hcross ⟨hz.1, hz.2.le.trans hu.2⟩ hu hz.2 (le_of_not_gt hn)
      linarith
    have hm : StrictMonoOn f (Icc 0 u) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hf.mono (by intro z hz; exact ⟨hz.1, hz.2.trans hu.2⟩))
      intro z hz
      rw [interior_Icc] at hz
      exact hpos z ⟨hz.1, hz.2.trans_le hu.2⟩ (hgneg z hz)
    have hh := hm ⟨le_rfl, hu.1.le⟩ ⟨hu.1.le, le_rfl⟩ hu.1
    rw [hf0, hfu] at hh
    exact lt_irrefl _ hh
  refine ⟨hgu, ?_⟩
  intro t ht hut
  have hm : StrictAntiOn f (Icc u t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hf.mono (by intro z hz; exact ⟨hu.1.le.trans hz.1, hz.2.trans ht.2⟩))
    intro z hz
    rw [interior_Icc] at hz
    exact hneg z ⟨hu.1.trans hz.1, hz.2.trans_le ht.2⟩
      (hcross hu ⟨hu.1.trans hz.1, hz.2.le.trans ht.2⟩ hz.1 hgu.le)
  simpa [hfu] using hm ⟨le_rfl, hut.le⟩ ⟨hut.le, le_rfl⟩ hut

end RenyiMonotonicity

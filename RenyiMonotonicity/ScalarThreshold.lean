module

public import Mathlib

/-! The finite scalar equation underlying the mass-gradient threshold.
This module defines the actual analytic function, proves its derivatives, and constructs
its unique reflected root. No threshold property is assumed as an extra hypothesis. -/

@[expose] public section
noncomputable section
open Set

namespace RenyiMonotonicity

/-- The finite scalar function `H` from the mass-gradient reduction. -/
def scalarH (q r : ℝ) : ℝ := (1 - (1 - q) * r) * (1 + r) ^ (1 - q)

/-- The exact derivative of the finite scalar function away from its left endpoint. -/
theorem hasDerivAt_scalarH (q r : ℝ) (hr : -1 < r) :
    HasDerivAt (scalarH q) (-(1 - q) * (2 - q) * r * (1 + r) ^ (-q)) r := by
  have hp : 0 < 1 + r := by linarith
  have he : (1 + r) ^ (1 - q) = (1 + r) ^ (-q) * (1 + r) := by
    rw [show 1 - q = -q + 1 by ring, Real.rpow_add hp, Real.rpow_one]
  have h₁ := (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).const_mul (1 - q))
  have h₂ := ((hasDerivAt_id r).const_add 1).rpow_const (p := 1 - q) (Or.inl hp.ne')
  convert h₁.mul h₂ using 1
  · rfl
  · simp only [id_eq, Pi.sub_apply, one_mul, zero_sub, mul_one]
    rw [show 1 - q - 1 = -q by ring, he]
    ring

lemma continuous_scalarH {q : ℝ} (hq : q < 1) : Continuous (scalarH q) := by
  unfold scalarH
  apply Continuous.mul (by fun_prop)
  exact (Real.continuous_rpow_const (by linarith : 0 ≤ 1 - q)).comp (by fun_prop)

@[simp] lemma scalarH_zero (q : ℝ) : scalarH q 0 = 1 := by simp [scalarH]

lemma scalarH_neg_one {q : ℝ} (hq : q < 1) : scalarH q (-1) = 0 := by
  simp [scalarH, Real.zero_rpow (by linarith : 1 - q ≠ 0)]

/-- `H` is strictly increasing from zero to one on its negative branch. -/
theorem scalarH_strictMonoOn_negative {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    StrictMonoOn (scalarH q) (Icc (-1) 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_scalarH hq1).continuousOn
  intro r hr
  rw [interior_Icc] at hr
  rw [(hasDerivAt_scalarH q r hr.1).deriv]
  have hc : 0 < (1 - q) * (2 - q) := mul_pos (by linarith) (by linarith)
  have hp : 0 < (1 + r) ^ (-q) := Real.rpow_pos_of_pos (by linarith [hr.1]) _
  nlinarith [mul_pos hc (neg_pos.mpr hr.2), mul_pos (mul_pos hc (neg_pos.mpr hr.2)) hp]

/-- `H` is strictly decreasing on its positive branch. -/
theorem scalarH_strictAntiOn_positive {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    StrictAntiOn (scalarH q) (Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_scalarH hq1).continuousOn
  intro r hr
  rw [interior_Icc] at hr
  rw [(hasDerivAt_scalarH q r (by linarith [hr.1])).deriv]
  have hc : 0 < (1 - q) * (2 - q) := mul_pos (by linarith) (by linarith)
  have hp : 0 < (1 + r) ^ (-q) := Real.rpow_pos_of_pos (by linarith [hr.1]) _
  nlinarith [mul_pos (mul_pos hc hr.1) hp]

lemma scalarH_pos {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : x ∈ Icc 0 1) :
    0 < scalarH q x := by
  have hf : 0 < 1 - (1 - q) * x := by
    have := mul_le_mul_of_nonneg_left hx.2 (by linarith : 0 ≤ 1 - q)
    linarith
  exact mul_pos hf (Real.rpow_pos_of_pos (by linarith [hx.1]) _)

lemma scalarH_lt_one {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : x ∈ Ioc 0 1) :
    scalarH q x < 1 := by
  have h := scalarH_strictAntiOn_positive hq0 hq1 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    ⟨hx.1.le, hx.2⟩ hx.1
  simpa using h

/-- Existence and uniqueness of the actual reflected root, including `x = 1`. -/
theorem existsUnique_scalarThresholdY {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc 0 1) : ∃! y, y ∈ Ioo (0 : ℝ) 1 ∧ scalarH q (-y) = scalarH q x := by
  have hh0 := scalarH_pos hq0 hq1 ⟨hx.1.le, hx.2⟩
  have hh1 := scalarH_lt_one hq0 hq1 hx
  have hmem : scalarH q x ∈ Icc (scalarH q (-1)) (scalarH q 0) := by
    rw [scalarH_neg_one hq1, scalarH_zero]
    exact ⟨hh0.le, hh1.le⟩
  obtain ⟨z, hz, heq⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 0)
    (continuous_scalarH hq1).continuousOn hmem
  have hz₁ : -1 < z := by
    apply lt_of_le_of_ne hz.1
    intro he
    subst z
    rw [scalarH_neg_one hq1] at heq
    linarith
  have hz₂ : z < 0 := by
    apply lt_of_le_of_ne hz.2
    intro he
    subst z
    rw [scalarH_zero] at heq
    linarith
  refine ⟨-z, ⟨⟨by linarith, by linarith⟩, by simpa using heq⟩, ?_⟩
  intro y hy
  have hn : -y = z := (scalarH_strictMonoOn_negative hq0 hq1).injOn
    ⟨by linarith [hy.1.2], by linarith [hy.1.1]⟩ hz (hy.2.trans heq.symm)
  linarith

/-- The reflected branch is strictly below the positive branch at a common positive argument. -/
theorem scalarH_reflection_lt {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc 0 1) : scalarH q (-x) < scalarH q x := by
  have hm : StrictMonoOn (fun r => scalarH q r - scalarH q (-r)) (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuous_scalarH hq1).sub ((continuous_scalarH hq1).comp continuous_neg)).continuousOn
    intro r hr
    rw [interior_Icc] at hr
    have hd : HasDerivAt (fun r => scalarH q r - scalarH q (-r))
        ((1 - q) * (2 - q) * r * ((1 - r) ^ (-q) - (1 + r) ^ (-q))) r := by
      convert (hasDerivAt_scalarH q r (by linarith [hr.1])).sub
        ((hasDerivAt_scalarH q (-r) (by linarith [hr.2])).comp r (hasDerivAt_neg r)) using 1
      · rfl
      · simp only [← sub_eq_add_neg]
        ring
    change 0 < deriv (fun r => scalarH q r - scalarH q (-r)) r
    rw [hd.deriv]
    have hh : (1 + r) ^ (-q) < (1 - r) ^ (-q) :=
      Real.rpow_lt_rpow_of_neg (by linarith [hr.2]) (by linarith [hr.1]) (by linarith)
    exact mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) hr.1) (sub_pos.mpr hh)
  have H := hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hx.1.le, hx.2⟩ hx.1
  simp only [neg_zero, scalarH_zero, sub_self] at H
  linarith

/-- The unique reflected solution lies strictly between zero and the original argument. -/
theorem scalarThresholdY_lt_of_eq {q x y : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc 0 1) (hy : y ∈ Ioo (0 : ℝ) 1) (heq : scalarH q (-y) = scalarH q x) : y < x := by
  by_contra h
  have hxy := le_of_not_gt h
  have H := (scalarH_strictMonoOn_negative hq0 hq1).monotoneOn
    (show -y ∈ Icc (-1 : ℝ) 0 by constructor <;> linarith [hy.1, hy.2])
    (show -x ∈ Icc (-1 : ℝ) 0 by constructor <;> linarith [hx.1, hx.2])
    (neg_le_neg hxy)
  rw [heq] at H
  exact (not_lt_of_ge H) (scalarH_reflection_lt hq0 hq1 hx)

/-- The unique solution of `H(-y)=H(x)` on the stated order and argument domain.
Outside the domain this total definition takes the value zero. -/
def scalarThresholdY (q x : ℝ) : ℝ :=
  if h : 0 < q ∧ q < 1 ∧ x ∈ Ioc (0 : ℝ) 1 then
    Classical.choose (existsUnique_scalarThresholdY h.1 h.2.1 h.2.2).exists
  else 0

/-- The selected root has all its defining properties as proved conclusions. -/
theorem scalarThresholdY_spec {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc 0 1) :
    scalarThresholdY q x ∈ Ioo (0 : ℝ) 1 ∧
      scalarH q (-(scalarThresholdY q x)) = scalarH q x := by
  unfold scalarThresholdY
  rw [dite_eq_left ⟨hq0, hq1, hx⟩]
  exact Classical.choose_spec (existsUnique_scalarThresholdY hq0 hq1 hx).exists

theorem scalarThresholdY_lt {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc 0 1) : scalarThresholdY q x < x := by
  have h := scalarThresholdY_spec hq0 hq1 hx
  exact scalarThresholdY_lt_of_eq hq0 hq1 hx h.1 h.2

/-- The root itself increases strictly with the original positive argument. -/
theorem scalarThresholdY_strictMonoOn {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    StrictMonoOn (scalarThresholdY q) (Ioc (0 : ℝ) 1) := by
  intro x hx z hz hxz
  have hx' := scalarThresholdY_spec hq0 hq1 hx
  have hz' := scalarThresholdY_spec hq0 hq1 hz
  have hH := scalarH_strictAntiOn_positive hq0 hq1 ⟨hx.1.le, hx.2⟩ ⟨hz.1.le, hz.2⟩ hxz
  by_contra hn
  have hzx := le_of_not_gt hn
  have hneg := (scalarH_strictMonoOn_negative hq0 hq1).monotoneOn
    (show -(scalarThresholdY q x) ∈ Icc (-1 : ℝ) 0 by constructor <;> linarith [hx'.1.1, hx'.1.2])
    (show -(scalarThresholdY q z) ∈ Icc (-1 : ℝ) 0 by constructor <;> linarith [hz'.1.1, hz'.1.2])
    (neg_le_neg hzx)
  rw [hx'.2, hz'.2] at hneg
  exact (not_lt_of_ge hneg) hH

/-- The reciprocal gap in the scalar-threshold proof. -/
def scalarThresholdGap (q x : ℝ) : ℝ := 1 / scalarThresholdY q x - 1 / x

/-- The intended threshold as the fractional transform of its actual unique root.
Monotonicity and the sharp gap bounds are separate analytic obligations. -/
def scalarKappa (q x : ℝ) : ℝ := scalarThresholdGap q x / (2 - scalarThresholdGap q x)

theorem scalarThresholdGap_pos {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc 0 1) : 0 < scalarThresholdGap q x := by
  have hy := (scalarThresholdY_spec hq0 hq1 hx).1.1
  have hlt := scalarThresholdY_lt hq0 hq1 hx
  exact sub_pos.mpr ((one_div_lt_one_div hx.1 hy).mpr hlt)

end RenyiMonotonicity

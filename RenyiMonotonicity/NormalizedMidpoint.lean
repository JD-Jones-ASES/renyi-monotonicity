module
public import RenyiMonotonicity.MidpointFunctional

@[expose] public section

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace RenyiMonotonicity

/-- The normalized order kernel, continuously filled at order one. Its value at
a zero mass is harmless because the actual adjacent difference then vanishes. -/
def entropyOrderKernel (q s : ℝ) : ℝ :=
  -Real.log s * dslope Real.exp 0 ((q - 1) * Real.log s)

def normalizedMidpointFunctional {n : ℕ} (q : ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ k : Fin (n + 2), edgeDifference p k * entropyOrderKernel q (edgeSum p k)

theorem continuous_dslope_exp : Continuous (dslope Real.exp (0 : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_dslope_same.mpr Real.differentiable_exp.differentiableAt
  · exact (continuousAt_dslope_of_ne hx).mpr Real.continuous_exp.continuousAt

@[simp] theorem entropyOrderKernel_one (s : ℝ) : entropyOrderKernel 1 s = -Real.log s := by
  simp [entropyOrderKernel, Real.deriv_exp]

@[simp] theorem entropyOrderKernel_at_one (q : ℝ) : entropyOrderKernel q 1 = 0 := by
  simp [entropyOrderKernel]

theorem entropyOrderKernel_eq {q s : ℝ} (hs : 0 < s) (hq : q ≠ 1) :
    entropyOrderKernel q s = (s ^ (q - 1) - 1) / (1 - q) := by
  by_cases hs1 : s = 1
  · simp [hs1]
  · have hl : Real.log s ≠ 0 := by
      intro he
      have hh := Real.exp_log hs
      rw [he, Real.exp_zero] at hh
      exact hs1 hh.symm
    have hz : (q - 1) * Real.log s ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hq) hl
    rw [entropyOrderKernel, dslope_of_ne _ hz, slope_def_field]
    simp only [sub_zero, Real.exp_zero]
    rw [show (q - 1) * Real.log s = Real.log s * (q - 1) by ring,
      ← Real.rpow_def_of_pos hs]
    field_simp
    ring

/-- Joint continuity includes the order-one slice on every positive mass. -/
theorem continuousAt_entropyOrderKernel {q s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun z : ℝ × ℝ => entropyOrderKernel z.1 z.2) (q, s) := by
  have hl : ContinuousAt (fun z : ℝ × ℝ => Real.log z.2) (q, s) :=
    continuousAt_snd.log hs.ne'
  exact hl.neg.mul (continuous_dslope_exp.continuousAt.comp
    ((continuousAt_fst.sub continuousAt_const).mul hl))

theorem hasDerivAt_entropyOrderKernel {q s : ℝ} (hs : 0 < s) :
    HasDerivAt (entropyOrderKernel q) (-(s ^ (q - 2))) s := by
  by_cases hq : q = 1
  · subst q
    have he : entropyOrderKernel 1 = fun t => -Real.log t := funext entropyOrderKernel_one
    rw [he]
    convert (Real.hasDerivAt_log hs.ne').neg using 1
    norm_num [Real.rpow_neg_one]
  · have he : entropyOrderKernel q =ᶠ[𝓝 s] (fun t => (t ^ (q - 1) - 1) / (1 - q)) := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      exact entropyOrderKernel_eq ht hq
    have hh := ((Real.hasDerivAt_rpow_const (x := s) (p := q - 1) (Or.inl hs.ne')).sub_const 1).div_const (1 - q)
    have hder : HasDerivAt (fun t : ℝ => (t ^ (q - 1) - 1) / (1 - q))
        (-(s ^ (q - 2))) s := by
      convert hh using 1
      rw [show q - 1 - 1 = q - 2 by ring]
      field_simp
      ring
    exact hder.congr_of_eventuallyEq he

/-- Uniform logarithmic lower bound for the normalized kernel. -/
theorem entropyOrderKernel_log_le {q s : ℝ} (hq : q ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) :
    -Real.log s ≤ entropyOrderKernel q s := by
  have hd (t : ℝ) (ht : t ∈ Icc s 1) :
      HasDerivAt (fun t => entropyOrderKernel q t + Real.log t)
        (-(t ^ (q - 2)) + t⁻¹) t :=
    (hasDerivAt_entropyOrderKernel (hs.trans_le ht.1)).add
      (Real.hasDerivAt_log (hs.trans_le ht.1).ne')
  have hm : AntitoneOn (fun t => entropyOrderKernel q t + Real.log t) (Icc s 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht' := interior_subset ht
    have hp := Real.rpow_le_rpow_of_exponent_ge (hs.trans_le ht'.1) ht'.2
      (show q - 2 ≤ (-1 : ℝ) by linarith)
    rw [Real.rpow_neg_one] at hp
    linarith
  have hh := hm (left_mem_Icc.mpr hs1) (right_mem_Icc.mpr hs1) hs1
  simp only [entropyOrderKernel_at_one, Real.log_one, add_zero] at hh
  linarith

/-- Uniform reciprocal upper bound; together with the logarithmic bound this
covers the full order interval from zero through one. -/
theorem entropyOrderKernel_le_inv {q s : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hs1 : s ≤ 1) :
    entropyOrderKernel q s ≤ s⁻¹ - 1 := by
  have hd (t : ℝ) (ht : t ∈ Icc s 1) :
      HasDerivAt (fun t => entropyOrderKernel q t - t⁻¹)
        (-(t ^ (q - 2)) + (t ^ 2)⁻¹) t := by
    convert (hasDerivAt_entropyOrderKernel (hs.trans_le ht.1)).sub
      (hasDerivAt_inv (hs.trans_le ht.1).ne') using 1
    ring
  have hm : MonotoneOn (fun t => entropyOrderKernel q t - t⁻¹) (Icc s 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht' := interior_subset ht
    have hp := Real.rpow_le_rpow_of_exponent_ge (hs.trans_le ht'.1) ht'.2
      (show (-2 : ℝ) ≤ q - 2 by linarith)
    norm_num [Real.rpow_neg] at hp
    linarith
  have hh := hm (left_mem_Icc.mpr hs1) (right_mem_Icc.mpr hs1) hs1
  simp only [entropyOrderKernel_at_one, inv_one, zero_sub] at hh
  linarith

theorem entropyOrderKernel_nonneg {q s : ℝ} (hq : q ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ entropyOrderKernel q s :=
  (neg_nonneg.mpr (Real.log_nonpos hs.le hs1)).trans (entropyOrderKernel_log_le hq hs hs1)

@[simp] theorem normalizedMidpointFunctional_one {n : ℕ} (p : Fin n → ℝ) :
    normalizedMidpointFunctional 1 p =
      -∑ k : Fin (n + 2), edgeDifference p k * Real.log (edgeSum p k) := by
  simp [normalizedMidpointFunctional, Finset.sum_neg_distrib]

theorem normalizedMidpointFunctional_eq {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : q ≠ 1) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    normalizedMidpointFunctional q p = midpointFunctional q p / (1 - q) := by
  have he (k : Fin (n + 2)) : edgeDifference p k * entropyOrderKernel q (edgeSum p k) =
      (edgeDifference p k * (edgeSum p k) ^ (q - 1) - edgeDifference p k) / (1 - q) := by
    rcases eq_or_lt_of_le (edgeSum_nonneg p hp hp1 k) with hs | hs
    · have hs0 : edgeSum p k = 0 := hs.symm
      have hd0 : edgeDifference p k = 0 := abs_eq_zero.mp
        (le_antisymm (by simpa [hs0] using abs_edgeDifference_le_edgeSum p hp hp1 k) (abs_nonneg _))
      simp [hd0]
    · rw [entropyOrderKernel_eq hs hq]
      ring
  simp_rw [normalizedMidpointFunctional, he, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [sum_edgeDifference, sub_zero]
  rfl

theorem continuousAt_normalizedMidpointFunctional {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hs : ∀ k, 0 < edgeSum p k) :
    ContinuousAt (fun z : ℝ × (Fin n → ℝ) => normalizedMidpointFunctional z.1 z.2) (q, p) := by
  unfold normalizedMidpointFunctional
  apply tendsto_finsetSum
  intro k _
  have hh : ContinuousAt (fun z : ℝ × (Fin n → ℝ) => entropyOrderKernel z.1 (edgeSum z.2 k)) (q, p) :=
    ContinuousAt.comp (x := (q, p)) (f := fun z : ℝ × (Fin n → ℝ) => (z.1, edgeSum z.2 k))
      (continuousAt_entropyOrderKernel (q := q) (hs k))
      (continuousAt_fst.prodMk ((continuous_edgeSum k).continuousAt.comp continuousAt_snd))
  exact ((continuous_edgeDifference k).continuousAt.comp continuousAt_snd).mul hh

end RenyiMonotonicity

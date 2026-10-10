module

public import RenyiMonotonicity.ScalarGap

/-! The actual scalar mass-gradient kernel and its link to the constructed threshold. -/

@[expose] public section
noncomputable section
open Set

namespace RenyiMonotonicity

/-- The one-neighbour kernel appearing in the derivative with respect to a mass. -/
def massGradientScalar (q b t : ℝ) : ℝ := (q * b + (2 - q) * t) * (b + t) ^ (q - 2)

/-- The exact three-mass gradient entry. -/
def massGradientEntry (q a b c : ℝ) : ℝ := massGradientScalar q b c - massGradientScalar q b a

/-- The normalized left secant coordinate. -/
def gradientCoordinate (a b : ℝ) : ℝ := (b - a) / (b + a)

/-- The curvature ratio used to compare a triple to its scalar threshold. -/
def tripleKappa (a b c : ℝ) : ℝ := (b^2 - a*c) / (b * (a - 2*b + c))

/-- The exact derivative formula (G1). -/
theorem hasDerivAt_massGradientScalar (q b t : ℝ) (hbt : 0 < b + t) :
    HasDerivAt (massGradientScalar q b)
      ((2 - q) * (1 - q) * (b - t) * (b + t)^(q - 3)) t := by
  have h₁ := (((hasDerivAt_id t).const_mul (2 - q)).const_add (q * b))
  have h₂ := ((hasDerivAt_id t).const_add b).rpow_const (p := q - 2) (Or.inl hbt.ne')
  have hp : (b + t)^(q - 2) = (b + t)^(q - 3) * (b + t) := by
    rw [show q - 2 = (q - 3) + 1 by ring, Real.rpow_add hbt, Real.rpow_one]
  convert h₁.mul h₂ using 1
  · rfl
  · simp only [id_eq, mul_one, one_mul]
    rw [show q - 2 - 1 = q - 3 by ring, hp]
    ring

/-- Scalar normalization directly identifies the mass-gradient kernel with `H`. -/
theorem scalarH_gradientCoordinate (q b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    scalarH q (gradientCoordinate t b) = (2 * b)^(1 - q) * massGradientScalar q b t := by
  have hs : 0 < b + t := by linarith
  have h₁ : 1 - (1 - q) * ((b - t) / (b + t)) = (q * b + (2 - q) * t) / (b + t) := by
    apply (eq_div_iff hs.ne').mpr
    rw [sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hs.ne']
    ring
  have h₂ : 1 + (b - t) / (b + t) = (2 * b) / (b + t) := by
    apply (eq_div_iff hs.ne').mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hs.ne']
    ring
  have hp : (b + t)^(q - 2) = ((b + t)^(1 - q))⁻¹ / (b + t) := by
    rw [show q - 2 = -(1 - q) - 1 by ring, Real.rpow_sub hs, Real.rpow_one,
      Real.rpow_neg hs.le]
  unfold scalarH gradientCoordinate massGradientScalar
  rw [h₁, h₂, Real.div_rpow (by linarith : 0 ≤ 2 * b) hs.le, hp]
  simp only [div_eq_mul_inv]
  ring

lemma gradientCoordinate_mem {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    gradientCoordinate a b ∈ Ioc (0 : ℝ) 1 := by
  have hs : 0 < b + a := by linarith
  refine ⟨div_pos (sub_pos.mpr hab) hs, ?_⟩
  exact (div_le_one hs).mpr (by linarith)

lemma continuousOn_massGradientScalar {q b : ℝ} (hb : 0 < b) :
    ContinuousOn (massGradientScalar q b) (Ici (0 : ℝ)) := by
  intro t ht
  change 0 ≤ t at ht
  exact (hasDerivAt_massGradientScalar q b t (by linarith [ht])).continuousAt.continuousWithinAt

/-- The scalar kernel strictly increases up to the middle mass. -/
theorem massGradientScalar_strictMonoOn {q b : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hb : 0 < b) :
    StrictMonoOn (massGradientScalar q b) (Icc (0 : ℝ) b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) ((continuousOn_massGradientScalar hb).mono (by intro t ht; exact ht.1))
  intro t ht
  rw [interior_Icc] at ht
  have hs : 0 < b + t := by linarith [ht.1]
  rw [(hasDerivAt_massGradientScalar q b t hs).deriv]
  exact mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (sub_pos.mpr ht.2)) (Real.rpow_pos_of_pos hs _)

/-- The scalar kernel strictly decreases above the middle mass. -/
theorem massGradientScalar_strictAntiOn {q b : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hb : 0 < b) :
    StrictAntiOn (massGradientScalar q b) (Ici b) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) ((continuousOn_massGradientScalar hb).mono (by intro t ht; change 0 ≤ t; have hbt : b ≤ t := ht; linarith))
  intro t ht
  rw [interior_Ici] at ht
  change b < t at ht
  have hs : 0 < b + t := by linarith [ht]
  rw [(hasDerivAt_massGradientScalar q b t hs).deriv]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos (by linarith) (by linarith)) (sub_neg.mpr ht))
    (Real.rpow_pos_of_pos hs _)

/-- The critical right neighbour is built from the proved reflected scalar root. -/
def criticalMass (q a b : ℝ) : ℝ :=
  b * (1 + scalarThresholdY q (gradientCoordinate a b)) /
    (1 - scalarThresholdY q (gradientCoordinate a b))

lemma criticalMass_gt {q a b : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 ≤ a) (hab : a < b) :
    b < criticalMass q a b := by
  have hx := gradientCoordinate_mem ha hab
  have hy := (scalarThresholdY_spec hq0 hq1 hx).1
  have hp : 0 < 1 - scalarThresholdY q (gradientCoordinate a b) := by linarith [hy.2]
  unfold criticalMass
  apply (lt_div_iff₀ hp).mpr
  have hb : 0 < b := by linarith
  nlinarith [mul_pos hb hy.1]

lemma gradientCoordinate_criticalMass {q a b : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) :
    gradientCoordinate (criticalMass q a b) b = -scalarThresholdY q (gradientCoordinate a b) := by
  have hx := gradientCoordinate_mem ha hab
  have hy := (scalarThresholdY_spec hq0 hq1 hx).1
  have hp : 1 - scalarThresholdY q (gradientCoordinate a b) ≠ 0 := by linarith [hy.2]
  have hb : 0 < b := by linarith
  have hc := criticalMass_gt hq0 hq1 ha hab
  have hs : b + criticalMass q a b ≠ 0 := by linarith
  change (b - criticalMass q a b) / (b + criticalMass q a b) = -scalarThresholdY q (gradientCoordinate a b)
  apply (div_eq_iff hs).mpr
  unfold criticalMass
  field_simp [hp]
  ring

/-- Existence of the critical right neighbour, with exact kernel equality. -/
theorem massGradientScalar_criticalMass {q a b : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) :
    massGradientScalar q b (criticalMass q a b) = massGradientScalar q b a := by
  have hb : 0 < b := by linarith
  have hc0 : 0 ≤ criticalMass q a b := le_of_lt (hb.trans (criticalMass_gt hq0 hq1 ha hab))
  have hx := gradientCoordinate_mem ha hab
  have hy := (scalarThresholdY_spec hq0 hq1 hx).2
  have hn : (2 * b)^(1 - q) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  apply mul_left_cancel₀ hn
  rw [← scalarH_gradientCoordinate q b _ hb hc0, ← scalarH_gradientCoordinate q b a hb ha,
    gradientCoordinate_criticalMass hq0 hq1 ha hab]
  exact hy

/-- Uniqueness is on the full descending half-line, without an upper cutoff. -/
theorem criticalMass_unique {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c)
    (heq : massGradientScalar q b c = massGradientScalar q b a) : c = criticalMass q a b := by
  have hb : 0 < b := by linarith
  apply (massGradientScalar_strictAntiOn hq0 hq1 hb).injOn hbc.le
    (criticalMass_gt hq0 hq1 ha hab).le
  exact heq.trans (massGradientScalar_criticalMass hq0 hq1 ha hab).symm

/-- Inverting the normalized left coordinate. -/
lemma mass_of_gradientCoordinate {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a = b * (1 - gradientCoordinate a b) / (1 + gradientCoordinate a b) := by
  have hx := gradientCoordinate_mem ha hab
  have hden : 1 + gradientCoordinate a b ≠ 0 := by linarith [hx.1]
  apply (eq_div_iff hden).mpr
  unfold gradientCoordinate
  have hs : b + a ≠ 0 := by linarith
  field_simp [hs]
  ring

/-- The two curvature numerators at the constructed critical triple are positive,
and their quotient is exactly the scalar threshold (G6). -/
theorem criticalMass_curvature {q a b : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) :
    0 < a - 2*b + criticalMass q a b ∧
      0 < b^2 - a * criticalMass q a b ∧
      tripleKappa a b (criticalMass q a b) = scalarKappa q (gradientCoordinate a b) := by
  let x := gradientCoordinate a b
  let y := scalarThresholdY q x
  let d := scalarThresholdGap q x
  have hx : x ∈ Ioc (0 : ℝ) 1 := gradientCoordinate_mem ha hab
  have hy : y ∈ Ioo (0 : ℝ) 1 := (scalarThresholdY_spec hq0 hq1 hx).1
  have hyx : y < x := scalarThresholdY_lt hq0 hq1 hx
  have hd := scalarThresholdGap_bounds hq0 hq1 hx
  have hb : 0 < b := by linarith
  have hden : 0 < (1 + x) * (1 - y) := mul_pos (by linarith [hx.1]) (by linarith [hy.2])
  have hxy : x - y = d * x * y := by
    change x - y = (1 / y - 1 / x) * x * y
    field_simp [hx.1.ne', hy.1.ne']
  have hJnum : 2*x*y-x+y = (2-d)*x*y := by linarith
  have hJpos : 0 < 2*x*y-x+y := by
    rw [hJnum]
    exact mul_pos (mul_pos (by linarith [hd.2]) hx.1) hy.1
  have ha' : a = b * (1 - x) / (1 + x) := mass_of_gradientCoordinate ha hab
  have hc' : criticalMass q a b = b * (1 + y) / (1 - y) := rfl
  have hJ : a - 2*b + criticalMass q a b = 2*b*(2*x*y-x+y) / ((1+x)*(1-y)) := by
    rw [hc', ha']
    field_simp [(by linarith [hx.1] : 1+x ≠ 0), (by linarith [hy.2] : 1-y ≠ 0)]
    ring
  have hT : b^2 - a * criticalMass q a b = 2*b^2*(x-y) / ((1+x)*(1-y)) := by
    rw [hc', ha']
    field_simp [(by linarith [hx.1] : 1+x ≠ 0), (by linarith [hy.2] : 1-y ≠ 0)]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hJ]
    exact div_pos (mul_pos (mul_pos (by norm_num) hb) hJpos) hden
  · rw [hT]
    exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hb)) (sub_pos.mpr hyx)) hden
  · change (b^2 - a * criticalMass q a b) / (b * (a - 2*b + criticalMass q a b)) = d / (2-d)
    rw [hJ, hT, hxy, hJnum]
    have hden' : 1 + x - x*y - y ≠ 0 := by nlinarith [hden]
    field_simp [hb.ne', hden.ne', hden', hx.1.ne', hy.1.ne', (by linarith [hd.2] : 2-d ≠ 0)]
    ring_nf
    field_simp [hden']
    ring

/-- Exact decrease of the curvature ratio as the right neighbour increases. -/
theorem tripleKappa_sub (a b c d : ℝ) (hb : b ≠ 0)
    (hc : a - 2*b + c ≠ 0) (hd : a - 2*b + d ≠ 0) :
    tripleKappa a b c - tripleKappa a b d =
      (b-a)^2 * (d-c) / (b * (a-2*b+c) * (a-2*b+d)) := by
  unfold tripleKappa
  rw [div_sub_div _ _ (mul_ne_zero hb hc) (mul_ne_zero hb hd)]
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hb hc) (mul_ne_zero hb hd))
    (mul_ne_zero (mul_ne_zero hb hc) hd)).mpr
  ring

/-- The ratio decreases strictly on the positive-curvature branch. -/
theorem tripleKappa_strictAntiOn {a b : ℝ} (hab : a < b) (hb : 0 < b) :
    StrictAntiOn (tripleKappa a b) (Ioi (2*b-a)) := by
  intro c hc d hd hcd
  have hJc : 0 < a - 2*b + c := by have hc' : 2*b-a < c := hc; linarith
  have hJd : 0 < a - 2*b + d := by have hd' : 2*b-a < d := hd; linarith
  have H := tripleKappa_sub a b c d hb.ne' hJc.ne' hJd.ne'
  have hp : 0 < (b-a)^2 * (d-c) / (b * (a-2*b+c) * (a-2*b+d)) :=
    div_pos (mul_pos (sq_pos_of_pos (sub_pos.mpr hab)) (sub_pos.mpr hcd))
      (mul_pos (mul_pos hb hJc) hJd)
  linarith

/-- Positive gradient sign is exactly the scalar-threshold comparison (G7). -/
theorem massGradientEntry_pos_iff {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hJ : 0 < a - 2*b + c) :
    0 < massGradientEntry q a b c ↔ scalarKappa q (gradientCoordinate a b) < tripleKappa a b c := by
  have hb : 0 < b := by linarith
  have hcstar := criticalMass_gt hq0 hq1 ha hab
  have hcurv := criticalMass_curvature hq0 hq1 ha hab
  have hF := (massGradientScalar_strictAntiOn hq0 hq1 hb).lt_iff_gt hcstar.le hbc.le
  have hK := (tripleKappa_strictAntiOn hab hb).lt_iff_gt
    (show criticalMass q a b ∈ Ioi (2*b-a) by change 2*b-a < criticalMass q a b; linarith [hcurv.1])
    (show c ∈ Ioi (2*b-a) by change 2*b-a < c; linarith)
  rw [massGradientScalar_criticalMass hq0 hq1 ha hab] at hF
  rw [hcurv.2.2] at hK
  exact (sub_pos).trans (hF.trans hK.symm)

/-- Zero gradient sign is exactly equality to the scalar threshold. -/
theorem massGradientEntry_eq_zero_iff {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hJ : 0 < a - 2*b + c) :
    massGradientEntry q a b c = 0 ↔ tripleKappa a b c = scalarKappa q (gradientCoordinate a b) := by
  have hb : 0 < b := by linarith
  have hcstar := criticalMass_gt hq0 hq1 ha hab
  have hcurv := criticalMass_curvature hq0 hq1 ha hab
  have hF := (massGradientScalar_strictAntiOn hq0 hq1 hb).eq_iff_eq hbc.le hcstar.le
  have hK := (tripleKappa_strictAntiOn hab hb).eq_iff_eq
    (show c ∈ Ioi (2*b-a) by change 2*b-a < c; linarith)
    (show criticalMass q a b ∈ Ioi (2*b-a) by change 2*b-a < criticalMass q a b; linarith [hcurv.1])
  rw [massGradientScalar_criticalMass hq0 hq1 ha hab] at hF
  rw [hcurv.2.2] at hK
  exact sub_eq_zero.trans (hF.trans hK.symm)

/-- Negative gradient sign is exactly the opposite scalar-threshold comparison. -/
theorem massGradientEntry_neg_iff {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hJ : 0 < a - 2*b + c) :
    massGradientEntry q a b c < 0 ↔ tripleKappa a b c < scalarKappa q (gradientCoordinate a b) := by
  have hb : 0 < b := by linarith
  have hcstar := criticalMass_gt hq0 hq1 ha hab
  have hcurv := criticalMass_curvature hq0 hq1 ha hab
  have hF := (massGradientScalar_strictAntiOn hq0 hq1 hb).lt_iff_gt hbc.le hcstar.le
  have hK := (tripleKappa_strictAntiOn hab hb).lt_iff_gt
    (show c ∈ Ioi (2*b-a) by change 2*b-a < c; linarith)
    (show criticalMass q a b ∈ Ioi (2*b-a) by change 2*b-a < criticalMass q a b; linarith [hcurv.1])
  rw [massGradientScalar_criticalMass hq0 hq1 ha hab] at hF
  rw [hcurv.2.2] at hK
  exact sub_neg.trans (hF.trans hK.symm)

/-- Increasing triples with nonpositive second difference have strictly positive gradient.
The proved critical curvature excludes a zero here without integrating a singular kernel. -/
theorem massGradientEntry_pos_of_curvature_nonpos {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hJ : a - 2*b + c ≤ 0) :
    0 < massGradientEntry q a b c := by
  have hb : 0 < b := by linarith
  have hcstar := criticalMass_gt hq0 hq1 ha hab
  have hcurv := (criticalMass_curvature hq0 hq1 ha hab).1
  have hlt : c < criticalMass q a b := by linarith
  have H := massGradientScalar_strictAntiOn hq0 hq1 hb hbc hcstar.le hlt
  rw [massGradientScalar_criticalMass hq0 hq1 ha hab] at H
  exact sub_pos.mpr H

end RenyiMonotonicity

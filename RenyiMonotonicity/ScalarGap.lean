module

public import RenyiMonotonicity.ScalarThreshold
public import RenyiMonotonicity.ScalarRatio
public import RenyiMonotonicity.ThresholdCrossing

/-! Finite-interval scalar gap comparison. -/

@[expose] public section
noncomputable section
open Set

namespace RenyiMonotonicity

/-- The difference whose zero characterizes a fixed reciprocal gap. -/
def scalarGapDifference (q c x : ℝ) : ℝ := scalarH q (-(x / (1 + c * x))) - scalarH q x

@[simp] lemma scalarGapDifference_zero (q c : ℝ) : scalarGapDifference q c 0 = 0 := by
  simp [scalarGapDifference]

lemma gap_bases {c x : ℝ} (hc : 0 < c) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < 1 + x ∧ 0 < 1 + c * x ∧ 0 < 1 + (c - 1) * x := by
  have hcx : 0 ≤ c * x := mul_nonneg hc.le hx.1
  refine ⟨by linarith [hx.1], by linarith, ?_⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  · have := mul_pos hc (lt_of_le_of_ne hx.1 (Ne.symm hx0))
    nlinarith [hx.2]

lemma continuousOn_scalarGapDifference {q c : ℝ} (hq : q < 1) (hc : 0 < c) :
    ContinuousOn (scalarGapDifference q c) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.sub _ (continuous_scalarH hq).continuousOn
  apply Continuous.comp_continuousOn (continuous_scalarH hq)
  apply ContinuousOn.neg
  exact continuousOn_id.div (by fun_prop) (fun x hx => (gap_bases hc hx).2.1.ne')

/-- The derivative ratio of the finite gap difference. -/
theorem hasDerivAt_scalarGapDifference (q c x : ℝ)
    (h1 : 0 < 1 + x) (h2 : 0 < 1 + c * x) (h3 : 0 < 1 + (c - 1) * x) :
    HasDerivAt (scalarGapDifference q c)
      ((1 - q) * (2 - q) * x * (1 + x)^(-q) * (1 - scalarRatio q c x)) x := by
  have hylt : x / (1 + c * x) < 1 := (div_lt_one h2).mpr (by nlinarith)
  have hdY : HasDerivAt (fun t : ℝ => t / (1 + c * t)) (1 / (1 + c * x)^2) x := by
    convert (hasDerivAt_id x).div (((hasDerivAt_id x).const_mul c).const_add 1) h2.ne' using 1
    · rfl
    · simp only [id_eq, one_mul, mul_one]
      congr 1
      ring
  have hr : 1 - x / (1 + c * x) = (1 + (c - 1) * x) / (1 + c * x) := by
    apply (eq_div_iff h2.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ h2.ne']
    ring
  have hpow : (1 - x / (1 + c * x)) ^ (-q) =
      (1 + (c - 1) * x)^(-q) * (1 + c * x)^q := by
    rw [hr, Real.div_rpow h3.le h2.le, Real.rpow_neg h2.le q]
    simp
  have hpow2 : (1 + c * x) ^ (q - 3) = (1 + c * x)^q / (1 + c * x)^3 := by
    rw [Real.rpow_sub h2]
    norm_num
  have hcancel : (1 + x)^(-q) * (1 + x)^q = 1 := by
    rw [← Real.rpow_add h1]
    simp
  convert ((hasDerivAt_scalarH q (-(x / (1 + c * x))) (by linarith)).comp x hdY.neg).sub
    (hasDerivAt_scalarH q x (by linarith)) using 1
  · rfl
  · dsimp [scalarRatio]
    simp only [← sub_eq_add_neg]
    rw [hpow, hpow2]
    have hterm : (1 + x)^(-q) *
        ((1 + x)^q * ((1 + c * x)^q / (1 + c * x)^3) * (1 + (c - 1) * x)^(-q)) =
        ((1 + c * x)^q / (1 + c * x)^3) * (1 + (c - 1) * x)^(-q) := by
      calc
        _ = ((1 + x)^(-q) * (1 + x)^q) *
          (((1 + c * x)^q / (1 + c * x)^3) * (1 + (c - 1) * x)^(-q)) := by ring
        _ = _ := by rw [hcancel]; ring
    calc
      _ = ((1 - q) * (2 - q) * x) * ((1 + x)^(-q) -
          ((1 + x)^(-q) * ((1 + x)^q * ((1 + c * x)^q / (1 + c * x)^3) * (1 + (c - 1) * x)^(-q)))) := by ring
      _ = _ := by
        rw [hterm]
        field_simp [h2.ne']
        ring

lemma continuousOn_scalarRatio {c q : ℝ} (hc : 0 < c) :
    ContinuousOn (scalarRatio q c) (Icc (0 : ℝ) 1) := by
  intro x hx
  have hb := gap_bases hc hx
  exact (hasDerivAt_scalarRatio q c x hb.1 hb.2.1 hb.2.2).continuousAt.continuousWithinAt

lemma scalarRatio_deriv_pos {q c x : ℝ} (hc : 0 < c) (hx : x ∈ Icc (0 : ℝ) 1)
    (hQ : 0 < scalarRatioNumerator q c x) : 0 < deriv (scalarRatio q c) x := by
  have hb := gap_bases hc hx
  rw [(hasDerivAt_scalarRatio q c x hb.1 hb.2.1 hb.2.2).deriv]
  exact div_pos (mul_pos (scalarRatio_pos q c x hb.1 hb.2.1 hb.2.2) hQ)
    (mul_pos (mul_pos hb.1 hb.2.1) hb.2.2)

lemma scalarRatio_deriv_neg {q c x : ℝ} (hc : 0 < c) (hx : x ∈ Icc (0 : ℝ) 1)
    (hQ : scalarRatioNumerator q c x < 0) : deriv (scalarRatio q c) x < 0 := by
  have hb := gap_bases hc hx
  rw [(hasDerivAt_scalarRatio q c x hb.1 hb.2.1 hb.2.2).deriv]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (scalarRatio_pos q c x hb.1 hb.2.1 hb.2.2) hQ)
    (mul_pos (mul_pos hb.1 hb.2.1) hb.2.2)

lemma scalarGapDifference_deriv_pos {q c x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hc : 0 < c) (hx : x ∈ Ioc (0 : ℝ) 1) (hR : scalarRatio q c x < 1) :
    0 < deriv (scalarGapDifference q c) x := by
  have hb := gap_bases hc ⟨hx.1.le, hx.2⟩
  rw [(hasDerivAt_scalarGapDifference q c x hb.1 hb.2.1 hb.2.2).deriv]
  exact mul_pos (mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) hx.1)
    (Real.rpow_pos_of_pos hb.1 _)) (sub_pos.mpr hR)

lemma scalarGapDifference_deriv_neg {q c x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hc : 0 < c) (hx : x ∈ Ioc (0 : ℝ) 1) (hR : 1 < scalarRatio q c x) :
    deriv (scalarGapDifference q c) x < 0 := by
  have hb := gap_bases hc ⟨hx.1.le, hx.2⟩
  rw [(hasDerivAt_scalarGapDifference q c x hb.1 hb.2.1 hb.2.2).deriv]
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) hx.1)
    (Real.rpow_pos_of_pos hb.1 _)) (sub_neg.mpr hR)

/-- The upper comparison shift has ratio below one, on the entire finite interval. -/
lemma scalarRatio_one_lt_one {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : x ∈ Ioc (0 : ℝ) 1) :
    scalarRatio q 1 x < 1 := by
  have hm : StrictAntiOn (scalarRatio q 1) (Icc (0 : ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_scalarRatio (by norm_num))
    intro t ht
    rw [interior_Icc] at ht
    apply scalarRatio_deriv_neg (by norm_num) ⟨ht.1.le, ht.2.le⟩
    unfold scalarRatioNumerator
    have hn : 2 * q - 3 < 0 := by linarith
    have hp : 0 < 1 + t := by linarith [ht.1]
    simpa using mul_neg_of_neg_of_pos hn hp
  simpa using hm ⟨le_rfl, by norm_num⟩ ⟨hx.1.le, hx.2⟩ hx.1

lemma scalarGapDifference_one_pos {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : x ∈ Ioc (0 : ℝ) 1) :
    0 < scalarGapDifference q 1 x := by
  have hm : StrictMonoOn (scalarGapDifference q 1) (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_scalarGapDifference hq1 (by norm_num))
    intro t ht
    rw [interior_Icc] at ht
    exact scalarGapDifference_deriv_pos hq0 hq1 (by norm_num) ⟨ht.1, ht.2.le⟩
      (scalarRatio_one_lt_one hq0 hq1 ⟨ht.1, ht.2.le⟩)
  simpa using hm ⟨le_rfl, by norm_num⟩ ⟨hx.1.le, hx.2⟩ hx.1

/-- The lower comparison shift has ratio above one. -/
lemma scalarRatio_lower_gt_one {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : x ∈ Ioc (0 : ℝ) 1) :
    1 < scalarRatio q (2 * q / 3) x := by
  have hc : 0 < 2 * q / 3 := by positivity
  have hm : StrictMonoOn (scalarRatio q (2 * q / 3)) (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_scalarRatio hc)
    intro t ht
    rw [interior_Icc] at ht
    apply scalarRatio_deriv_pos hc ⟨ht.1.le, ht.2.le⟩
    unfold scalarRatioNumerator
    have he : 2 * q - 3 * (2 * q / 3) = 0 := by ring
    rw [he, zero_mul, zero_add]
    exact mul_pos (mul_pos (mul_pos (by linarith) hc) (by linarith)) (sq_pos_of_pos ht.1)
  simpa using hm ⟨le_rfl, by norm_num⟩ ⟨hx.1.le, hx.2⟩ hx.1

lemma scalarGapDifference_lower_neg {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hx : x ∈ Ioc (0 : ℝ) 1) :
    scalarGapDifference q (2 * q / 3) x < 0 := by
  have hc : 0 < 2 * q / 3 := by positivity
  have hm : StrictAntiOn (scalarGapDifference q (2 * q / 3)) (Icc (0 : ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_scalarGapDifference hq1 hc)
    intro t ht
    rw [interior_Icc] at ht
    exact scalarGapDifference_deriv_neg hq0 hq1 hc ⟨ht.1, ht.2.le⟩
      (scalarRatio_lower_gt_one hq0 hq1 ⟨ht.1, ht.2.le⟩)
  simpa using hm ⟨le_rfl, by norm_num⟩ ⟨hx.1.le, hx.2⟩ hx.1

/-- At a positive zero of the gap difference, its ratio exceeds one and
its later values are strictly negative. -/
theorem scalarGapDifference_crossing {q c u : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hc0 : 2 * q / 3 < c) (hc1 : c < 1) (hu : u ∈ Ioc (0 : ℝ) 1)
    (hDu : scalarGapDifference q c u = 0) :
    1 < scalarRatio q c u ∧
      ∀ t ∈ Ioc (0 : ℝ) 1, u < t → scalarGapDifference q c t < 0 := by
  have hc : 0 < c := by linarith
  have ha : 2 * q - 3 * c < 0 := by linarith
  have hb : 0 ≤ (3 - q) * c * (1 - c) := mul_nonneg (mul_nonneg (by linarith) hc.le) (by linarith)
  have hcross : ∀ {u t : ℝ}, u ∈ Ioc (0 : ℝ) 1 → t ∈ Ioc (0 : ℝ) 1 → u < t →
      0 ≤ scalarRatio q c u - 1 → 0 < scalarRatio q c t - 1 := by
    apply thresholdLog_crossing ha hb ((continuousOn_scalarRatio hc).sub continuousOn_const)
      (by simp)
    · intro t ht hQ
      have h := scalarRatio_deriv_neg hc ⟨ht.1.le, ht.2.le⟩ hQ
      change deriv (fun x => scalarRatio q c x - 1) t < 0
      rwa [deriv_sub_const]
    · intro t ht hQ
      have h := scalarRatio_deriv_pos hc ⟨ht.1.le, ht.2.le⟩ hQ
      change 0 < deriv (fun x => scalarRatio q c x - 1) t
      rwa [deriv_sub_const]
  have H := thresholdPrimitive_crossing (continuousOn_scalarGapDifference hq1 hc)
    (scalarGapDifference_zero q c) hcross
    (fun t ht hR => scalarGapDifference_deriv_pos hq0 hq1 hc ⟨ht.1, ht.2.le⟩ (by linarith))
    (fun t ht hR => scalarGapDifference_deriv_neg hq0 hq1 hc ⟨ht.1, ht.2.le⟩ (by linarith)) hu hDu
  exact ⟨by linarith [H.1], H.2⟩

lemma gap_argument_mem {c x : ℝ} (hc : 0 < c) (hx : x ∈ Ioc (0 : ℝ) 1) :
    -(x / (1 + c * x)) ∈ Icc (-1 : ℝ) 0 := by
  have hb := gap_bases hc ⟨hx.1.le, hx.2⟩
  have hy0 : 0 < x / (1 + c * x) := div_pos hx.1 hb.2.1
  have hy1 : x / (1 + c * x) < 1 := (div_lt_one hb.2.1).mpr (by nlinarith [hb.2.2])
  constructor <;> linarith

/-- At a fixed positive argument, increasing the reciprocal shift strictly increases the difference. -/
theorem scalarGapDifference_strictMonoOn_gap {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc (0 : ℝ) 1) : StrictMonoOn (fun c => scalarGapDifference q c x) (Ioi (0 : ℝ)) := by
  intro c hc d hd hcd
  have hb := gap_bases hc ⟨hx.1.le, hx.2⟩
  have hden : 1 + c * x < 1 + d * x := by nlinarith [mul_pos (sub_pos.mpr hcd) hx.1]
  have harg : -(x / (1 + c * x)) < -(x / (1 + d * x)) :=
    neg_lt_neg (div_lt_div_of_pos_left hx.1 hb.2.1 hden)
  have H := scalarH_strictMonoOn_negative hq0 hq1 (gap_argument_mem hc hx) (gap_argument_mem hd hx) harg
  unfold scalarGapDifference
  linarith

/-- The actual reciprocal gap solves its defining finite difference equation. -/
theorem scalarThresholdGap_root {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc (0 : ℝ) 1) : scalarGapDifference q (scalarThresholdGap q x) x = 0 := by
  have hy := scalarThresholdY_spec hq0 hq1 hx
  have hden : 1 + scalarThresholdGap q x * x = x / scalarThresholdY q x := by
    unfold scalarThresholdGap
    field_simp [hx.1.ne', hy.1.1.ne']
    ring
  have hid : x / (1 + scalarThresholdGap q x * x) = scalarThresholdY q x := by
    rw [hden]
    field_simp [hx.1.ne', hy.1.1.ne']
  unfold scalarGapDifference
  rw [hid, hy.2]
  ring

/-- Both sharp comparison bounds on the actual reciprocal gap, with strict endpoints. -/
theorem scalarThresholdGap_bounds {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc (0 : ℝ) 1) : 2 * q / 3 < scalarThresholdGap q x ∧ scalarThresholdGap q x < 1 := by
  have hg0 := scalarThresholdGap_pos hq0 hq1 hx
  have heq := scalarThresholdGap_root hq0 hq1 hx
  have hm := (scalarGapDifference_strictMonoOn_gap hq0 hq1 hx).monotoneOn
  constructor
  · by_contra hn
    have H := hm hg0 (by change 0 < 2 * q / 3; positivity : 2 * q / 3 ∈ Ioi (0 : ℝ)) (le_of_not_gt hn)
    dsimp only at H
    rw [heq] at H
    exact (not_lt_of_ge H) (scalarGapDifference_lower_neg hq0 hq1 hx)
  · by_contra hn
    have H := hm (by norm_num : (1 : ℝ) ∈ Ioi (0 : ℝ)) hg0 (le_of_not_gt hn)
    dsimp only at H
    rw [heq] at H
    exact (not_lt_of_ge H) (scalarGapDifference_one_pos hq0 hq1 hx)

/-- Strict monotonicity of the actual reciprocal gap on the complete finite domain. -/
theorem scalarThresholdGap_strictMonoOn {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    StrictMonoOn (scalarThresholdGap q) (Ioc (0 : ℝ) 1) := by
  intro x hx z hz hxz
  have hb := scalarThresholdGap_bounds hq0 hq1 hx
  have hcross := scalarGapDifference_crossing hq0 hq1 hb.1 hb.2 hx
    (scalarThresholdGap_root hq0 hq1 hx)
  have hneg := hcross.2 z hz hxz
  have hzroot := scalarThresholdGap_root hq0 hq1 hz
  by_contra hn
  have H := (scalarGapDifference_strictMonoOn_gap hq0 hq1 hz).monotoneOn
    (scalarThresholdGap_pos hq0 hq1 hz) (scalarThresholdGap_pos hq0 hq1 hx) (le_of_not_gt hn)
  rw [hzroot] at H
  linarith

/-- The actual scalar threshold is strictly increasing, including the endpoint `x=1`. -/
theorem scalarKappa_strictMonoOn {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    StrictMonoOn (scalarKappa q) (Ioc (0 : ℝ) 1) := by
  intro x hx z hz hxz
  have hb₁ := scalarThresholdGap_bounds hq0 hq1 hx
  have hb₂ := scalarThresholdGap_bounds hq0 hq1 hz
  have hg := scalarThresholdGap_strictMonoOn hq0 hq1 hx hz hxz
  unfold scalarKappa
  apply (div_lt_div_iff₀ (by linarith : 0 < 2 - scalarThresholdGap q x)
    (by linarith : 0 < 2 - scalarThresholdGap q z)).mpr
  nlinarith

/-- The sharp open bounds on the scalar mass-gradient threshold. -/
theorem scalarKappa_bounds {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x ∈ Ioc (0 : ℝ) 1) : q / (3 - q) < scalarKappa q x ∧ scalarKappa q x < 1 := by
  have hb := scalarThresholdGap_bounds hq0 hq1 hx
  have hp : 0 < 2 - scalarThresholdGap q x := by linarith
  unfold scalarKappa
  constructor
  · apply (div_lt_div_iff₀ (by linarith : 0 < 3 - q) hp).mpr
    nlinarith
  · exact (div_lt_one hp).mpr (by linarith)

end RenyiMonotonicity

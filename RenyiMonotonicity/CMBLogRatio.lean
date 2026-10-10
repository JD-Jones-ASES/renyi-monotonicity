module

public import RenyiMonotonicity.CMBFiniteComparison

/-! Elementary central-log ratios replacing the infinite Gamma expansion in the finite density argument. -/

@[expose] public section
noncomputable section
open Set

namespace RenyiMonotonicity

/-- The logarithm of the symmetric odds ratio. -/
def centralLog (x : ℝ) : ℝ := Real.log (1+x)-Real.log (1-x)

@[simp] lemma centralLog_zero : centralLog 0=0 := by simp [centralLog]

lemma hasDerivAt_centralLog (x : ℝ) (hx : x∈Ioo (-1:ℝ) 1) :
    HasDerivAt centralLog (2/(1-x^2)) x := by
  have ha : 1+x≠0 := ne_of_gt (by linarith [hx.1])
  have hb : 1-x≠0 := ne_of_gt (by linarith [hx.2])
  have H := (((hasDerivAt_id x).const_add 1).log ha).sub (((hasDerivAt_id x).const_sub 1).log hb)
  convert H using 1
  · funext t; rfl
  · simp only [id_eq]
    have hd : 1-x^2≠0 := ne_of_gt (by nlinarith [hx.1,hx.2])
    field_simp
    ring

/-- Cauchy's mean value theorem gives the decreasing-quotient rule in the form needed here. -/
theorem strictAntiOn_div_of_deriv_ratio (f g df dg : ℝ → ℝ) (b : ℝ)
    (hf0 : f 0=0) (hg0 : g 0=0)
    (hfc : ContinuousOn f (Ico 0 b)) (hgc : ContinuousOn g (Ico 0 b))
    (hf : ∀ x∈Ioo 0 b, HasDerivAt f (df x) x)
    (hg : ∀ x∈Ioo 0 b, HasDerivAt g (dg x) x)
    (hgmono : StrictMonoOn g (Ico 0 b)) (hdg : ∀ x∈Ioo 0 b, 0<dg x)
    (hratio : StrictAntiOn (fun x => df x/dg x) (Ioo 0 b)) :
    StrictAntiOn (fun x => f x/g x) (Ioo 0 b) := by
  intro x hx y hy hxy
  have h0b : 0<b := hx.1.trans hx.2
  have hgx : 0<g x := by simpa only [hg0] using hgmono ⟨le_rfl,h0b⟩ ⟨hx.1.le,hx.2⟩ hx.1
  have hgyx : g x<g y := hgmono ⟨hx.1.le,hx.2⟩ ⟨hy.1.le,hy.2⟩ hxy
  obtain ⟨u,hu,Hu⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f df hx.1
    (hfc.mono (by intro t ht; exact ⟨ht.1,ht.2.trans_lt hx.2⟩))
    (fun t ht => hf t ⟨ht.1,ht.2.trans hx.2⟩) g dg
    (hgc.mono (by intro t ht; exact ⟨ht.1,ht.2.trans_lt hx.2⟩))
    (fun t ht => hg t ⟨ht.1,ht.2.trans hx.2⟩)
  obtain ⟨v,hv,Hv⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f df hxy
    (hfc.mono (by intro t ht; exact ⟨hx.1.le.trans ht.1,ht.2.trans_lt hy.2⟩))
    (fun t ht => hf t ⟨hx.1.trans ht.1,ht.2.trans hy.2⟩) g dg
    (hgc.mono (by intro t ht; exact ⟨hx.1.le.trans ht.1,ht.2.trans_lt hy.2⟩))
    (fun t ht => hg t ⟨hx.1.trans ht.1,ht.2.trans hy.2⟩)
  have hum : u∈Ioo 0 b := ⟨hu.1,hu.2.trans hx.2⟩
  have hvm : v∈Ioo 0 b := ⟨hx.1.trans hv.1,hv.2.trans hy.2⟩
  have Hr := hratio hum hvm (hu.2.trans hv.1)
  have Hu' : df u/dg u=f x/g x := by
    apply (div_eq_div_iff (hdg u hum).ne' hgx.ne').mpr
    simpa only [hf0,hg0,sub_zero,mul_comm] using Hu
  have Hv' : df v/dg v=(f y-f x)/(g y-g x) := by
    apply (div_eq_div_iff (hdg v hvm).ne' (sub_pos.mpr hgyx).ne').mpr
    simpa only [mul_comm] using Hv
  change df v/dg v<df u/dg u at Hr
  rw [Hu',Hv'] at Hr
  have H := (div_lt_div_iff₀ (sub_pos.mpr hgyx) hgx).mp Hr
  apply (div_lt_div_iff₀ (hgx.trans hgyx) hgx).mpr
  nlinarith

lemma centralLog_strictMonoOn : StrictMonoOn centralLog (Ioo (-1:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro x hx
    exact (hasDerivAt_centralLog x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x∈Ioo (-1:ℝ) 1 := interior_subset hx
    rw [(hasDerivAt_centralLog x hx').deriv]
    exact div_pos (by norm_num) (by nlinarith [hx'.1,hx'.2])

lemma centralLog_pos {x : ℝ} (hx : x∈Ioo 0 1) : 0<centralLog x := by
  simpa only [centralLog_zero] using centralLog_strictMonoOn (by norm_num : (0:ℝ)∈Ioo (-1:ℝ) 1)
    ⟨by linarith [hx.1],hx.2⟩ hx.1

lemma centralLog_derivative_ratio_strictAnti {c : ℝ} (hc0 : 0<c) (hc1 : c<1) :
    StrictAntiOn (fun x => c*(1-x^2)/(1-c^2*x^2)) (Ioo 0 1) := by
  intro x hx y hy hxy
  have hc : 0<c^2 ∧ c^2<1 := ⟨sq_pos_of_pos hc0,by nlinarith⟩
  have hx2 : 0<x^2 ∧ x^2<1 := ⟨sq_pos_of_pos hx.1,by nlinarith [hx.1,hx.2]⟩
  have hy2 : 0<y^2 ∧ y^2<1 := ⟨sq_pos_of_pos hy.1,by nlinarith [hy.1,hy.2]⟩
  have hdx : 0<1-c^2*x^2 := by nlinarith
  have hdy : 0<1-c^2*y^2 := by nlinarith
  apply (div_lt_div_iff₀ hdy hdx).mpr
  have H := mul_pos (mul_pos hc0 (by linarith : 0<1-c^2)) (by nlinarith [hx.1,hy.1] : 0<y^2-x^2)
  nlinarith

/-- The actual symmetric log quotient is strictly decreasing on the positive unit interval. -/
theorem centralLog_scaled_ratio_strictAnti {c : ℝ} (hc0 : 0<c) (hc1 : c<1) :
    StrictAntiOn (fun x => centralLog (c*x)/centralLog x) (Ioo 0 1) := by
  let df := fun x => 2*c/(1-(c*x)^2)
  let dg : ℝ → ℝ := fun x => 2/(1-x^2)
  have hcx (x : ℝ) (hx : x∈Ico 0 1) : c*x∈Ioo (-1:ℝ) 1 := by
    have hnon : 0≤c*x := mul_nonneg hc0.le hx.1
    constructor
    · linarith
    · nlinarith [hx.1,hx.2]
  have hf (x : ℝ) (hx : x∈Ico 0 1) : HasDerivAt (fun x => centralLog (c*x)) (df x) x := by
    have H := (hasDerivAt_centralLog (c*x) (hcx x hx)).comp x ((hasDerivAt_id x).const_mul c)
    convert H using 1
    · funext t; rfl
    · dsimp [df]; ring
  have hg (x : ℝ) (hx : x∈Ico 0 1) := hasDerivAt_centralLog x ⟨by linarith [hx.1],hx.2⟩
  apply strictAntiOn_div_of_deriv_ratio (fun x => centralLog (c*x)) centralLog df dg 1
    (by simp) centralLog_zero (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => hf x ⟨hx.1.le,hx.2⟩) (fun x hx => hg x ⟨hx.1.le,hx.2⟩)
    (centralLog_strictMonoOn.mono (by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩))
  · intro x hx
    exact div_pos (by norm_num) (by nlinarith [hx.1,hx.2])
  · have he (x : ℝ) (hx : x∈Ioo 0 1) : df x/dg x=c*(1-x^2)/(1-c^2*x^2) := by
      dsimp [df,dg]
      field_simp
    intro x hx y hy hxy
    change df y/dg y < df x/dg x
    rw [he x hx,he y hy]
    exact centralLog_derivative_ratio_strictAnti hc0 hc1 hx hy hxy

end RenyiMonotonicity

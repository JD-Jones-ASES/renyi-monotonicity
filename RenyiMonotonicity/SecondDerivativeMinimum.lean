module

public import RenyiMonotonicity.ContactLocalMin
public import Mathlib.Analysis.Calculus.LHopital

/-! A genuine second derivative at an actual scalar minimum is nonnegative. -/

@[expose] public section
noncomputable section
open Filter Topology

namespace RenyiMonotonicity

theorem secondDerivative_nonneg_of_localMin {f d : ℝ → ℝ} {c : ℝ}
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (d t) t)
    (hdd : HasDerivAt d c 0) (hmin : IsLocalMin f 0) : 0 ≤ c := by
  have hf := hd.self_of_nhds
  have hz : d 0 = 0 := hmin.hasDerivAt_eq_zero hf
  have hs : Tendsto (fun t => d t / t) (𝓝[≠] (0:ℝ)) (𝓝 c) := by
    convert hdd.tendsto_slope using 1
    ext t
    simp [slope_def_field, hz]
  have hl : Tendsto (fun t => (f t-f 0)/t^2) (𝓝[≠] (0:ℝ)) (𝓝 (c/2)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
      (f' := d) (g' := fun t => 2*t)
    · filter_upwards [hd.filter_mono nhdsWithin_le_nhds] with t ht
      exact ht.sub_const _
    · exact Filter.Eventually.of_forall (fun t => by
        simpa using (hasDerivAt_id t).fun_pow 2)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_ne_zero (by norm_num) ht
    · have hcont : ContinuousAt (fun t => f t-f 0) 0 := hf.continuousAt.sub continuousAt_const
      simpa only [sub_self] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · have hcont : ContinuousAt (fun t : ℝ => t^2) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · convert hs.div_const 2 using 1; simp only [div_div, mul_comm]
  have hn : 0 ≤ c/2 := by
    apply ge_of_tendsto hl
    filter_upwards [hmin.filter_mono nhdsWithin_le_nhds] with t ht
    exact div_nonneg (sub_nonneg.mpr ht) (sq_nonneg t)
  linarith

end RenyiMonotonicity

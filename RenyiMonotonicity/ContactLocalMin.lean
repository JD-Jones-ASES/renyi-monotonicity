module

public import RenyiMonotonicity.ContactPolynomial

/-! Leading-term signs at an actual scalar local minimum. -/

@[expose] public section
noncomputable section
open Filter Topology

namespace RenyiMonotonicity

/-- A right local minimum has nonnegative ordinary derivative. -/
theorem hasDerivAt_nonneg_of_right_min {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hmin : ∀ᶠ t in 𝓝[>] (0:ℝ), f 0 ≤ f t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [hmin, self_mem_nhdsWithin] with t ht hpos
  simpa only [zero_add, smul_eq_mul] using mul_nonneg (inv_nonneg.mpr (le_of_lt hpos)) (sub_nonneg.mpr ht)

/-- A finite cubic leading coefficient at a two-sided local minimum must vanish. -/
theorem cubic_limit_eq_zero_of_localMin {f : ℝ → ℝ} {c : ℝ}
    (hmin : IsLocalMin f 0)
    (hlim : Tendsto (fun t => (f t-f 0)/t^3) (𝓝[≠] (0:ℝ)) (𝓝 c)) : c=0 := by
  have hpos : 0 ≤ c := by
    apply ge_of_tendsto (hlim.mono_left (nhdsGT_le_nhdsNE 0))
    filter_upwards [hmin.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hpos
    exact div_nonneg (sub_nonneg.mpr ht) (pow_nonneg (le_of_lt hpos) 3)
  have hneg : c ≤ 0 := by
    apply le_of_tendsto (hlim.mono_left (nhdsLT_le_nhdsNE 0))
    filter_upwards [hmin.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hneg
    exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht) (by nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (le_of_lt hneg)])
  exact le_antisymm hneg hpos

end RenyiMonotonicity

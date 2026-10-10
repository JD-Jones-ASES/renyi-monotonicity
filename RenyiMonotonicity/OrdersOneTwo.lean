module
public import RenyiMonotonicity.CoordinateTransfer
public import RenyiMonotonicity.HarmonicBernoulli

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace RenyiMonotonicity

/-- Harmonic lowering and coordinate concavity give the closed-cube entropy
comparison at every order strictly above one and at most two. -/
theorem tsallis_monotone_of_one_lt {n : ℕ} (q : ℝ) (hq : 1 < q) (hq2 : q ≤ 2)
    (p r : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    tsallis q (bernoulliSum p) ≤ tsallis q (bernoulliSum r) := by
  apply tsallis_monotone_of_midpoint q (by linarith) (ne_of_gt hq) ?_ p r hp hpr hr
  intro m v hv hvHalf
  exact div_nonneg_of_nonpos (midpointFunctional_nonpos_of_one_le v
    (fun i => (hv i).le) hvHalf q hq.le hq2) (by linarith)

/-- The Shannon endpoint follows from the actual finite-law order limit. -/
theorem shannon_monotone {n : ℕ} (p r : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    shannon (bernoulliSum p) ≤ shannon (bernoulliSum r) := by
  have hp1 : ∀ i, p i ≤ 1 := fun i => by linarith [hpr i, hr i]
  have hr0 : ∀ i, 0 ≤ r i := fun i => (hp i).trans (hpr i)
  have hr1 : ∀ i, r i ≤ 1 := fun i => by linarith [hr i]
  have htp := (tendsto_tsallis_order_one (bernoulliSum p)
    (bernoulliSum_nonneg p hp hp1) (sum_bernoulliSum p)).mono_left
    (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have htr := (tendsto_tsallis_order_one (bernoulliSum r)
    (bernoulliSum_nonneg r hr0 hr1) (sum_bernoulliSum r)).mono_left
    (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto htp htr
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds] with q hq hq2
  exact tsallis_monotone_of_one_lt q hq hq2.le p r hp hpr hr

theorem tsallis_monotone_of_one_le {n : ℕ} (q : ℝ) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (p r : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    tsallis q (bernoulliSum p) ≤ tsallis q (bernoulliSum r) := by
  rcases eq_or_lt_of_le hq with hq | hq
  · subst q
    simpa only [tsallis_one] using shannon_monotone p r hp hpr hr
  · exact tsallis_monotone_of_one_lt q hq hq2 p r hp hpr hr

theorem renyi_monotone_of_one_le {n : ℕ} (q : ℝ) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (p r : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    renyi q (bernoulliSum p) ≤ renyi q (bernoulliSum r) := by
  apply (renyi_le_iff_tsallis_le_probability q _ _ (by linarith)
    (bernoulliSum_nonneg p hp (fun i => by linarith [hpr i, hr i]))
    (bernoulliSum_nonneg r (fun i => (hp i).trans (hpr i)) (fun i => by linarith [hr i]))
    (sum_bernoulliSum p) (sum_bernoulliSum r)).mpr
  exact tsallis_monotone_of_one_le q hq hq2 p r hp hpr hr

end RenyiMonotonicity

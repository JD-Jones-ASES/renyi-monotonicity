module
public import RenyiMonotonicity.OneBiasedLaw
public import RenyiMonotonicity.SmallBackgrounds

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RenyiMonotonicity

/-- The actual finite-law midpoint tends to zero as the distinguished coin
vanishes. Support-loss continuity supplies the endpoint without summing the
binomial series at its radius of convergence. -/
theorem tendsto_midpointFunctional_oneBiased_boundary (m : ℕ) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun δ : ℝ => midpointFunctional q (oneBiasedParameters m ((1-δ)/2)))
      (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have hmap : Continuous (fun δ : ℝ => (q,oneBiasedParameters m ((1-δ)/2))) := by
    apply continuous_const.prodMk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun _ => continuous_const) i
    change Continuous (fun δ : ℝ => (1-δ)/2)
    fun_prop
  have hcont : ContinuousOn (fun δ : ℝ => midpointFunctional q
      (oneBiasedParameters m ((1-δ)/2))) (Icc (0:ℝ) 1) := by
    apply continuousOn_midpointFunctional_halfCube.comp hmap.continuousOn
    intro δ hδ
    refine ⟨hq,?_⟩
    intro i
    refine Fin.cases ?_ (fun _ => by norm_num [oneBiasedParameters]) i
    change (1-δ)/2 ∈ Icc (0:ℝ) (1/2)
    constructor <;> linarith [hδ.1,hδ.2]
  have hfilter : Tendsto (fun δ : ℝ => δ) (𝓝[<] (1:ℝ)) (𝓝[Icc (0:ℝ) 1] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with δ hδ hδ0
    exact ⟨hδ0.le,hδ.le⟩
  have hh := (hcont 1 ⟨by norm_num,le_rfl⟩).tendsto.comp hfilter
  simpa only [sub_self,zero_div,oneBiasedParameters,midpointFunctional_cons_zero,
    midpointFunctional_all_half,Function.comp_def] using hh

end RenyiMonotonicity

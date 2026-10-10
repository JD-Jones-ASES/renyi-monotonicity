module
public import RenyiMonotonicity.FairNeighborhood
public import RenyiMonotonicity.BoxMonotonicity

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RenyiMonotonicity

theorem normalizedMidpoint_strictAnti_updates_box (n : ℕ) (q c : ℝ) (hc : 0 < c)
    (hgrad : ∀ p ∈ Icc (fun _ : Fin (n+1) => c) (fun _ => (1/2:ℝ)),
      ∀ i, normalizedCoinDerivative q p i < 0) :
    ∀ p ∈ Icc (fun _ : Fin (n+1) => c) (fun _ => (1/2:ℝ)), ∀ i,
      StrictAntiOn (fun t => normalizedMidpointFunctional q (Function.update p i t)) (Icc c (1/2)) := by
  classical
  intro p hp i
  have hmem (t : ℝ) (ht : t ∈ Icc c (1/2)) :
      Function.update p i t ∈ Icc (fun _ : Fin (n+1) => c) (fun _ => (1/2:ℝ)) := by
    constructor <;> intro j <;> by_cases hj : j = i
    · subst j; simpa using ht.1
    · simpa [Function.update, hj] using hp.1 j
    · subst j; simpa using ht.2
    · simpa [Function.update, hj] using hp.2 j
  have hd (t : ℝ) (ht : t ∈ Icc c (1/2)) :
      HasDerivAt (fun u => normalizedMidpointFunctional q (Function.update p i u))
        (normalizedCoinDerivative q (Function.update p i t) i) t := by
    have hw := hmem t ht
    have hs := edgeSum_pos (Function.update p i t)
      (fun j => hc.trans_le (hw.1 j)) (fun j => lt_of_le_of_lt (hw.2 j) (by norm_num))
    simpa only [Function.update_self, Function.update_idem] using
      hasDerivAt_normalizedMidpointFunctional_update q (Function.update p i t) i hs
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc c (1/2))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  exact hgrad _ (hmem t (interior_subset ht)) i

/-- Uniform strict positivity near the all-fair corner on a compact positive
order band. The fair vector itself has value zero. -/
theorem exists_fair_corner_box_pos (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ c ∈ Ioo (0:ℝ) (1/2), ∀ q ∈ Icc a 1,
      ∀ p ∈ Icc (fun _ : Fin (n+1) => c) (fun _ => (1/2:ℝ)),
        p ≠ (fun _ => (1/2:ℝ)) → 0 < normalizedMidpointFunctional q p := by
  have he := eventually_normalizedCoinDerivative_all_half_neg n a ha
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  let d := min (ε/2) (1/4:ℝ)
  have hd : 0 < d := lt_min (by linarith) (by norm_num)
  have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd4 : d ≤ 1/4 := min_le_right _ _
  let c := 1/2 - d
  have hc : c ∈ Ioo (0:ℝ) (1/2) := by dsimp [c]; constructor <;> linarith
  have hgrad (p : Fin (n+1) → ℝ)
      (hp : p ∈ Icc (fun _ => c) (fun _ => (1/2:ℝ))) :
      ∀ q ∈ Icc a 1, ∀ i, normalizedCoinDerivative q p i < 0 := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hp.2 i))]
    have := hp.1 i
    dsimp [c] at this
    linarith
  refine ⟨c, hc, ?_⟩
  intro q hq p hp hne
  have hh := upper_corner_lt_of_strict_updates (normalizedMidpointFunctional q)
    (fun _ : Fin (n+1) => c) (fun _ => (1/2:ℝ))
    (normalizedMidpoint_strictAnti_updates_box n q c hc.1 (fun r hr i => hgrad r hr q hq i)) p hp hne
  rwa [normalizedMidpointFunctional_all_half] at hh

end RenyiMonotonicity

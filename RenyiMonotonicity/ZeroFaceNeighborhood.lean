module
public import RenyiMonotonicity.SupportDecomposition

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RenyiMonotonicity

/-- Inductive nonnegativity on smaller backgrounds extends uniformly to a
neighborhood of every zero face. The added block is controlled by the explicit
small-coin estimate, and is allowed to remain identically zero. -/
theorem eventually_normalizedMidpoint_nonneg_zero_face {n : ℕ}
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc (0:ℝ) (1/2)) (hz : ∃ i, p i = 0)
    (a : ℝ) (ha : 0 ≤ a)
    (hIH : ∀ m < n, ∀ q ∈ Icc a 1, ∀ r : Fin m → ℝ,
      (∀ i, r i ∈ Icc (0:ℝ) (1/2)) → 0 ≤ normalizedMidpointFunctional q r) :
    ∀ᶠ r in 𝓝 p, (∀ i, r i ∈ Icc (0:ℝ) (1/2)) →
      ∀ q ∈ Icc a 1, 0 ≤ normalizedMidpointFunctional q r := by
  obtain ⟨m, k, hdim, hmn, hk, e, hpos, hzero⟩ :=
    exists_positive_core_zero_tail p (fun i => (hp i).1) hz
  let C : (Fin n → ℝ) → (Fin m → ℝ) := fun r i => r (e (Fin.castAdd k i))
  let T : (Fin n → ℝ) → (Fin k → ℝ) := fun r i => r (e (Fin.natAdd m i))
  have hC : Continuous C := continuous_reindexed_core e
  have hT : Continuous T := continuous_reindexed_tail e
  have hg (i : Fin (m+1)) : 0 < bernoulliMass (C p) (i.val : ℤ) :=
    bernoulliMass_pos (C p) hpos (fun j => lt_of_le_of_lt (hp _).2 (by norm_num))
      _ (by omega) (by omega)
  obtain ⟨j, hj⟩ := Finite.exists_min (fun i : Fin (m+1) => bernoulliMass (C p) (i.val : ℤ))
  let c := bernoulliMass (C p) (j.val : ℤ) / 2
  have hc : 0 < c := half_pos (hg j)
  have hcm (i : Fin (m+1)) : c < bernoulliMass (C p) (i.val : ℤ) :=
    (half_lt_self (hg j)).trans_le (hj i)
  have hmass : ∀ᶠ r in 𝓝 p, ∀ i : Fin (m+1), c ≤ bernoulliMass (C r) (i.val : ℤ) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (((continuous_bernoulliMass_coordinate (i.val : ℤ)).comp hC).continuousAt.eventually
      (eventually_gt_nhds (hcm i))).mono (fun _ h => h.le)
  let δ := min (1/4:ℝ) (Real.exp (-128 / c^2))
  have hδ : 0 < δ := lt_min (by norm_num) (Real.exp_pos _)
  have hsum : Continuous (fun r : Fin n → ℝ => ∑ i, T r i) := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).comp hT
  have hzsum : (∑ i, T p i) = 0 := by simp [T, hzero]
  have hsmall : ∀ᶠ r in 𝓝 p, (∑ i, T r i) < δ :=
    hsum.continuousAt.eventually (eventually_lt_nhds (by simpa only [hzsum] using hδ))
  filter_upwards [hmass, hsmall] with r hrmass hrsmall
  intro hr q hq
  have hcore := hIH m hmn q hq (C r) (fun i => hr _)
  have htail : ∀ i, 0 ≤ T r i := fun i => (hr _).1
  have hsum0 : 0 ≤ ∑ i, T r i := Finset.sum_nonneg (fun i _ => htail i)
  rw [← normalizedMidpointFunctional_comp_finiteEquiv q r e, reindexed_append]
  change 0 ≤ normalizedMidpointFunctional q (Fin.append (C r) (T r))
  rcases hsum0.eq_or_lt with hs | hs
  · have hzT : ∀ i, T r i = 0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => htail i)).mp hs.symm
      exact fun i => hh i (Finset.mem_univ i)
    rwa [normalizedMidpointFunctional_append_zero q (C r) (T r) hzT]
  · exact hcore.trans (normalizedMidpointFunctional_append_gt (C r) (T r) q c
      (ha.trans hq.1) hq.2 hc (fun i => (hr _).1)
      (fun i => (hr _).2.trans (by norm_num)) htail (fun i => (hr _).2) hs
      (hrsmall.le.trans (min_le_left _ _)) (hrsmall.le.trans (min_le_right _ _)) hrmass).le

end RenyiMonotonicity

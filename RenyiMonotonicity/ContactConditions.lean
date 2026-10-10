module

public import RenyiMonotonicity.ContactLocalMin

/-! Ordinary coordinate conditions derived from an actual half-cube minimum. -/

@[expose] public section
noncomputable section
open Filter Topology

namespace RenyiMonotonicity

/-- Interior stationarity follows from actual global minimality on the closed half cube. -/
theorem midpoint_deriv_zero_of_min {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) (1/2)) (i : Fin n) (hi0 : 0 < p i) (hiHalf : p i < 1/2)
    (hmin : ∀ r : Fin n → ℝ, (∀ j, r j ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r) :
    deriv (fun t => midpointFunctional q (Function.update p i t)) (p i)=0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards [eventually_gt_nhds hi0,eventually_lt_nhds hiHalf] with t ht0 hthalf
  simp only [Function.update_eq_self]
  apply hmin
  intro j
  by_cases hj : j=i
  · subst j; simp only [Function.update_self]; exact ⟨ht0.le,hthalf.le⟩
  · simpa only [Function.update_of_ne hj] using hp j

/-- At a fair boundary coordinate, the actual ordinary derivative is nonpositive. -/
theorem midpoint_deriv_nonpos_of_min_fair {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1/2) (i : Fin (n+1)) (hi : p i=1/2)
    (hmin : ∀ r : Fin (n+1) → ℝ, (∀ j, r j ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r) :
    deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) ≤ 0 := by
  let F := fun t => midpointFunctional q (Function.update p i t)
  have hd := hasDerivAt_midpointFunctional_update_gradient q p hp
    (fun j => lt_of_le_of_lt (hpHalf j) (by norm_num)) i
  have hd' : HasDerivAt (fun s => F (p i-s)) (-deriv F (p i)) 0 := by
    have hr : HasDerivAt (fun s : ℝ => p i-s) (-1) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_sub (p i)
    have hd0 : HasDerivAt F (deriv F (p i)) ((fun s : ℝ => p i-s) 0) := by
      simpa only [F,sub_zero,hd.deriv] using hd
    simpa only [mul_neg_one,Function.comp_def] using hd0.comp (0:ℝ) hr
  have hright : ∀ᶠ s in 𝓝[>] (0:ℝ), F (p i-0) ≤ F (p i-s) := by
    filter_upwards [(eventually_lt_nhds (hp i)).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs hs0
    simp only [sub_zero,F,Function.update_eq_self]
    apply hmin
    intro j
    by_cases hj : j=i
    · subst j; simp only [Function.update_self]; exact ⟨by linarith,by have : 0<s := hs0; linarith⟩
    · simpa only [Function.update_of_ne hj,Set.mem_Icc] using And.intro (hp j).le (hpHalf j)
  exact neg_nonneg.mp (hasDerivAt_nonneg_of_right_min hd' hright)

end RenyiMonotonicity

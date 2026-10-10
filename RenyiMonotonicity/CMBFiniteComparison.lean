module

public import RenyiMonotonicity.CMBDefinitions

/-! Finite matched-mean comparison for a signed law with one negative interval. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

/-- Negative entries have interval sublevels in the underlying real coordinate. -/
def IntervalNegativeBlock {ι : Type*} (y δ : ι → ℝ) : Prop :=
  ∀ i j k, y i≤y j → y j≤y k → δ i<0 → δ k<0 → δ j≤0

/-- Equal mass and mean, together with a single negative interval, force nonnegative signed second moment. -/
theorem secondMoment_nonneg_of_intervalNegativeBlock {ι : Type*} [Fintype ι]
    (y δ : ι → ℝ) (hblock : IntervalNegativeBlock y δ)
    (hmass : ∑ i, δ i=0) (hmean : ∑ i, δ i*y i=0) :
    0≤∑ i, δ i*(y i)^2 := by
  classical
  let S : Finset ι := Finset.univ.filter (fun i => δ i<0)
  by_cases hs : S.Nonempty
  · let Y := S.image y
    have hyne : Y.Nonempty := hs.image y
    let u := Y.min' hyne
    let v := Y.max' hyne
    obtain ⟨a,ha,hau⟩ := Finset.mem_image.mp (Finset.min'_mem Y hyne)
    obtain ⟨b,hb,hbv⟩ := Finset.mem_image.mp (Finset.max'_mem Y hyne)
    have had : δ a<0 := (Finset.mem_filter.mp ha).2
    have hbd : δ b<0 := (Finset.mem_filter.mp hb).2
    have hbound (i : ι) (hi : δ i<0) : u≤y i ∧ y i≤v := by
      have hiY : y i∈Y := Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
      exact ⟨Finset.min'_le _ _ hiY,Finset.le_max' _ _ hiY⟩
    have hterm (i : ι) : 0≤δ i*(y i-u)*(y i-v) := by
      by_cases hi : u≤y i ∧ y i≤v
      · have hd : δ i≤0 := hblock a i b (by rw [hau]; exact hi.1) (by rw [hbv]; exact hi.2) had hbd
        exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hd (sub_nonneg.mpr hi.1))
          (sub_nonpos.mpr hi.2)
      · have hd : 0≤δ i := by by_contra h; exact hi (hbound i (lt_of_not_ge h))
        rcases lt_or_ge (y i) u with H|H
        · have huv : u≤v := by
            have H := (hbound a had).2
            change y a≤v at H
            have hau' : y a=u := hau
            rwa [hau'] at H
          have hiv : y i≤v := H.le.trans huv
          rw [mul_assoc]
          exact mul_nonneg hd (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr H.le) (sub_nonpos.mpr hiv))
        · have hv : v<y i := lt_of_not_ge (fun h => hi ⟨H,h⟩)
          exact mul_nonneg (mul_nonneg hd (sub_nonneg.mpr H)) (sub_nonneg.mpr hv.le)
    have H : 0≤∑ i, δ i*(y i-u)*(y i-v) := Finset.sum_nonneg (fun i _ => hterm i)
    have he : (∑ i, δ i*(y i-u)*(y i-v)) = ∑ i, δ i*(y i)^2 := by
      calc
        _ = (∑ i, δ i*(y i)^2) - (u+v)*(∑ i, δ i*y i) + (u*v)*(∑ i, δ i) := by
          simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hmass,hmean]; ring
    exact he ▸ H
  · apply Finset.sum_nonneg
    intro i _
    have hi : 0≤δ i := by
      by_contra hi
      exact hs ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge hi⟩⟩
    exact mul_nonneg hi (sq_nonneg _)

/-- Matched finite probability laws with interval negative density difference have ordered second moments. -/
theorem matchedMean_secondMoment_le {ι : Type*} [Fintype ι] (y P Q : ι → ℝ)
    (hmass : ∑ i, P i=∑ i, Q i) (hmean : ∑ i, P i*y i=∑ i, Q i*y i)
    (hblock : IntervalNegativeBlock y (fun i => P i-Q i)) :
    (∑ i, Q i*(y i)^2) ≤ ∑ i, P i*(y i)^2 := by
  have H := secondMoment_nonneg_of_intervalNegativeBlock y (fun i => P i-Q i) hblock
    (by rw [Finset.sum_sub_distrib,hmass,sub_self])
    (by simp only [sub_mul,Finset.sum_sub_distrib,hmean,sub_self])
  simpa only [sub_mul,Finset.sum_sub_distrib,sub_nonneg] using H

end RenyiMonotonicity

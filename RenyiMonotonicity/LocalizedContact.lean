module
public import RenyiMonotonicity.ZeroFaceNeighborhood
public import RenyiMonotonicity.FairCorner
public import RenyiMonotonicity.FirstContact

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RenyiMonotonicity

/-- A negative actual midpoint produces a positive, nonfair global zero minimum
at a strictly intermediate order. Induction is only on the number of coins;
zero faces are excluded by the explicit boundary estimate. -/
theorem exists_normalized_contact_of_negative (n : ℕ) (a : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hIH : ∀ m < n+1, ∀ q ∈ Icc a 1, ∀ r : Fin m → ℝ,
      (∀ i, r i ∈ Icc (0:ℝ) (1/2)) → 0 ≤ normalizedMidpointFunctional q r)
    (v : Fin (n+1) → ℝ) (hv : ∀ i, v i ∈ Icc (0:ℝ) (1/2))
    (hneg : normalizedMidpointFunctional a v < 0) :
    ∃ q ∈ Ioo a 1, ∃ p : Fin (n+1) → ℝ,
      (∀ i, 0 < p i ∧ p i ≤ 1/2) ∧ (∃ i, p i < 1/2) ∧
      normalizedMidpointFunctional q p = 0 ∧
      (∀ r : Fin (n+1) → ℝ, (∀ i, r i ∈ Icc (0:ℝ) (1/2)) →
        0 ≤ normalizedMidpointFunctional q r) := by
  classical
  let Q : Set (Fin (n+1) → ℝ) := Icc (fun _ => 0) (fun _ => (1/2:ℝ))
  let B : Set (Fin (n+1) → ℝ) := {p | p ∈ Q ∧ ∃ q ∈ Icc a 1, normalizedMidpointFunctional q p < 0}
  let K := closure B
  have hKQ : K ⊆ Q := closure_minimal (fun p hp => hp.1) isClosed_Icc
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset isClosed_closure hKQ
  have hpK (p : Fin (n+1) → ℝ) (hp : p ∈ K) : ∀ i, p i ∈ Icc (0:ℝ) (1/2) :=
    fun i => ⟨(hKQ hp).1 i, (hKQ hp).2 i⟩
  have hpos (p : Fin (n+1) → ℝ) (hp : p ∈ K) : ∀ i, 0 < p i := by
    intro i
    by_contra hn
    have hz : p i = 0 := le_antisymm (le_of_not_gt hn) ((hpK p hp i).1)
    have he := eventually_normalizedMidpoint_nonneg_zero_face p (hpK p hp) ⟨i,hz⟩ a ha0.le hIH
    have havoid : ∀ᶠ r in 𝓝 p, r ∉ B := by
      filter_upwards [he] with r hr
      intro hb
      obtain ⟨q,hq,hneg⟩ := hb.2
      exact (not_lt_of_ge (hr (fun j => ⟨hb.1.1 j,hb.1.2 j⟩) q hq)) hneg
    exact (mem_closure_iff_frequently.mp hp) havoid
  obtain ⟨c,hc,hcorner⟩ := exists_fair_corner_box_pos n a ha0
  let fair : Fin (n+1) → ℝ := fun _ => 1/2
  have hfair : fair ∉ K := by
    have he : ∀ᶠ r in 𝓝 fair, ∀ i, c < r i := by
      apply Filter.eventually_all.mpr
      intro i
      exact (continuous_apply i).continuousAt.eventually (eventually_gt_nhds hc.2)
    have havoid : ∀ᶠ r in 𝓝 fair, r ∉ B := by
      filter_upwards [he] with r hr
      intro hb
      obtain ⟨q,hq,hneg⟩ := hb.2
      by_cases heq : r = fair
      · subst r
        rw [normalizedMidpointFunctional_all_half] at hneg
        exact lt_irrefl _ hneg
      · exact (not_lt_of_ge (hcorner q hq r ⟨fun i => (hr i).le, hb.1.2⟩ heq).le) hneg
    intro hp
    exact (mem_closure_iff_frequently.mp hp) havoid
  have hbiased (p : Fin (n+1) → ℝ) (hp : p ∈ K) : ∃ i, p i < 1/2 := by
    have hn : p ≠ fair := fun h => hfair (h ▸ hp)
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hn
    exact ⟨i, lt_of_le_of_ne (hpK p hp i).2 hi⟩
  let F : ℝ × (Fin (n+1) → ℝ) → ℝ := fun z => normalizedMidpointFunctional (1+a-z.1) z.2
  have hF : ContinuousOn F (Icc a 1 ×ˢ K) := by
    intro z hz
    have hs := edgeSum_pos z.2 (hpos z.2 hz.2)
      (fun i => lt_of_le_of_lt (hpK z.2 hz.2 i).2 (by norm_num))
    exact (ContinuousAt.comp (x := z)
      (f := fun w : ℝ × (Fin (n+1) → ℝ) => (1+a-w.1,w.2))
      (continuousAt_normalizedMidpointFunctional (1+a-z.1) z.2 hs)
      ((continuousAt_const.sub continuousAt_fst).prodMk continuousAt_snd)).continuousWithinAt
  have hstart : ∀ p ∈ K, 0 < F (a,p) := by
    intro p hp
    simpa only [F,add_sub_cancel_right] using
      normalizedMidpointFunctional_one_pos p (hpos p hp) (fun i => (hpK p hp i).2) (hbiased p hp)
  have hvB : v ∈ B := ⟨⟨fun i => (hv i).1,fun i => (hv i).2⟩, a, ⟨le_rfl,ha1.le⟩,hneg⟩
  have hend : ∃ p ∈ K, F (1,p) < 0 := by
    refine ⟨v,subset_closure hvB,?_⟩
    simpa only [F,add_sub_cancel_left] using hneg
  obtain ⟨t,ht,p,hp,hzero,hmin,_⟩ := exists_first_contact K hK F ha1 hF hstart hend
  let q := 1+a-t
  have hq : q ∈ Ioo a 1 := by dsimp [q]; constructor <;> linarith [ht.1,ht.2]
  refine ⟨q,hq,p,fun i => ⟨hpos p hp i,(hpK p hp i).2⟩,hbiased p hp,hzero,?_⟩
  intro r hr
  by_contra hn
  have hrB : r ∈ B := ⟨⟨fun i => (hr i).1,fun i => (hr i).2⟩,q,⟨hq.1.le,hq.2.le⟩,lt_of_not_ge hn⟩
  exact hn (hmin r (subset_closure hrB))

end RenyiMonotonicity

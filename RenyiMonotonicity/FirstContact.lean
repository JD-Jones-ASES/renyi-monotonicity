module
public import Mathlib

@[expose] public section

noncomputable section
open Set

namespace RenyiMonotonicity

/-- Compact first contact for a continuous order-parameter family. The analytic
application must separately supply its compact set and strict initial slice. -/
theorem exists_first_contact {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (F : ℝ × X → ℝ)
    {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b ×ˢ K))
    (ha : ∀ x ∈ K, 0 < F (a, x))
    (hb : ∃ x ∈ K, F (b, x) < 0) :
    ∃ q ∈ Ioo a b, ∃ x ∈ K, F (q, x) = 0 ∧
      (∀ y ∈ K, 0 ≤ F (q, y)) ∧
      (∀ r ∈ Ico a q, ∀ y ∈ K, 0 < F (r, y)) := by
  have earlier : ∀ t ∈ Icc a b, ∀ x ∈ K, F (t, x) < 0 →
      ∃ r ∈ Ioo a t, F (r, x) = 0 := by
    intro t ht x hx htx
    have hc : ContinuousOn (fun r => F (r, x)) (Icc a t) :=
      hF.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨⟨hr.1, hr.2.trans ht.2⟩, hx⟩)
    obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc' ht.1 hc
      (show (0 : ℝ) ∈ Icc (F (t, x)) (F (a, x)) from
        ⟨le_of_lt htx, le_of_lt (ha x hx)⟩)
    refine ⟨r, ⟨lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_⟩, hfr⟩
    · intro he
      subst r
      linarith [ha x hx]
    · intro he
      subst r
      linarith
  let S := (Icc a b ×ˢ K) ∩ F ⁻¹' Iic 0
  have hS : IsCompact S :=
    hF.lowerSemicontinuousOn.isCompact_inter_preimage_Iic (isCompact_Icc.prod hK) 0
  obtain ⟨x₀, hx₀, hbx₀⟩ := hb
  have hn : S.Nonempty := ⟨(b, x₀), ⟨⟨⟨hab.le, le_rfl⟩, hx₀⟩, hbx₀.le⟩⟩
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hn continuous_fst.continuousOn
  have hza : a < z.1 := by
    refine lt_of_le_of_ne hz.1.1.1 ?_
    intro he
    have hh := ha z.2 hz.1.2
    rw [he] at hh
    exact (not_lt_of_ge hz.2) hh
  have no_neg : ∀ y ∈ K, 0 ≤ F (z.1, y) := by
    intro y hy
    by_contra hn
    obtain ⟨r, hr, hfr⟩ := earlier z.1 hz.1.1 y hy (lt_of_not_ge hn)
    have hrs : (r, y) ∈ S :=
      ⟨⟨⟨hr.1.le, hr.2.le.trans hz.1.1.2⟩, hy⟩, hfr.le⟩
    exact (not_lt_of_ge (hmin hrs)) hr.2
  have hzero : F z = 0 := le_antisymm hz.2 (no_neg z.2 hz.1.2)
  have hzb : z.1 < b := by
    obtain ⟨r, hr, hfr⟩ := earlier b ⟨hab.le, le_rfl⟩ x₀ hx₀ hbx₀
    have hrs : (r, x₀) ∈ S := ⟨⟨⟨hr.1.le, hr.2.le⟩, hx₀⟩, hfr.le⟩
    exact (hmin hrs).trans_lt hr.2
  refine ⟨z.1, ⟨hza, hzb⟩, z.2, hz.1.2, hzero, no_neg, ?_⟩
  intro r hr y hy
  by_contra hn
  have hrs : (r, y) ∈ S :=
    ⟨⟨⟨hr.1, hr.2.le.trans hz.1.1.2⟩, hy⟩, le_of_not_gt hn⟩
  exact (not_lt_of_ge (hmin hrs)) hr.2

end RenyiMonotonicity

module
public import Mathlib

@[expose] public section
noncomputable section
open Set
namespace RenyiMonotonicity

/-- Finite coordinatewise decrease propagates across a rectangular box. -/
theorem antitoneOn_box_of_updates {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (a b : Fin n → ℝ)
    (hcoord : ∀ p ∈ Icc a b, ∀ i,
      AntitoneOn (fun t => F (Function.update p i t)) (Icc (a i) (b i))) :
    AntitoneOn F (Icc a b) := by
  classical
  intro p hp r hr hpr
  have haux (s : Finset (Fin n)) : F (s.piecewise r p) ≤ F p := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.piecewise_insert]
      have hw : s.piecewise r p ∈ Icc a b := by
        constructor <;> intro j <;> by_cases hj : j ∈ s
        · simpa [Finset.piecewise, hj] using hr.1 j
        · simpa [Finset.piecewise, hj] using hp.1 j
        · simpa [Finset.piecewise, hj] using hr.2 j
        · simpa [Finset.piecewise, hj] using hp.2 j
      have hc := hcoord _ hw i ⟨hp.1 i, hp.2 i⟩ ⟨hr.1 i, hr.2 i⟩ (hpr i)
      have hv : s.piecewise r p i = p i := Finset.piecewise_eq_of_notMem _ _ _ hi
      have hu : Function.update (s.piecewise r p) i (p i) = s.piecewise r p := by
        rw [← hv]; exact Function.update_eq_self _ _
      dsimp only at hc
      rw [hu] at hc
      exact hc.trans ih
  simpa only [Finset.piecewise_univ] using haux Finset.univ

/-- Strict coordinate decrease makes the upper corner the unique minimum. -/
theorem upper_corner_lt_of_strict_updates {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (a b : Fin n → ℝ)
    (hcoord : ∀ p ∈ Icc a b, ∀ i,
      StrictAntiOn (fun t => F (Function.update p i t)) (Icc (a i) (b i)))
    (p : Fin n → ℝ) (hp : p ∈ Icc a b) (hne : p ≠ b) : F b < F p := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ b i := Function.ne_iff.mp hne
  have hlt : p i < b i := lt_of_le_of_ne (hp.2 i) hi
  let w := Function.update b i (p i)
  have hw : w ∈ Icc a b := by
    constructor <;> intro j <;> by_cases hj : j = i
    · subst j; simpa [w] using hp.1 i
    · simpa [w, Function.update, hj] using (hp.1 j).trans (hp.2 j)
    · subst j; simpa [w] using hp.2 i
    · simp [w, hj]
  have hb : b ∈ Icc a b := ⟨hp.1.trans hp.2, le_rfl⟩
  have hwlt : F b < F w := by
    have hc := hcoord b hb i ⟨hp.1 i, hp.2 i⟩ ⟨hb.1 i, le_rfl⟩ hlt
    simpa only [Function.update_eq_self] using hc
  have hpw : p ≤ w := by
    intro j
    by_cases hj : j = i
    · subst j; simp [w]
    · simpa [w, Function.update, hj] using hp.2 j
  exact hwlt.trans_le (antitoneOn_box_of_updates F a b
    (fun p hp i => (hcoord p hp i).antitoneOn) hp hw hpw)

end RenyiMonotonicity
